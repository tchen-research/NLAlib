import NLAlib.RandomMatrix.Gaussian.Spectral.SpectralSecondMoment
/-!
# Chevet's inequality for a Gaussian sandwich

For fixed matrices `S` (`a × p`) and `T` (`m × n`) and a `p × m` standard Gaussian matrix `Γ`
(HMT 2011, Prop. A.2; Chevet 1978, Gordon 1985):

* `integral_specNorm_mul_gaussianMatrix_mul_le`: `𝔼 ‖S Γ T‖₂ ≤ ‖S‖₂ ‖T‖_F + ‖S‖_F ‖T‖₂`;
* `integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le`: the same with integrability of
  `‖S Γ T‖₂`.

Proof: `‖S Γ T‖₂` is `‖S‖₂‖T‖₂`-Lipschitz in `Γ` for the Frobenius norm, hence integrable with
integrable square, and `𝔼 X ≤ (𝔼 X²)^{1/2}` reduces the bound to the second-moment estimate
`NLAlib.integral_specNorm_sq_mul_gaussianMatrix_mul_le` (Tropp–Webber 2023, Lemma B.1).

Ported from the Prove2me solutions `GaussianMatrix.chevet_expectation_bound` and
`GaussianMatrix.chevet`.

Atlas: `chevet`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- **Chevet's inequality** (expectation form). For `S : a × p`, `T : m × n` and a `p × m`
standard Gaussian matrix `Γ`, `𝔼 ‖S Γ T‖₂ ≤ ‖S‖₂ ‖T‖_F + ‖S‖_F ‖T‖₂`. Source: HMT 2011,
Prop. A.2; Chevet 1978; Gordon 1985. Deduced here from the second-moment bound (Tropp–Webber
2023, Lemma B.1). Atlas: `chevet`. Ported from Prove2me solution
`GaussianMatrix.chevet_expectation_bound`.
atlas: chevet -/
theorem integral_specNorm_mul_gaussianMatrix_mul_le {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ G, specNorm (S * G * T) ∂(gaussianMatrix (Fin p) (Fin m))
      ≤ specNorm S * frobNorm T + frobNorm S * specNorm T := by
  obtain ⟨hI, hI2⟩ := integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm
    (fun G : Matrix (Fin p) (Fin m) ℝ => specNorm (S * G * T))
    (specNorm S * specNorm T) (mul_nonneg (specNorm_nonneg S) (specNorm_nonneg T))
    (abs_specNorm_mul_of_mul_sub_le S T)
  refine integral_le_of_integral_sq_le (gaussianMatrix (Fin p) (Fin m)) _ hI hI2 _ ?_
    (integral_specNorm_sq_mul_gaussianMatrix_mul_le S T)
  exact add_nonneg (mul_nonneg (specNorm_nonneg S) (frobNorm_nonneg T))
    (mul_nonneg (frobNorm_nonneg S) (specNorm_nonneg T))

/-- **Chevet's inequality, with integrability.** For `S : a × p`, `T : m × n` and a `p × m`
standard Gaussian matrix `Γ`, `‖S Γ T‖₂` is integrable and
`𝔼 ‖S Γ T‖₂ ≤ ‖S‖₂ ‖T‖_F + ‖S‖_F ‖T‖₂`. Source: HMT 2011, Prop. A.2. Atlas: `chevet`. Ported
from Prove2me solution `GaussianMatrix.chevet`.
atlas: chevet -/
theorem integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le {a p m n : ℕ}
    (S : Matrix (Fin a) (Fin p) ℝ) (T : Matrix (Fin m) (Fin n) ℝ) :
    Integrable (fun G : Matrix (Fin p) (Fin m) ℝ => specNorm (S * G * T))
      (gaussianMatrix (Fin p) (Fin m)) ∧
    ∫ G, specNorm (S * G * T) ∂(gaussianMatrix (Fin p) (Fin m))
      ≤ specNorm S * frobNorm T + frobNorm S * specNorm T := by
  refine ⟨(integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm
    (fun G : Matrix (Fin p) (Fin m) ℝ => specNorm (S * G * T))
    (specNorm S * specNorm T) (mul_nonneg (specNorm_nonneg S) (specNorm_nonneg T))
    (abs_specNorm_mul_of_mul_sub_le S T)).1, integral_specNorm_mul_gaussianMatrix_mul_le S T⟩

/-- `integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le` for a random matrix `X` with
`HasLaw X (gaussianMatrix (Fin p) (Fin m)) μ`. Atlas: `chevet`. -/
theorem integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {a p m n : ℕ} {X : Ω → Matrix (Fin p) (Fin m) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin p) (Fin m)) μ) (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    Integrable (fun ω => specNorm (S * X ω * T)) μ ∧
    ∫ ω, specNorm (S * X ω * T) ∂μ ≤ specNorm S * frobNorm T + frobNorm S * specNorm T := by
  have hc : Continuous fun G : Matrix (Fin p) (Fin m) ℝ => specNorm (S * G * T) :=
    continuous_of_abs_sub_le_mul_frobNorm _ _ (abs_specNorm_mul_of_mul_sub_le S T)
  obtain ⟨h1, h2⟩ := integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le S T
  have e : ∫ ω, specNorm (S * X ω * T) ∂μ
      = ∫ G, specNorm (S * G * T) ∂(gaussianMatrix (Fin p) (Fin m)) :=
    hX.integral_comp hc.aestronglyMeasurable
  rw [← hX.map_eq] at h1
  exact ⟨h1.comp_aemeasurable hX.aemeasurable, by rw [e]; exact h2⟩

/-- `integral_specNorm_mul_gaussianMatrix_mul_le` for a random matrix `X` with
`HasLaw X (gaussianMatrix (Fin p) (Fin m)) μ`. Atlas: `chevet`. -/
theorem integral_specNorm_mul_gaussianMatrix_mul_le_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {a p m n : ℕ} {X : Ω → Matrix (Fin p) (Fin m) ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin p) (Fin m)) μ) (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) :
    ∫ ω, specNorm (S * X ω * T) ∂μ ≤ specNorm S * frobNorm T + frobNorm S * specNorm T :=
  (integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le_of_hasLaw hX S T).2

end NLAlib
