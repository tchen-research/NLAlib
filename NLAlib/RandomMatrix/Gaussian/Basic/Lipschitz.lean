import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix
import NLAlib.Matrix.Norms.Core
import NLAlib.ForMathlib.MeasureTheory.IntegrableSup
import NLAlib.ForMathlib.MeasureTheory.IntegralSqrt
/-!
# Integrability of Lipschitz functionals of a Gaussian matrix

* `integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm`: a function `h` of a Gaussian
  matrix that is `L`-Lipschitz for the Frobenius norm is integrable with integrable square
  (it grows at most like `|h 0| + L ‖G‖_F`, and `‖G‖_F²` is integrable);
* `abs_specNorm_mul_of_mul_sub_le`: `G ↦ ‖S G T‖₂` is `‖S‖₂‖T‖₂`-Lipschitz for the Frobenius norm;
  together with the Lipschitz bounds of `NLAlib.Matrix.Spectral.Core` this makes `σ_min(G)`, `‖G‖₂`
  and `‖S G T‖₂` integrable;
* the generic helpers (integrability of finite maxima and minima, `𝔼 X² ≤ c²` ⟹ `𝔼 X ≤ c`)
  live in `NLAlib.ForMathlib.MeasureTheory.{IntegrableSup,IntegralSqrt}`.

Ported from the Prove2me solutions `GaussianMatrix.gordon_upper`, `GaussianMatrix.gordon_lower`,
`GaussianMatrix.gordon`, `GaussianMatrix.chevet_expectation_bound`, `GaussianMatrix.chevet`,
`GaussianMatrix.spectral_second_moment_bound` and `GaussianMatrix.spectral_second_moment`, whose
identical helper sections are deduplicated here.

Atlas: `norm-lipschitz` (integrability consequences; helpers of `gordon`, `chevet`,
`spectral-second-moment`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- `‖G‖_F² = ∑ᵢⱼ Gᵢⱼ²` is integrable under the Gaussian matrix law. Ported from Prove2me
solution `GaussianMatrix.gordon_upper` (helper `gu_integrable_frobSq`). Atlas: helper of
`gordon`. -/
theorem integrable_frobSq_gaussianMatrix (p m : ℕ) :
    Integrable (fun X : Matrix (Fin p) (Fin m) ℝ => frobSq X) (gaussianMatrix (Fin p) (Fin m)) := by
  simp only [frobSq_eq_sum_sq]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  exact ((memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving
    (measurePreserving_gaussianMatrix_entry i j)).integrable_sq

/-- `G ↦ ‖G‖_F` is continuous on `Matrix (Fin p) (Fin m) ℝ`. Ported from Prove2me solution
`GaussianMatrix.gordon_upper` (helper `gu_continuous_frobNorm`). Atlas: helper of `gordon`. -/
theorem continuous_frobNorm_of (p m : ℕ) :
    Continuous (fun X : Matrix (Fin p) (Fin m) ℝ => frobNorm X) := by
  unfold frobNorm
  simp only [frobSq_eq_sum_sq]
  fun_prop

/-- A function that is `L`-Lipschitz for the Frobenius norm is continuous. Ported from
Prove2me solution `GaussianMatrix.gordon_upper` (helper `gu_continuous_of_lip`). Atlas: helper of
`gordon`. -/
theorem continuous_of_abs_sub_le_mul_frobNorm {p m : ℕ} (h : Matrix (Fin p) (Fin m) ℝ → ℝ) (L : ℝ)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (X - Y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro X₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous (fun Y : Matrix (Fin p) (Fin m) ℝ => L * frobNorm (Y - X₀)) :=
    continuous_const.mul ((continuous_frobNorm_of p m).comp (continuous_id.sub
      continuous_const))
  have h0 : Filter.Tendsto (fun Y : Matrix (Fin p) (Fin m) ℝ => L * frobNorm (Y - X₀))
      (nhds X₀) (nhds 0) := by
    have := hc.tendsto X₀
    simpa [frobNorm, frobSq] using this
  refine squeeze_zero (fun _ => dist_nonneg) (fun Y => ?_) h0
  rw [Real.dist_eq]
  exact hLip Y X₀

/-- A function of a Gaussian matrix that is `L`-Lipschitz for the Frobenius norm,
`|h X - h Y| ≤ L ‖X - Y‖_F`, is integrable with integrable square under
`gaussianMatrix (Fin p) (Fin m)`.
Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper `gu_integrable_of_lip`;
identical copies in `gordon_lower`, `gordon`, `chevet`, `spectral_second_moment`). Atlas:
`norm-lipschitz` (integrability consequence). -/
theorem integrable_and_integrable_sq_of_abs_sub_le_mul_frobNorm {p m : ℕ}
    (h : Matrix (Fin p) (Fin m) ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (X - Y)) :
    Integrable h (gaussianMatrix (Fin p) (Fin m)) ∧
      Integrable (fun X => h X ^ 2) (gaussianMatrix (Fin p) (Fin m)) := by
  have hcont := continuous_of_abs_sub_le_mul_frobNorm h L hLip
  have hF := integrable_frobSq_gaussianMatrix p m
  have hbound : ∀ X, |h X| ≤ |h 0| + L * frobNorm X := by
    intro X
    have h1 := hLip X 0
    rw [sub_zero] at h1
    have := abs_sub_abs_le_abs_sub (h X) (h 0)
    linarith
  have hsq : ∀ X : Matrix (Fin p) (Fin m) ℝ, frobNorm X ^ 2 = frobSq X := fun X =>
    Real.sq_sqrt (frobSq_nonneg X)
  have hfn : ∀ X : Matrix (Fin p) (Fin m) ℝ, 0 ≤ frobNorm X := fun X => Real.sqrt_nonneg _
  constructor
  · refine Integrable.mono' (((integrable_const (|h 0| + L)).add (hF.const_mul L)))
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    refine (hbound X).trans ?_
    have := hsq X
    have := hfn X
    have : frobNorm X ≤ 1 + frobSq X := by
      nlinarith [sq_nonneg (frobNorm X - 1)]
    simp only [Pi.add_apply]
    nlinarith
  · refine Integrable.mono' (((integrable_const (2 * h 0 ^ 2)).add (hF.const_mul (2 * L ^ 2))))
      (hcont.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    have hb := hbound X
    have h0 : 0 ≤ |h X| := abs_nonneg _
    have : |h X| ^ 2 ≤ (|h 0| + L * frobNorm X) ^ 2 := pow_le_pow_left₀ h0 hb 2
    rw [sq_abs] at this
    simp only [Pi.add_apply]
    have hs := hsq X
    nlinarith [sq_nonneg (|h 0| - L * frobNorm X), sq_abs (h 0)]

open scoped Matrix.Norms.L2Operator in
/-- `G ↦ ‖S G T‖₂` is `‖S‖₂‖T‖₂`-Lipschitz for the Frobenius norm:
`|‖S X T‖₂ - ‖S Y T‖₂| ≤ ‖S‖₂‖T‖₂ ‖X - Y‖_F`. Ported from Prove2me solution
`GaussianMatrix.spectral_second_moment_bound` (helper `ssb_sandwich_lip`). Atlas:
`norm-lipschitz`. -/
theorem abs_specNorm_mul_of_mul_sub_le {a p m n : ℕ} (S : Matrix (Fin a) (Fin p) ℝ)
    (T : Matrix (Fin m) (Fin n) ℝ) (X Y : Matrix (Fin p) (Fin m) ℝ) :
    |specNorm (S * X * T) - specNorm (S * Y * T)|
      ≤ (specNorm S * specNorm T) * frobNorm (X - Y) := by
  unfold specNorm
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have hd : S * X * T - S * Y * T = S * (X - Y) * T := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hd]
  have h1 := Matrix.l2_opNorm_mul (S * (X - Y)) T
  have h2 := Matrix.l2_opNorm_mul S (X - Y)
  have h3 := specNorm_le_frobNorm (X - Y)
  unfold specNorm at h3
  have hS : 0 ≤ ‖S‖ := norm_nonneg _
  have hT : 0 ≤ ‖T‖ := norm_nonneg _
  have hD : 0 ≤ ‖X - Y‖ := norm_nonneg _
  calc ‖S * (X - Y) * T‖
      ≤ ‖S * (X - Y)‖ * ‖T‖ := h1
    _ ≤ (‖S‖ * ‖X - Y‖) * ‖T‖ := mul_le_mul_of_nonneg_right h2 hT
    _ ≤ (‖S‖ * frobNorm (X - Y)) * ‖T‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hS) hT
    _ = (‖S‖ * ‖T‖) * frobNorm (X - Y) := by ring

end NLAlib
