/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_specNorm_inv_gram_eq`, `Sol_GaussianMatrix_specNorm_pinvR_sq`, and the
measurability helpers of `Sol_GaussianMatrix_pinv_spectral_expectation`,
`Sol_GaussianMatrix_inverse_wishart_spectral_moment`).
-/
import NLAlib.Matrix.Spectral
import NLAlib.Matrix.Pseudoinverse
import NLAlib.Gaussian.InverseMoments.SchurComplement

/-!
# Spectral norm of the inverse Gram matrix and of the pseudoinverse

Deterministic identities that turn spectral statements about `(G Gᵀ)⁻¹` and `G† = pinvR G` into
statements about the smallest singular value `σ_min(Gᵀ) = sigmaMin Gᵀ`:

* `specNorm_inv_self_mul_transpose_eq`: `‖(A Aᵀ)⁻¹‖ = 1 / σ_min(Aᵀ)²` (both sides `0` when
  `A Aᵀ` is singular, by Mathlib's convention `M⁻¹ = 0` and `1 / 0 = 0`);
* `specNorm_pinvR_sq`: `‖A†‖² = ‖(A Aᵀ)⁻¹‖`;
* `measurable_specNorm_inv_self_mul_transpose`, `measurable_specNorm_pinvR`: measurability of
  these norms as functions of a Gaussian sample.

Atlas: `pinv-spectral-tail`, `inverse-wishart-spectral-moment` (helpers), `pseudoinverse`.
Proof source: Prove2me workspace, Gaussian Random Matrices series (`specNorm_inv_gram_eq`,
`specNorm_pinvR_sq`). The statements are generalised from `Fin r × Fin k` to arbitrary finite
index types.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

private lemma norm_toLp_eq_sqrt (v : EuclideanSpace ℝ m) :
    ‖v‖ = Real.sqrt (v.ofLp ⬝ᵥ v.ofLp) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

/-- Cauchy–Schwarz for the dot product. -/
private lemma dotProduct_le_sqrt_mul_sqrt (v w : m → ℝ) :
    v ⬝ᵥ w ≤ Real.sqrt (v ⬝ᵥ v) * Real.sqrt (w ⬝ᵥ w) := by
  rw [← Real.sqrt_mul (dotProduct_self_nonneg v)]
  refine le_trans (le_abs_self _) ?_
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  simpa [dotProduct, sq] using h

/-- `xᵀ (A Aᵀ) x = ‖Aᵀ x‖²`. -/
private lemma dotProduct_mul_transpose_mulVec (A : Matrix m n ℝ) (x : m → ℝ) :
    x ⬝ᵥ ((A * Aᵀ) *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

/-- Homogeneous form of the definition of `σ_min`: `σ_min(B)² ‖y‖² ≤ ‖B y‖²`. -/
private lemma sigmaMin_sq_mul_le (B : Matrix m n ℝ) (y : n → ℝ) :
    sigmaMin B ^ 2 * (y ⬝ᵥ y) ≤ (B *ᵥ y) ⬝ᵥ (B *ᵥ y) := by
  have h := sigmaMin_mul_sqrt_le B y
  have h0 : 0 ≤ sigmaMin B * Real.sqrt (y ⬝ᵥ y) :=
    mul_nonneg (sigmaMin_nonneg B) (Real.sqrt_nonneg _)
  have h2 := pow_le_pow_left₀ h0 h 2
  rwa [mul_pow, Real.sq_sqrt (dotProduct_self_nonneg y),
    Real.sq_sqrt (dotProduct_self_nonneg _)] at h2

variable [DecidableEq m]

/-- For an invertible Gram matrix and a unit vector `x`, `‖(AAᵀ)⁻¹‖ ≥ 1 / ‖Aᵀ x‖²`. -/
private lemma one_div_le_norm_inv_self_mul_transpose (A : Matrix m n ℝ)
    (hM : IsUnit (A * Aᵀ).det) (x : m → ℝ) (hx : x ⬝ᵥ x = 1) :
    0 < (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) ∧ 1 / ((Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x)) ≤ ‖(A * Aᵀ)⁻¹‖ := by
  set M := A * Aᵀ with hM_def
  set q := (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) with hq_def
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hq : 0 < q := by
    rcases (dotProduct_self_nonneg (Aᵀ *ᵥ x)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : Aᵀ *ᵥ x = 0 := dotProduct_self_eq_zero.1 h.symm
      have h1 : M *ᵥ x = 0 := by rw [hM_def, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
      have h2 : x = 0 := by
        have : M⁻¹ *ᵥ (M *ᵥ x) = x := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
        rw [← this, h1, Matrix.mulVec_zero]
      rw [h2, dotProduct_zero] at hx
      exact zero_ne_one hx
  refine ⟨hq, ?_⟩
  set w := M⁻¹ *ᵥ x with hw_def
  have hMw : M *ᵥ w = x := by rw [hw_def, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have hsym : Mᵀ = M := by rw [hM_def, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hwMx : w ⬝ᵥ (M *ᵥ x) = 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hMw, hx]
  have hxMx : x ⬝ᵥ (M *ᵥ x) = q := dotProduct_mul_transpose_mulVec A x
  set c := 1 / q with hc_def
  have hpsd : 0 ≤ (w - c • x) ⬝ᵥ (M *ᵥ (w - c • x)) := by
    rw [hM_def, dotProduct_mul_transpose_mulVec]; exact dotProduct_self_nonneg _
  have hexp : (w - c • x) ⬝ᵥ (M *ᵥ (w - c • x)) = w ⬝ᵥ x - 1 / q := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMw, sub_dotProduct, dotProduct_sub,
      dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul, hwMx, hxMx, hx, dotProduct_smul]
    rw [hc_def]
    field_simp
    ring
  have hwx : 1 / q ≤ w ⬝ᵥ x := by linarith
  have hCS : w ⬝ᵥ x ≤ Real.sqrt (w ⬝ᵥ w) := by
    have := dotProduct_le_sqrt_mul_sqrt w x
    rwa [hx, Real.sqrt_one, mul_one] at this
  have hop : Real.sqrt (w ⬝ᵥ w) ≤ ‖M⁻¹‖ := by
    have h := Matrix.l2_opNorm_mulVec M⁻¹ (WithLp.toLp 2 x)
    rw [norm_toLp_eq_sqrt, norm_toLp_eq_sqrt] at h
    have h' : Real.sqrt (w ⬝ᵥ w) ≤ ‖M⁻¹‖ * Real.sqrt (x ⬝ᵥ x) := h
    rwa [hx, Real.sqrt_one, mul_one] at h'
  linarith

/-- If `σ_min(Aᵀ) > 0` then `AAᵀ` is invertible and `‖(AAᵀ)⁻¹‖ ≤ 1/σ_min(Aᵀ)²`. -/
private lemma isUnit_and_norm_inv_self_mul_transpose_le (A : Matrix m n ℝ)
    (hs : 0 < sigmaMin Aᵀ) :
    IsUnit (A * Aᵀ).det ∧ ‖(A * Aᵀ)⁻¹‖ ≤ 1 / sigmaMin Aᵀ ^ 2 := by
  set M := A * Aᵀ with hM_def
  set s := sigmaMin Aᵀ with hs_def
  have hs2 : 0 < s ^ 2 := by positivity
  have hlow : ∀ y : m → ℝ, s ^ 2 * (y ⬝ᵥ y) ≤ y ⬝ᵥ (M *ᵥ y) := fun y => by
    rw [hM_def, dotProduct_mul_transpose_mulVec]; exact sigmaMin_sq_mul_le Aᵀ y
  have hunit : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have h1 := hlow v
    rw [hv, dotProduct_zero] at h1
    have h2 : v ⬝ᵥ v = 0 := le_antisymm (by nlinarith [dotProduct_self_nonneg v])
      (dotProduct_self_nonneg v)
    exact hv0 (dotProduct_self_eq_zero.1 h2)
  refine ⟨hunit, ?_⟩
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  show ‖(Matrix.toEuclideanLin M⁻¹ y)‖ ≤ 1 / s ^ 2 * ‖y‖
  rw [norm_toLp_eq_sqrt, norm_toLp_eq_sqrt]
  have hT : (Matrix.toEuclideanLin M⁻¹ y).ofLp = M⁻¹ *ᵥ y.ofLp := rfl
  rw [hT]
  set w := M⁻¹ *ᵥ y.ofLp with hw_def
  set yy := y.ofLp with hyy
  have hMw : M *ᵥ w = yy := by rw [hw_def, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have h1 := hlow w
  rw [hMw] at h1
  have h2 := dotProduct_le_sqrt_mul_sqrt w yy
  set a := Real.sqrt (w ⬝ᵥ w)
  set b := Real.sqrt (yy ⬝ᵥ yy)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have haa : a ^ 2 = w ⬝ᵥ w := Real.sq_sqrt (dotProduct_self_nonneg _)
  have h3 : s ^ 2 * a ^ 2 ≤ a * b := by rw [haa]; linarith
  have h4 : s ^ 2 * a ≤ b := by
    rcases ha.lt_or_eq with hapos | ha0
    · nlinarith
    · rw [← ha0, mul_zero]; exact hb
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs2]
  linarith

/-- **Spectral norm of the inverse Gram matrix.** For every real matrix `A`,
`‖(A Aᵀ)⁻¹‖ = 1 / σ_min(Aᵀ)²`, i.e. `λ_max((A Aᵀ)⁻¹) = 1 / λ_min(A Aᵀ)`. When `A Aᵀ` is
singular both sides are `0` (Mathlib's `M⁻¹ = 0` and `1 / 0 = 0`).

HMT 2011, proof of Prop A.3; Tropp–Webber 2023, proof of Lemma B.4. Atlas:
`pinv-spectral-tail`, `inverse-wishart-spectral-moment` (helper). Generalised from
`Fin r × Fin k` to arbitrary finite index types. Ported from Prove2me solution
`GaussianMatrix.specNorm_inv_gram_eq`. -/
theorem specNorm_inv_self_mul_transpose_eq (A : Matrix m n ℝ) :
    specNorm (A * Aᵀ)⁻¹ = 1 / sigmaMin Aᵀ ^ 2 := by
  unfold specNorm
  rcases isEmpty_or_nonempty m with hr | hr
  · have h1 : (A * Aᵀ)⁻¹ = 0 := Subsingleton.elim _ _
    rw [h1, sigmaMin_of_isEmpty, norm_zero]; simp
  · by_cases hM : IsUnit (A * Aᵀ).det
    · have hne := nonempty_unitSphere (n := m)
      set N := ‖(A * Aᵀ)⁻¹‖ with hN_def
      have x0 := hne.some
      have hNpos : 0 < N := by
        obtain ⟨hq, hle⟩ := one_div_le_norm_inv_self_mul_transpose A hM x0.1 x0.2
        exact lt_of_lt_of_le (by positivity) hle
      have hlow : 1 / Real.sqrt N ≤ sigmaMin Aᵀ := by
        refine le_sigmaMin _ fun x hx => ?_
        obtain ⟨hq, hle⟩ := one_div_le_norm_inv_self_mul_transpose A hM x hx
        have h1 : 1 / N ≤ (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
          rw [div_le_iff₀ hNpos]; rw [div_le_iff₀ hq] at hle; linarith
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_div' _ hNpos.le, Real.sqrt_one] at h2
      have hs : 0 < sigmaMin Aᵀ := lt_of_lt_of_le (by positivity) hlow
      have hup := (isUnit_and_norm_inv_self_mul_transpose_le A hs).2
      apply le_antisymm hup
      have h1 : 1 / N ≤ sigmaMin Aᵀ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hlow 2
        rwa [div_pow, one_pow, Real.sq_sqrt hNpos.le] at this
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hNpos] at h1
      linarith
    · have h1 : (A * Aᵀ)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hM
      have h2 : sigmaMin Aᵀ = 0 := by
        rcases (sigmaMin_nonneg Aᵀ).lt_or_eq with h | h
        · exact absurd (isUnit_and_norm_inv_self_mul_transpose_le A h).1 hM
        · exact h.symm
      rw [h1, h2, norm_zero]; simp

/-- **Spectral norm of the pseudoinverse.** For every real matrix `A`,
`‖A†‖² = ‖(A Aᵀ)⁻¹‖` with `A† = pinvR A = Aᵀ (A Aᵀ)⁻¹` (`C*`-identity
`‖A†‖² = ‖(A†)ᵀ A†‖` and `(A†)ᵀ A† = (A Aᵀ)⁻¹`; both sides `0` when `A Aᵀ` is singular).

HMT 2011, proof of Prop A.3 / Prop 10.4. Atlas: `pseudoinverse`; helper for
`pinv-spectral-tail`. Generalised from `Fin r × Fin k` to arbitrary finite index types.
Ported from Prove2me solution `GaussianMatrix.specNorm_pinvR_sq`. -/
theorem specNorm_pinvR_sq [DecidableEq n] (A : Matrix m n ℝ) :
    specNorm (pinvR A) ^ 2 = specNorm (A * Aᵀ)⁻¹ := by
  unfold specNorm pinvR
  have hsym : (A * Aᵀ)ᵀ = A * Aᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have key : (Aᵀ * (A * Aᵀ)⁻¹)ᴴ * (Aᵀ * (A * Aᵀ)⁻¹) = (A * Aᵀ)⁻¹ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, hsym]
    by_cases hM : IsUnit (A * Aᵀ).det
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hM]; simp
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, key]

/-- `G ↦ ‖(G Gᵀ)⁻¹‖` is measurable on samples `G : Fin r → Fin k → ℝ`.

Helper for Tropp–Webber 2023, Lemma B.4. Atlas: `inverse-wishart-spectral-moment` (helper).
Ported from the Prove2me solution `Sol_GaussianMatrix_inverse_wishart_spectral_moment`
(`iwsm_measurable_specNorm_inv_gram`). -/
theorem measurable_specNorm_inv_self_mul_transpose {r k : ℕ} :
    Measurable (fun G : Fin r → Fin k → ℝ => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) := by
  have h1 : Measurable (fun G : Fin r → Fin k → ℝ =>
      Matrix.of.symm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply]
    exact measurable_inv_self_mul_transpose_apply a b
  have h2 : Continuous (fun M : Fin r → Fin r → ℝ => ‖Matrix.of M‖) :=
    continuous_norm.comp continuous_id
  exact h2.measurable.comp h1

/-- `G ↦ ‖G†‖` is measurable on samples `G : Fin r → Fin k → ℝ`, with `G† = pinvR G`.

Helper for HMT 2011, Prop A.4. Atlas: `pinv-spectral-expectation` (helper). Ported from the
Prove2me solution `Sol_GaussianMatrix_pinv_spectral_expectation`
(`measurable_specNorm_pinvR`). -/
theorem measurable_specNorm_pinvR {r k : ℕ} :
    Measurable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) := by
  have h1 : Measurable (fun G : Fin r → Fin k → ℝ => Matrix.of.symm (pinvR (Matrix.of G))) := by
    refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => ?_
    simp only [Matrix.of_symm_apply, pinvR, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply]
    refine Finset.measurable_sum _ fun a _ => ?_
    refine Measurable.mul ?_ (measurable_inv_self_mul_transpose_apply a i)
    exact (measurable_pi_apply a).eval
  have h2 : Continuous (fun M : Fin k → Fin r → ℝ => ‖Matrix.of M‖) :=
    continuous_norm.comp continuous_id
  exact h2.measurable.comp h1

end NLAlib
