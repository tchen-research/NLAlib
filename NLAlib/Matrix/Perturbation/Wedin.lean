import NLAlib.Matrix.Perturbation.WedinResidual
/-!
# Wedin perturbation and population-gap bounds

Actual perturbed SVD residuals are perturbation times the paired leading frames.
The exact mixed-gap bounds imply the perturbation bound, and Weyl plus the unit
sine bound gives the unconditional population-gap estimate. Source: Wedin (1972),
Section 3; Stewart–Sun, Theorem V.4.4. Atlas: `wedin-sin-theta`.
-/
noncomputable section
open scoped Matrix
namespace NLAlib
namespace IsSVD

/-- The leading right-frame singular residual equals minus perturbation times
that frame. Wedin (1972), Section 3; the frames are from an actual SVD of `A+E`. -/
theorem headColumns_left_residual_eq_neg_mul {m n k : ℕ}
    {A E : Matrix (Fin m) (Fin n) ℝ} {Uhat : Matrix (Fin m) (Fin m) ℝ}
    {Vhat : Matrix (Fin n) (Fin n) ℝ} (hhat : IsSVD (A + E) Uhat Vhat)
    (hkm : k ≤ m) (hkn : k ≤ n) :
    A * headColumns Vhat hkn - headColumns Uhat hkm *
      Matrix.diagonal (fun i : Fin k => singularValues (A + E) i) =
        -(E * headColumns Vhat hkn) := by
  rw [← hhat.mul_headColumns hkm hkn, Matrix.add_mul]
  abel

/-- The transpose leading-frame residual is the paired perturbation residual.
Wedin (1972), Section 3; every rectangular null direction remains included. -/
theorem headColumns_right_residual_eq_neg_mul {m n k : ℕ}
    {A E : Matrix (Fin m) (Fin n) ℝ} {Uhat : Matrix (Fin m) (Fin m) ℝ}
    {Vhat : Matrix (Fin n) (Fin n) ℝ} (hhat : IsSVD (A + E) Uhat Vhat)
    (hkm : k ≤ m) (hkn : k ≤ n) :
    Aᵀ * headColumns Uhat hkm - headColumns Vhat hkn *
      Matrix.diagonal (fun i : Fin k => singularValues (A + E) i) =
        -(Eᵀ * headColumns Uhat hkm) := by
  rw [← hhat.transpose_mul_headColumns hkm hkn, Matrix.transpose_add, Matrix.add_mul]
  abel

end IsSVD

/-- Wedin's exact operator bound measured by the two actual perturbation-frame
products. Wedin (1972), Section 3; all admissible rectangular endpoints are allowed.
atlas: wedin-sin-theta (partial) -/
theorem max_specNorm_sinePrincipalAngles_le_max_perturbation_frame_div
    {m n k : ℕ} {A E : Matrix (Fin m) (Fin n) ℝ}
    {U Uhat : Matrix (Fin m) (Fin m) ℝ} {V Vhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSVD A U V) (hhat : IsSVD (A + E) Uhat Vhat) (hk : k ≤ min m n)
    (hδ : 0 < singularValues (A + E) (k - 1) - singularValues A k) :
    let U₁ := headColumns U (hk.trans (min_le_left m n))
    let V₁ := headColumns V (hk.trans (min_le_right m n))
    let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
    let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
    max (specNorm (sinePrincipalAngles U₁ Uhat₁)) (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤
      max (specNorm (E * Vhat₁)) (specNorm (Eᵀ * Uhat₁)) /
        (singularValues (A + E) (k - 1) - singularValues A k) := by
  have h := max_specNorm_sinePrincipalAngles_le_max_residual_div hA hhat hk hδ
  dsimp only at h ⊢
  rw [hhat.headColumns_left_residual_eq_neg_mul,
    hhat.headColumns_right_residual_eq_neg_mul, specNorm_neg, specNorm_neg] at h
  exact h

/-- Wedin's paired Frobenius bound with the exact perturbation-frame residuals.
Wedin (1972), Section 3; no factor is lost in combining the two residual norms.
atlas: wedin-sin-theta (partial) -/
theorem sqrt_add_sq_frobNorm_sinePrincipalAngles_le_sqrt_add_sq_perturbation_frame_div
    {m n k : ℕ} {A E : Matrix (Fin m) (Fin n) ℝ}
    {U Uhat : Matrix (Fin m) (Fin m) ℝ} {V Vhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSVD A U V) (hhat : IsSVD (A + E) Uhat Vhat) (hk : k ≤ min m n)
    (hδ : 0 < singularValues (A + E) (k - 1) - singularValues A k) :
    let U₁ := headColumns U (hk.trans (min_le_left m n))
    let V₁ := headColumns V (hk.trans (min_le_right m n))
    let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
    let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
    Real.sqrt (frobNorm (sinePrincipalAngles U₁ Uhat₁) ^ 2 +
      frobNorm (sinePrincipalAngles V₁ Vhat₁) ^ 2) ≤
      Real.sqrt (frobNorm (E * Vhat₁) ^ 2 + frobNorm (Eᵀ * Uhat₁) ^ 2) /
        (singularValues (A + E) (k - 1) - singularValues A k) := by
  have h := sqrt_add_sq_frobNorm_sinePrincipalAngles_le_sqrt_add_sq_residual_div hA hhat hk hδ
  dsimp only at h ⊢
  rw [hhat.headColumns_left_residual_eq_neg_mul,
    hhat.headColumns_right_residual_eq_neg_mul, frobNorm_neg, frobNorm_neg] at h
  exact h

/-- Wedin's mixed-gap sine operator norms are both at most the perturbation
operator norm divided by the actual mixed gap. Wedin (1972), Section 3.
atlas: wedin-sin-theta (partial) -/
theorem max_specNorm_sinePrincipalAngles_le_specNorm_div
    {m n k : ℕ} {A E : Matrix (Fin m) (Fin n) ℝ}
    {U Uhat : Matrix (Fin m) (Fin m) ℝ} {V Vhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSVD A U V) (hhat : IsSVD (A + E) Uhat Vhat) (hk : k ≤ min m n)
    (hδ : 0 < singularValues (A + E) (k - 1) - singularValues A k) :
    let U₁ := headColumns U (hk.trans (min_le_left m n))
    let V₁ := headColumns V (hk.trans (min_le_right m n))
    let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
    let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
    max (specNorm (sinePrincipalAngles U₁ Uhat₁)) (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤
      specNorm E / (singularValues (A + E) (k - 1) - singularValues A k) := by
  have h := max_specNorm_sinePrincipalAngles_le_max_perturbation_frame_div hA hhat hk hδ
  dsimp only at h ⊢
  apply h.trans
  apply div_le_div_of_nonneg_right _ hδ.le
  apply max_le
  · exact specNorm_mul_frame_le (hasOrthonormalCols_headColumns hhat.transpose_mul_right _) E
  · simpa only [specNorm_transpose] using
      specNorm_mul_frame_le (hasOrthonormalCols_headColumns hhat.transpose_mul_left _) Eᵀ

/-- The leading singular-space population-gap operator bound holds without
any smallness hypothesis on the perturbation. Wedin (1972), Section 3; Weyl
and the unit sine bound give the exact constant two. The next singular value is
zero padded at `k=min(m,n)`, including unmatched rectangular null directions.
atlas: wedin-sin-theta (partial) -/
theorem max_specNorm_sinePrincipalAngles_le_two_mul_specNorm_div_population_gap
    {m n k : ℕ} {A E : Matrix (Fin m) (Fin n) ℝ}
    {U Uhat : Matrix (Fin m) (Fin m) ℝ} {V Vhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSVD A U V) (hhat : IsSVD (A + E) Uhat Vhat) (hk : k ≤ min m n)
    (hg : 0 < singularValues A (k - 1) - singularValues A k) :
    let U₁ := headColumns U (hk.trans (min_le_left m n))
    let V₁ := headColumns V (hk.trans (min_le_right m n))
    let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
    let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
    max (specNorm (sinePrincipalAngles U₁ Uhat₁)) (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤
      2 * specNorm E / (singularValues A (k - 1) - singularValues A k) := by
  dsimp only
  let U₁ := headColumns U (hk.trans (min_le_left m n))
  let V₁ := headColumns V (hk.trans (min_le_right m n))
  let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
  let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
  let M := max (specNorm (sinePrincipalAngles U₁ Uhat₁)) (specNorm (sinePrincipalAngles V₁ Vhat₁))
  have hM0 : 0 ≤ M := (specNorm_nonneg _).trans (le_max_left _ _)
  apply (le_div_iff₀ hg).2
  by_cases hsmall : specNorm E < (singularValues A (k - 1) - singularValues A k) / 2
  · have hweyl := singularValues_le_singularValues_add_add_specNorm A E (k - 1)
    have hδ : 0 < singularValues (A + E) (k - 1) - singularValues A k := by linarith
    have hmix := max_specNorm_sinePrincipalAngles_le_specNorm_div hA hhat hk hδ
    have hmult := (le_div_iff₀ hδ).mp hmix
    have hgap : (singularValues A (k - 1) - singularValues A k) / 2 ≤
        singularValues (A + E) (k - 1) - singularValues A k := by linarith
    have hh := mul_le_mul_of_nonneg_left hgap hM0
    change M * (singularValues A (k - 1) - singularValues A k) ≤ _
    change M * (singularValues (A + E) (k - 1) - singularValues A k) ≤ _ at hmult
    nlinarith
  · have hM : M ≤ 1 := max_le
      (specNorm_sinePrincipalAngles_le_one
        (hasOrthonormalCols_headColumns hA.transpose_mul_left _)
        (hasOrthonormalCols_headColumns hhat.transpose_mul_left _))
      (specNorm_sinePrincipalAngles_le_one
        (hasOrthonormalCols_headColumns hA.transpose_mul_right _)
        (hasOrthonormalCols_headColumns hhat.transpose_mul_right _))
    have hh := mul_le_mul_of_nonneg_right hM hg.le
    change M * (singularValues A (k - 1) - singularValues A k) ≤ _
    nlinarith

end NLAlib
