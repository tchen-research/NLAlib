import NLAlib.Matrix.Wedin

/-!
# Complete leading singular-subspace perturbation interface

All catalogue Wedin conclusions are supplied for actual paired SVD frames:
exact residual identities, constant-one mixed-gap maximum and paired-Frobenius
bounds, unconditional population-gap constant two, and empty-frame endpoints.
Source: Wedin (1972), Section 3; Stewart–Sun, Theorem V.4.4.
-/
noncomputable section
open scoped Matrix
namespace NLAlib

/-- A zero-width pair of frames has an empty, zero sine-angle matrix.
Stewart–Sun, Section I.5; the ambient shape may also be empty. -/
theorem sinePrincipalAngles_eq_zero_of_card_eq_zero {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P Q : Matrix m n ℝ) (hn : Fintype.card n = 0) : sinePrincipalAngles P Q = 0 := by
  ext i j
  have hi := i.isLt
  omega

/-- Every Wedin conclusion for actual leading singular-vector frames, including
the exact perturbation residuals, constant-one mixed-gap operator and paired
Frobenius bounds, constant-two population-gap operator bound without a
perturbation smallness premise, and the zero-width endpoint. Wedin (1972),
Section 3; Stewart–Sun, Theorem V.4.4. Rectangular full-thin endpoints use the
zero-padded next singular value and arbitrary valid SVD choices are accepted.
atlas: wedin-sin-theta -/
theorem singular_subspace_perturbation_bounds
    {m n k : ℕ} {A E : Matrix (Fin m) (Fin n) ℝ}
    {U Uhat : Matrix (Fin m) (Fin m) ℝ} {V Vhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSVD A U V) (hhat : IsSVD (A + E) Uhat Vhat) (hk : k ≤ min m n) :
    let U₁ := headColumns U (hk.trans (min_le_left m n))
    let V₁ := headColumns V (hk.trans (min_le_right m n))
    let Uhat₁ := headColumns Uhat (hk.trans (min_le_left m n))
    let Vhat₁ := headColumns Vhat (hk.trans (min_le_right m n))
    let T := Matrix.diagonal (fun i : Fin k => singularValues (A + E) i)
    let R := A * Vhat₁ - Uhat₁ * T
    let S := Aᵀ * Uhat₁ - Vhat₁ * T
    let δ := singularValues (A + E) (k - 1) - singularValues A k
    let g := singularValues A (k - 1) - singularValues A k
    R = -(E * Vhat₁) ∧ S = -(Eᵀ * Uhat₁) ∧
      max (specNorm R) (specNorm S) ≤ specNorm E ∧
      (0 < δ →
        max (specNorm (sinePrincipalAngles U₁ Uhat₁))
          (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤ max (specNorm R) (specNorm S) / δ ∧
        max (specNorm (sinePrincipalAngles U₁ Uhat₁))
          (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤ specNorm E / δ ∧
        Real.sqrt (frobNorm (sinePrincipalAngles U₁ Uhat₁) ^ 2 +
          frobNorm (sinePrincipalAngles V₁ Vhat₁) ^ 2) ≤
            Real.sqrt (frobNorm R ^ 2 + frobNorm S ^ 2) / δ) ∧
      (0 < g → max (specNorm (sinePrincipalAngles U₁ Uhat₁))
        (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤ 2 * specNorm E / g) ∧
      (k = 0 → specNorm (sinePrincipalAngles U₁ Uhat₁) = 0 ∧
        specNorm (sinePrincipalAngles V₁ Vhat₁) = 0 ∧
        frobNorm (sinePrincipalAngles U₁ Uhat₁) = 0 ∧
        frobNorm (sinePrincipalAngles V₁ Vhat₁) = 0) := by
  dsimp only
  have hR := hhat.headColumns_left_residual_eq_neg_mul
    (hk.trans (min_le_left m n)) (hk.trans (min_le_right m n))
  have hS := hhat.headColumns_right_residual_eq_neg_mul
    (hk.trans (min_le_left m n)) (hk.trans (min_le_right m n))
  refine ⟨hR, hS, ?_, ?_, ?_, ?_⟩
  · rw [hR, hS, specNorm_neg, specNorm_neg]
    apply max_le
    · exact specNorm_mul_frame_le (hasOrthonormalCols_headColumns hhat.transpose_mul_right _) E
    · simpa only [specNorm_transpose] using
        specNorm_mul_frame_le (hasOrthonormalCols_headColumns hhat.transpose_mul_left _) Eᵀ
  · intro hδ
    exact ⟨max_specNorm_sinePrincipalAngles_le_max_residual_div hA hhat hk hδ,
      max_specNorm_sinePrincipalAngles_le_specNorm_div hA hhat hk hδ,
      sqrt_add_sq_frobNorm_sinePrincipalAngles_le_sqrt_add_sq_residual_div hA hhat hk hδ⟩
  · exact max_specNorm_sinePrincipalAngles_le_two_mul_specNorm_div_population_gap hA hhat hk
  · intro hk0
    subst k
    rw [sinePrincipalAngles_eq_zero_of_card_eq_zero _ _ (by simp),
      sinePrincipalAngles_eq_zero_of_card_eq_zero _ _ (by simp)]
    simp [specNorm_zero, frobNorm_zero]

end NLAlib
