import NLAlib.Matrix.ConditionNumber
import NLAlib.Matrix.InversePerturbationBounds

/-!
# Attained distance to singularity

For nonsingular square matrices of positive dimension, the absolute spectral
distance is the reciprocal inverse norm and the relative distance is the
reciprocal condition number. A truncated SVD supplies an actual attaining
perturbation. Source: Higham, Theorem 6.5; Golub--Van Loan, Section 2.6.2.
Supports `condition-number-def`; empty dimensions are deliberately excluded
because their singular set is empty.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A nonsingular matrix in positive dimension has a nonzero inverse norm.
Source: the inverse identity; supports `condition-number-def`. -/
theorem specNorm_inv_pos_of_isUnit {A : Matrix n n ℝ} (hA : IsUnit A) :
    0 < specNorm A⁻¹ := by
  apply norm_pos_iff.mpr
  intro hZero
  have h := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  rw [hZero, Matrix.zero_mul] at h
  exact one_ne_zero h.symm

/-- Every perturbation producing a singular matrix has spectral norm at least
the reciprocal inverse norm. Higham, Theorem 6.5.
atlas: condition-number-def (partial) -/
theorem inv_specNorm_inv_le_specNorm_of_not_isUnit_add
    {A E : Matrix n n ℝ} (hA : IsUnit A) (hAE : ¬ IsUnit (A + E)) :
    1 / specNorm A⁻¹ ≤ specNorm E := by
  by_contra h
  have hN := specNorm_inv_pos_of_isUnit hA
  have hSmall : specNorm E < 1 / specNorm A⁻¹ := lt_of_not_ge h
  have hProd : specNorm A⁻¹ * specNorm E < 1 := by
    have h := (lt_div_iff₀ hN).mp hSmall
    simpa only [mul_comm] using h
  exact hAE (isUnit_add_of_specNorm_inv_mul_lt_one hA
    ((specNorm_mul_le A⁻¹ E).trans_lt hProd))

/-- An actual singular perturbation attains the reciprocal inverse norm.
Higham, Theorem 6.5. The construction uses spectral Eckart--Young rather
than an assumed minimizing perturbation.
atlas: condition-number-def (partial) -/
theorem exists_not_isUnit_add_specNorm_eq_inv_specNorm_inv
    (A : Matrix n n ℝ) (hA : IsUnit A) :
    ∃ E : Matrix n n ℝ, ¬ IsUnit (A + E) ∧ specNorm E = 1 / specNorm A⁻¹ := by
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let A' := A.reindex e e
  let T := truncatedSVD A' (Fintype.card n - 1)
  let E := (T - A').reindex e.symm e.symm
  have hRank : A'.rank = Fintype.card n := by
    simpa only [A', Matrix.rank_reindex] using Matrix.rank_of_isUnit A hA
  have hRankPos : 0 < A'.rank := by rw [hRank]; exact Fintype.card_pos
  have hE : A + E = T.reindex e.symm e.symm := by
    ext i j
    simp [E, A', Matrix.reindex_apply]
  refine ⟨E, ?_, ?_⟩
  · intro hUnit
    have hr := Matrix.rank_of_isUnit (A + E) hUnit
    rw [hE, Matrix.rank_reindex] at hr
    have hBound := (isBestRankApprox_truncatedSVD A' (Fintype.card n - 1)).1
    have hPos : 0 < Fintype.card n := Fintype.card_pos
    change T.rank ≤ Fintype.card n - 1 at hBound
    omega
  · have hN := specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive A' hRankPos
    rw [hRank] at hN
    have hInv : specNorm A⁻¹ = 1 / singularValues A' (Fintype.card n - 1) := by
      simpa only [A', moorePenroseInverse_reindex, specNorm_reindex,
        moorePenroseInverse_eq_inv_of_isUnit A hA] using hN
    calc
      specNorm E = specNorm (T - A') := specNorm_reindex _ _ _
      _ = singularValues A' (Fintype.card n - 1) := by
        rw [specNorm_sub_comm]
        exact specNorm_sub_truncatedSVD_eq A' _
      _ = 1 / specNorm A⁻¹ := by rw [hInv, one_div_one_div]

/-- The absolute distance to the singular set is an attained minimum.
Higham, Theorem 6.5.
atlas: condition-number-def (partial) -/
theorem isLeast_specNorm_singular_perturbations (A : Matrix n n ℝ) (hA : IsUnit A) :
    IsLeast (specNorm '' {E : Matrix n n ℝ | ¬ IsUnit (A + E)})
      (1 / specNorm A⁻¹) := by
  obtain ⟨E, hE, hNorm⟩ := exists_not_isUnit_add_specNorm_eq_inv_specNorm_inv A hA
  refine ⟨⟨E, hE, hNorm⟩, ?_⟩
  rintro _ ⟨F, hF, rfl⟩
  exact inv_specNorm_inv_le_specNorm_of_not_isUnit_add hA hF

/-- The original matrix has positive spectral norm on the nonsingular,
positive-dimensional branch. Source: the inverse identity; supports
`condition-number-def`. -/
theorem specNorm_pos_of_isUnit {A : Matrix n n ℝ} (hA : IsUnit A) : 0 < specNorm A := by
  apply norm_pos_iff.mpr
  intro hZero
  have h := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  rw [hZero, Matrix.zero_mul] at h
  exact one_ne_zero h.symm

/-- The relative distance to singularity is the attained reciprocal condition
number. Higham, Theorem 6.5.
atlas: condition-number-def (partial) -/
theorem isLeast_relative_singular_perturbations (A : Matrix n n ℝ) (hA : IsUnit A) :
    IsLeast ((fun E : Matrix n n ℝ => specNorm E / specNorm A) ''
      {E | ¬ IsUnit (A + E)}) (1 / conditionNumber A) := by
  have hNorm := specNorm_pos_of_isUnit hA
  obtain ⟨E, hE, hNormE⟩ := exists_not_isUnit_add_specNorm_eq_inv_specNorm_inv A hA
  have hRel : (1 / specNorm A⁻¹) / specNorm A = 1 / conditionNumber A := by
    rw [conditionNumber_eq_mul_specNorm_inv hA]
    ring
  constructor
  · refine ⟨E, hE, ?_⟩
    dsimp only
    rw [hNormE, hRel]
  · rintro _ ⟨F, hF, rfl⟩
    dsimp only
    rw [← hRel]
    exact div_le_div_of_nonneg_right (inv_specNorm_inv_le_specNorm_of_not_isUnit_add hA hF)
      hNorm.le

end NLAlib
