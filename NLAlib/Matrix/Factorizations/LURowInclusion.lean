import NLAlib.Matrix.Factorizations.LU

/-!
# Singular LU and row/column inclusion

Local relations among original leading rows produce a unit lower elimination
matrix. Its inverse gives LU even when every pivot may vanish. Transposition
provides the dual unit-upper statement. Horn–Johnson 2013, Theorem 3.5.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- Every row's entries strictly before its diagonal label are a combination
of the preceding original rows' entries in those same columns.
Horn–Johnson 2013, Theorem 3.5.3, row inclusion property.
atlas: lu-row-inclusion (partial) -/
def HasRowInclusion {K : Type*} [Field K] (A : Matrix n n K) : Prop :=
  ∀ i : n, ∃ c : n → K, (∀ j : n, ¬j < i → c j = 0) ∧
    ∀ k : n, k < i → A i k = ∑ j : n, c j * A j k

/-- Column inclusion is row inclusion of the transpose; this is exactly the
dual leading-column condition. Horn–Johnson 2013, Theorem 3.5.3.
atlas: lu-row-inclusion (partial) -/
def HasColumnInclusion {K : Type*} [Field K] (A : Matrix n n K) : Prop := HasRowInclusion Aᵀ

/-- Row inclusion produces a unit lower elimination matrix with an upper
triangular product, without divisions or nonzero pivot assumptions.
Horn–Johnson 2013, Theorem 3.5.3.
atlas: lu-row-inclusion (partial) -/
theorem exists_unitLower_mul_upper_of_rowInclusion {A : Matrix n n ℝ}
    (hA : HasRowInclusion A) :
    ∃ H : Matrix n n ℝ, IsUnitLowerTriangular H ∧ (H * A).IsUpperTriangular := by
  classical
  choose c hc hRows using hA
  let C : Matrix n n ℝ := c
  let H : Matrix n n ℝ := 1 - C
  have hH : IsUnitLowerTriangular H := by
    constructor
    · apply isLowerTriangular_iff.mpr
      intro i j hij
      change (1 : Matrix n n ℝ) i j - c i j = 0
      rw [Matrix.one_apply_ne hij.ne, hc i j hij.not_gt, sub_self]
    · intro i
      change (1 : Matrix n n ℝ) i i - c i i = 1
      rw [Matrix.one_apply_eq, hc i i (lt_irrefl i), sub_zero]
  refine ⟨H, hH, ?_⟩
  apply isUpperTriangular_iff.mpr
  intro i k hki
  rw [show H * A = A - C * A by simp [H, Matrix.sub_mul]]
  change A i k - ∑ j : n, c i j * A j k = 0
  rw [hRows i k hki, sub_self]

/-- A singular real matrix admits a unit-lower LU factorization exactly when
it has row inclusion. Arbitrary finite ordered labels and empty matrices are
included. Horn–Johnson 2013, Theorem 3.5.3.
atlas: lu-row-inclusion (partial) -/
theorem exists_isLU_iff_rowInclusion (A : Matrix n n ℝ) :
    (∃ L U : Matrix n n ℝ, IsLU A L U) ↔ HasRowInclusion A := by
  constructor
  · rintro ⟨L, U, hLU⟩
    let H := L⁻¹
    let C := 1 - H
    have hH : IsUnitLowerTriangular H := hLU.isUnitLowerTriangular.inv
    have hHL : H * L = 1 := by
      apply Matrix.nonsing_inv_mul
      rw [hLU.isUnitLowerTriangular.det_eq_one]
      exact isUnit_one
    have hHA : H * A = U := by rw [hLU.eq_mul, ← Matrix.mul_assoc, hHL, Matrix.one_mul]
    intro i
    refine ⟨C i, ?_, ?_⟩
    · intro j hij
      by_cases hji : j = i
      · subst j; simp [C, hH.apply_self, Matrix.one_apply_eq]
      · have hlt : i < j := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm hji)
        simp [C, isLowerTriangular_iff.mp hH.isLowerTriangular i j hlt, Ne.symm hji]
    · intro k hki
      have hZero : (H * A) i k = 0 := by rw [hHA]; exact hLU.isUpperTriangular hki
      have hCA : C * A = A - H * A := by simp [C, Matrix.sub_mul]
      change A i k = (C * A) i k
      rw [hCA]
      change A i k = A i k - (H * A) i k
      rw [hZero, sub_zero]
  · intro hA
    obtain ⟨H, hH, hUpper⟩ := exists_unitLower_mul_upper_of_rowInclusion hA
    refine ⟨H⁻¹, H * A, hH.inv, hUpper, ?_⟩
    have hInv : H⁻¹ * H = 1 := by
      apply Matrix.nonsing_inv_mul
      rw [hH.det_eq_one]
      exact isUnit_one
    rw [← Matrix.mul_assoc, hInv, Matrix.one_mul]

/-- Column inclusion is equivalent to an LU factorization with a unit upper
factor, independently of row inclusion. Horn–Johnson 2013, Theorem 3.5.3.
atlas: lu-row-inclusion (partial) -/
theorem exists_lower_unitUpper_iff_columnInclusion (A : Matrix n n ℝ) :
    (∃ L U : Matrix n n ℝ, L.IsLowerTriangular ∧ IsUnitUpperTriangular U ∧ A = L * U) ↔
      HasColumnInclusion A := by
  rw [HasColumnInclusion, ← exists_isLU_iff_rowInclusion]
  constructor
  · rintro ⟨L, U, hL, hU, hA⟩
    refine ⟨Uᵀ, Lᵀ, isUnitLowerTriangular_transpose_iff.mpr hU,
      isUpperTriangular_transpose_iff.mpr hL, ?_⟩
    rw [hA, Matrix.transpose_mul]
  · rintro ⟨L, U, hLU⟩
    refine ⟨Uᵀ, Lᵀ, isLowerTriangular_transpose_iff.mpr hLU.isUpperTriangular,
      isUnitUpperTriangular_transpose_iff.mpr hLU.isUnitLowerTriangular, ?_⟩
    have h := congrArg Matrix.transpose hLU.eq_mul
    simpa only [Matrix.transpose_transpose, Matrix.transpose_mul] using h

end NLAlib
