import NLAlib.Matrix.Inequalities.Schur
import NLAlib.Matrix.Subspaces.Stiefel

/-!
# Projected eigenvector certificates for Schur–Horn

Columns of the actual orthogonal diagonalizer supply the needed eigenvectors.
Projection to a reducing coordinate set gives masses in `[0,1]`, an exact
integer budget and the exact weighted diagonal sum; normalization gives unit
eigenvectors in the set and its complement. No block diagonalization is assumed.
Source: user variational re-derivation, Schur–Horn steps 2–4.
Supports atlas `schur-horn`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared mass of a matrix column in a finite coordinate set. -/
def columnProjectionMass (Q : Matrix n n ℝ) (S : Finset n) (j : n) : ℝ := ∑ i ∈ S, Q i j ^ 2

/-- A matrix column projected onto a finite coordinate set. -/
def projectedColumn (Q : Matrix n n ℝ) (S : Finset n) (j : n) : n → ℝ :=
  fun i => if i ∈ S then Q i j else 0

/-- The normalized projected column, using the actual square root of its mass.
The unit-vector theorem assumes that this mass is positive. -/
def normalizedProjectedColumn (Q : Matrix n n ℝ) (S : Finset n) (j : n) : n → ℝ :=
  (Real.sqrt (columnProjectionMass Q S j))⁻¹ • projectedColumn Q S j

omit [Fintype n] [DecidableEq n] in
/-- The squared column projection mass is nonnegative. -/
theorem columnProjectionMass_nonneg (Q : Matrix n n ℝ) (S : Finset n) (j : n) :
    0 ≤ columnProjectionMass Q S j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Every projected mass of an orthogonal column is at most one. -/
theorem columnProjectionMass_le_one {Q : Matrix n n ℝ} (hQ : HasOrthonormalCols Q)
    (S : Finset n) (j : n) : columnProjectionMass Q S j ≤ 1 := by
  have hD := sq_entries_mem_doublyStochastic hQ
  rw [← sum_col_of_mem_doublyStochastic hD j]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => sq_nonneg _)

/-- The full projected mass budget is exactly the coordinate-set cardinality. -/
theorem sum_columnProjectionMass_eq_card {Q : Matrix n n ℝ} (hQ : HasOrthonormalCols Q)
    (S : Finset n) : (∑ j, columnProjectionMass Q S j) = (S.card : ℝ) := by
  have hD := sq_entries_mem_doublyStochastic hQ
  unfold columnProjectionMass
  rw [Finset.sum_comm]
  have hrow (i : n) : (∑ j, Q i j ^ 2) = 1 := sum_row_of_mem_doublyStochastic hD i
  simp_rw [hrow]
  simp

/-- Complementary projected column masses add to one. -/
theorem columnProjectionMass_compl {Q : Matrix n n ℝ} (hQ : HasOrthonormalCols Q)
    (S : Finset n) (j : n) : columnProjectionMass Q Sᶜ j = 1 - columnProjectionMass Q S j := by
  have hsum := Finset.sum_add_sum_compl S (fun i => Q i j ^ 2)
  have hcol : (∑ i, Q i j ^ 2) = 1 := sum_col_of_mem_doublyStochastic (sq_entries_mem_doublyStochastic hQ) j
  rw [hcol] at hsum
  unfold columnProjectionMass
  linarith

/-- Projection mass is exactly the squared Euclidean norm in dot-product coordinates. -/
theorem projectedColumn_dotProduct_self (Q : Matrix n n ℝ) (S : Finset n) (j : n) :
    projectedColumn Q S j ⬝ᵥ projectedColumn Q S j = columnProjectionMass Q S j := by
  simp [projectedColumn, dotProduct, columnProjectionMass, pow_two]

/-- A positive-mass projected column normalizes to an actual unit vector. -/
theorem normalizedProjectedColumn_dotProduct_self (Q : Matrix n n ℝ) (S : Finset n) (j : n)
    (hj : 0 < columnProjectionMass Q S j) :
    normalizedProjectedColumn Q S j ⬝ᵥ normalizedProjectedColumn Q S j = 1 := by
  have hs : Real.sqrt (columnProjectionMass Q S j) ≠ 0 := (Real.sqrt_pos.mpr hj).ne'
  have hsq := Real.sq_sqrt (columnProjectionMass_nonneg Q S j)
  unfold normalizedProjectedColumn
  rw [smul_dotProduct, dotProduct_smul, projectedColumn_dotProduct_self]
  simp only [smul_eq_mul]
  field_simp
  nlinarith

omit [Fintype n] in
/-- Normalized projected columns vanish off their coordinate set. -/
theorem normalizedProjectedColumn_apply_eq_zero_of_not_mem (Q : Matrix n n ℝ) (S : Finset n)
    (j i : n) (hi : i ∉ S) : normalizedProjectedColumn Q S j i = 0 := by
  simp [normalizedProjectedColumn, projectedColumn, hi]

/-- Projected columns on complementary coordinate sets have disjoint support. -/
theorem normalizedProjectedColumn_mul_compl_eq_zero (Q : Matrix n n ℝ) (S : Finset n)
    (j k i : n) : normalizedProjectedColumn Q S j i * normalizedProjectedColumn Q Sᶜ k i = 0 := by
  by_cases hi : i ∈ S
  · rw [normalizedProjectedColumn_apply_eq_zero_of_not_mem Q Sᶜ k i (by simpa using hi), mul_zero]
  · rw [normalizedProjectedColumn_apply_eq_zero_of_not_mem Q S j i hi, zero_mul]

/-- Normalized projected columns in complementary coordinate sets are orthogonal. -/
theorem normalizedProjectedColumn_dotProduct_compl_eq_zero (Q : Matrix n n ℝ) (S : Finset n)
    (j k : n) : normalizedProjectedColumn Q S j ⬝ᵥ normalizedProjectedColumn Q Sᶜ k = 0 :=
  Finset.sum_eq_zero (fun i _ => normalizedProjectedColumn_mul_compl_eq_zero Q S j k i)

/-- Spectral factorization turns every orthogonal diagonalizer column into an
actual eigenvector at the given coefficient. -/
theorem mulVec_column_eq_smul_of_orthogonal_diagonalization {A Q : Matrix n n ℝ}
    (hQ : HasOrthonormalCols Q) (lam : n → ℝ) (hA : A = Q * Matrix.diagonal lam * Qᵀ) (j : n) :
    A *ᵥ (fun i => Q i j) = lam j • (fun i => Q i j) := by
  have hAQ : A * Q = Q * Matrix.diagonal lam := by
    calc
      A * Q = Q * Matrix.diagonal lam * (Qᵀ * Q) := by rw [hA]; simp only [Matrix.mul_assoc]
      _ = Q * Matrix.diagonal lam := by rw [hQ, Matrix.mul_one]
  funext i
  have h := congrArg (fun M : Matrix n n ℝ => M i j) hAQ
  rw [Matrix.mul_diagonal] at h
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm] using h

/-- The exact subset diagonal sum is the spectral sum weighted by projected masses. -/
theorem sum_mul_columnProjectionMass_eq_sum_diagonal {A Q : Matrix n n ℝ}
    (lam : n → ℝ) (hA : A = Q * Matrix.diagonal lam * Qᵀ) (S : Finset n) :
    (∑ j, lam j * columnProjectionMass Q S j) = ∑ i ∈ S, A i i := by
  have hdiag (i : n) : A i i = ∑ j, lam j * Q i j ^ 2 := by
    rw [hA, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [columnProjectionMass, Finset.mul_sum, hdiag]
  exact Finset.sum_comm

/-- The coordinate-set selector is its actual diagonal orthogonal projection. -/
def coordinateSelector (S : Finset n) : Matrix n n ℝ := Matrix.diagonal (fun i => if i ∈ S then 1 else 0)

/-- A reducing cross-zero coordinate set commutes with the actual Hermitian matrix. -/
theorem coordinateSelector_commute_of_cross_eq_zero {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Finset n) (hcross : ∀ i ∈ S, ∀ k ∉ S, A i k = 0) :
    A * coordinateSelector S = coordinateSelector S * A := by
  have hs (i k : n) : A i k = A k i := by
    have h := congrArg (fun M : Matrix n n ℝ => M k i) hA.eq
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply] using h
  ext i k
  rw [coordinateSelector, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S
  · simp [hi, hk]
  · simp [hi, hk, hcross i hi k hk]
  · simp [hi, hk, hs i k, hcross k hk i hi]
  · simp [hi, hk]

/-- Multiplying by the coordinate selector gives the actual projected column. -/
theorem coordinateSelector_mulVec_column (Q : Matrix n n ℝ) (S : Finset n) (j : n) :
    coordinateSelector S *ᵥ (fun i => Q i j) = projectedColumn Q S j := by
  funext i
  rw [coordinateSelector, Matrix.mulVec_diagonal]
  simp [projectedColumn]

/-- A column projected onto a reducing coordinate set is still an actual
eigenvector, without a nonzero-mass or simple-spectrum hypothesis. -/
theorem mulVec_projectedColumn_eq_smul {A Q : Matrix n n ℝ} (hQ : HasOrthonormalCols Q)
    (lam : n → ℝ) (hA : A = Q * Matrix.diagonal lam * Qᵀ) (S : Finset n)
    (hcomm : A * coordinateSelector S = coordinateSelector S * A) (j : n) :
    A *ᵥ projectedColumn Q S j = lam j • projectedColumn Q S j := by
  rw [← coordinateSelector_mulVec_column Q S j, Matrix.mulVec_mulVec, hcomm,
    ← Matrix.mulVec_mulVec, mulVec_column_eq_smul_of_orthogonal_diagonalization hQ lam hA j,
    Matrix.mulVec_smul]

/-- A normalized projected column is an eigenvector with the same eigenvalue,
derived from actual orthogonal factorization and reduction. -/
theorem mulVec_normalizedProjectedColumn_eq_smul {A Q : Matrix n n ℝ} (hQ : HasOrthonormalCols Q)
    (lam : n → ℝ) (hA : A = Q * Matrix.diagonal lam * Qᵀ) (S : Finset n)
    (hcomm : A * coordinateSelector S = coordinateSelector S * A) (j : n) :
    A *ᵥ normalizedProjectedColumn Q S j = lam j • normalizedProjectedColumn Q S j := by
  unfold normalizedProjectedColumn
  rw [Matrix.mulVec_smul, mulVec_projectedColumn_eq_smul hQ lam hA S hcomm]
  exact smul_comm _ _ _

/-- Complementary coordinate selectors are exactly the residual projection. -/
theorem coordinateSelector_compl (S : Finset n) : coordinateSelector Sᶜ = 1 - coordinateSelector S := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S <;> simp [coordinateSelector, hi]
  · simp [coordinateSelector, hij]

/-- A reducing selector has a reducing complementary selector. -/
theorem coordinateSelector_compl_commute {A : Matrix n n ℝ} (S : Finset n)
    (hcomm : A * coordinateSelector S = coordinateSelector S * A) :
    A * coordinateSelector Sᶜ = coordinateSelector Sᶜ * A := by
  rw [coordinateSelector_compl, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hcomm]

/-- Positive inside mass and non-full outside mass give an actual pair of
disjoint unit eigenvectors, using the given orthogonal diagonalizer columns.
Every norm, eigenvalue and support condition is derived from the actual matrix. -/
theorem exists_projectedColumn_pair {A Q : Matrix n n ℝ} (hQ : HasOrthonormalCols Q)
    (lam : n → ℝ) (hFactor : A = Q * Matrix.diagonal lam * Qᵀ) (hA : A.IsHermitian)
    (S : Finset n) (hcross : ∀ i ∈ S, ∀ k ∉ S, A i k = 0) (j k : n)
    (hj : 0 < columnProjectionMass Q S j) (hk : columnProjectionMass Q S k < 1) :
    ∃ u v : n → ℝ, u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 ∧
      A *ᵥ u = lam j • u ∧ A *ᵥ v = lam k • v ∧ (∀ i, u i * v i = 0) ∧
      (∀ i ∉ S, u i = 0) ∧ (∀ i ∈ S, v i = 0) := by
  have hcomm := coordinateSelector_commute_of_cross_eq_zero hA S hcross
  have hcommc := coordinateSelector_compl_commute S hcomm
  have hkc : 0 < columnProjectionMass Q Sᶜ k := by
    rw [columnProjectionMass_compl hQ]
    linarith
  refine ⟨normalizedProjectedColumn Q S j, normalizedProjectedColumn Q Sᶜ k,
    normalizedProjectedColumn_dotProduct_self Q S j hj,
    normalizedProjectedColumn_dotProduct_self Q Sᶜ k hkc,
    normalizedProjectedColumn_dotProduct_compl_eq_zero Q S j k,
    mulVec_normalizedProjectedColumn_eq_smul hQ lam hFactor S hcomm j,
    mulVec_normalizedProjectedColumn_eq_smul hQ lam hFactor Sᶜ hcommc k,
    fun i => normalizedProjectedColumn_mul_compl_eq_zero Q S j k i,
    fun i hi => normalizedProjectedColumn_apply_eq_zero_of_not_mem Q S j i hi,
    fun i hi => normalizedProjectedColumn_apply_eq_zero_of_not_mem Q Sᶜ k i (by simpa using hi)⟩

/-- Orthogonal square matrices form a compact set on arbitrary finite index
types, by transporting the already proved finite orthogonal-group compactness. -/
theorem isCompact_orthogonalMatrices : IsCompact {Q : Matrix n n ℝ | HasOrthonormalCols Q} := by
  let e := Fintype.equivFin n
  let L := Matrix.reindexLinearEquiv ℝ ℝ e.symm e.symm
  let F : Matrix.orthogonalGroup (Fin (Fintype.card n)) ℝ → Matrix n n ℝ := fun O => L O.val
  have hF : Continuous F := L.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val
  have heq : Set.range F = {Q : Matrix n n ℝ | HasOrthonormalCols Q} := by
    ext Q
    constructor
    · rintro ⟨O, rfl⟩
      exact (show HasOrthonormalCols O.val from transpose_mul_self_orthogonalGroup O).reindex e.symm e.symm
    · intro hQ
      let O : Matrix.orthogonalGroup (Fin (Fintype.card n)) ℝ :=
        ⟨Q.reindex e e, (Matrix.mem_orthogonalGroup_iff' (Fin (Fintype.card n)) ℝ).mpr (hQ.reindex e e)⟩
      refine ⟨O, ?_⟩
      ext i j
      simp [F, L, O, Matrix.reindex_apply]
  rw [← heq]
  exact isCompact_range hF

/-- Every continuous real objective has an actual global minimizer over all
real orthogonal matrices, including empty dimensions. -/
theorem exists_orthogonal_isMinOn_of_continuous (F : Matrix n n ℝ → ℝ) (hF : Continuous F) :
    ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧
      ∀ R : Matrix n n ℝ, HasOrthonormalCols R → F Q ≤ F R := by
  obtain ⟨Q, hQ, hmin⟩ := isCompact_orthogonalMatrices.exists_isMinOn
    ⟨1, by simp [HasOrthonormalCols]⟩ hF.continuousOn
  exact ⟨Q, hQ, fun R hR => hmin hR⟩

end NLAlib
