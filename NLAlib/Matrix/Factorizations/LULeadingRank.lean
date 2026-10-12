import NLAlib.Matrix.Factorizations.LURowInclusion
import NLAlib.Matrix.Inequalities.MajorizationProperties
import NLAlib.Matrix.Basic.Gram
/-!
# LU from leading minors through the rank

An invertible leading rank-sized block identifies a basis of the full row
space. Earlier leading blocks span every earlier coordinate space.
Horn–Johnson 2013, Corollary 3.5.4; atlas `lu-row-inclusion`.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib

private theorem exists_coefficients_supported_prefix {n k : ℕ} (hk : k ≤ n)
    (a : Fin k → ℝ) :
    ∃ c : Fin n → ℝ, (∀ j : Fin n, ¬j.val < k → c j = 0) ∧
      ∀ f : Fin n → ℝ, ∑ j : Fin n, c j * f j = ∑ j : Fin k, a j * f (Fin.castLE hk j) := by
  let c : Fin n → ℝ := fun j => if h : j.val < k then a ⟨j.val, h⟩ else 0
  refine ⟨c, ?_, ?_⟩
  · intro j hj; simp [c, hj]
  · intro f
    have h : (fun j : Fin n => c j * f j) =
        fun j => if j.val < k then c j * f j else 0 := by
      funext j
      dsimp [c]
      split_ifs <;> simp
    rw [h, sum_fin_ite_lt_eq_sum_castLE hk]
    apply Finset.sum_congr rfl
    intro j _
    simp [c, j.isLt]

/-- Nonzero leading minors through the rank imply the local row-inclusion
property, including rank zero. Horn–Johnson 2013, Corollary 3.5.4.
atlas: lu-row-inclusion (partial) -/
theorem rowInclusion_of_leading_minors_through_rank {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hRank : A.rank = k)
    (hMinors : ∀ j (hj : j ≤ n), j ≤ k → (leadingSubmatrix A j hj).det ≠ 0) :
    HasRowInclusion A := by
  have hk : k ≤ n := by simpa only [hRank] using A.rank_le_width
  have hRows : LinearIndependent ℝ (fun j : Fin k => A (Fin.castLE hk j)) := by
    let restrict : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ) := LinearMap.funLeft ℝ ℝ (Fin.castLE hk)
    apply LinearIndependent.of_comp restrict
    exact Matrix.linearIndependent_rows_of_det_ne_zero (hMinors k hk le_rfl)
  let S := Submodule.span ℝ (Set.range (fun j : Fin k => A (Fin.castLE hk j)))
  let T := Submodule.span ℝ (Set.range A.row)
  have hST : S ≤ T := Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Fin.castLE hk j, rfl⟩)
  have hDimS : Module.finrank ℝ S = k := by
    simpa only [S, Set.finrank, Fintype.card_fin] using
      (linearIndependent_iff_card_eq_finrank_span.mp hRows).symm
  have hDimT : Module.finrank ℝ T = k := by
    rw [← Matrix.rank_eq_finrank_span_row]
    exact hRank
  have hEq : S = T := Submodule.eq_of_le_of_finrank_eq hST (hDimS.trans hDimT.symm)
  intro i
  by_cases hik : i.val < k
  · let j := i.val
    have hj : j ≤ n := i.isLt.le
    let M := leadingSubmatrix A j hj
    have hM : IsUnit Mᵀ := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [Matrix.det_transpose]
      exact isUnit_iff_ne_zero.mpr (hMinors j hj (by omega))
    obtain ⟨a, ha⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hM
      (fun t : Fin j => A i (Fin.castLE hj t))
    obtain ⟨c, hc, hSum⟩ := exists_coefficients_supported_prefix hj a
    refine ⟨c, ?_, ?_⟩
    · intro t ht
      exact hc t (by simpa only [j, Fin.lt_def] using ht)
    · intro t hti
      rw [hSum]
      have h := congrFun ha (⟨t.val, by simpa only [j, Fin.lt_def] using hti⟩ : Fin j)
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        M, leadingSubmatrix, Matrix.submatrix_apply] at h
      simpa only [Fin.castLE, mul_comm] using h.symm
  · have hiRow : A i ∈ S := by
      rw [hEq]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hiRow
    obtain ⟨c, hc, hSum⟩ := exists_coefficients_supported_prefix hk a
    refine ⟨c, ?_, ?_⟩
    · intro t hti
      apply hc t
      change ¬ t.val < i.val at hti
      omega
    · intro t _
      rw [hSum]
      have h := congrFun ha t
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm

/-- If the leading principal blocks of orders one through the rank are
nonsingular, unit-lower LU and lower-times-unit-upper factorizations both
exist, possibly with different factors. Rank zero is included.
Horn–Johnson 2013, Corollary 3.5.4.
atlas: lu-row-inclusion (partial) -/
theorem exists_unit_triangular_factorizations_of_leading_minors_through_rank {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hMinors : ∀ j (hj : j ≤ n), 0 < j → j ≤ A.rank →
      (leadingSubmatrix A j hj).det ≠ 0) :
    (∃ L U : Matrix (Fin n) (Fin n) ℝ, IsLU A L U) ∧
      (∃ L U : Matrix (Fin n) (Fin n) ℝ,
        L.IsLowerTriangular ∧ IsUnitUpperTriangular U ∧ A = L * U) := by
  have hAll : ∀ j (hj : j ≤ n), j ≤ A.rank → (leadingSubmatrix A j hj).det ≠ 0 := by
    intro j hj hr
    by_cases h0 : j = 0
    · subst j; simp
    · exact hMinors j hj (Nat.pos_of_ne_zero h0) hr
  have hRows := rowInclusion_of_leading_minors_through_rank A rfl hAll
  have hAllT : ∀ j (hj : j ≤ n), j ≤ Aᵀ.rank → (leadingSubmatrix Aᵀ j hj).det ≠ 0 := by
    intro j hj hr
    have h := hAll j hj (by simpa only [Matrix.rank_transpose] using hr)
    change (Aᵀ.submatrix (Fin.castLE hj) (Fin.castLE hj)).det ≠ 0
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
    exact h
  have hCols := rowInclusion_of_leading_minors_through_rank Aᵀ rfl hAllT
  exact ⟨(exists_isLU_iff_rowInclusion A).mpr hRows,
    (exists_lower_unitUpper_iff_columnInclusion A).mpr hCols⟩

/-- All singular-LU row/column inclusion equivalences and the leading-minors-
through-rank sufficiency result. Empty and rank-zero matrices are included.
Horn–Johnson 2013, Theorem 3.5.3 and Corollary 3.5.4.
atlas: lu-row-inclusion -/
theorem lu_row_inclusion_properties {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ((∃ L U, IsLU A L U) ↔ HasRowInclusion A) ∧
    ((∃ L U, L.IsLowerTriangular ∧ IsUnitUpperTriangular U ∧ A = L * U) ↔
      HasColumnInclusion A) ∧
    ((∀ j (hj : j ≤ n), 0 < j → j ≤ A.rank → (leadingSubmatrix A j hj).det ≠ 0) →
      (∃ L U, IsLU A L U) ∧
        (∃ L U, L.IsLowerTriangular ∧ IsUnitUpperTriangular U ∧ A = L * U)) :=
  ⟨exists_isLU_iff_rowInclusion A, exists_lower_unitUpper_iff_columnInclusion A,
    exists_unit_triangular_factorizations_of_leading_minors_through_rank A⟩

end NLAlib
