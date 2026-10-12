import NLAlib.Matrix.HermitianPartConverse

/-!
# Complete real-part eigenvalue majorization

Majorization is the exact compatibility condition for complex eigenvalues
and a prescribed Hermitian-part spectrum. Source: Horn--Johnson (2013),
Theorem 4.3.50 and Corollary 4.3.51;
atlas `real-part-eigenvalue-majorization`.
-/

noncomputable section
open Matrix Polynomial
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real-part majorization is equivalent to realization by an actual complex
matrix with both specified characteristic eigenvalue lists. This retains
all multiplicities and permits arbitrary orderings and empty dimensions.
Horn--Johnson (2013), Theorem 4.3.50.
atlas: real-part-eigenvalue-majorization (partial) -/
theorem majorized_real_parts_iff_exists_charpoly_and_selfAdjointPart_charpoly
    (x : n → ℝ) (z : n → ℂ) :
    Majorized (fun i => (z i).re) x ↔
      ∃ A : Matrix n n ℂ, A.charpoly = ∏ i, (X - C (z i)) ∧
        (selfAdjointPart ℝ A : Matrix n n ℂ).charpoly = ∏ i, (X - C (x i : ℂ)) := by
  constructor
  · exact exists_matrix_charpoly_and_selfAdjointPart_charpoly_of_majorized x z
  · rintro ⟨A, hA, hHchar⟩
    let hH : (selfAdjointPart ℝ A : Matrix n n ℂ).IsHermitian := (selfAdjointPart ℝ A).property
    have hchar : (∏ i, (X - C (hH.eigenvalues i : ℂ))) = ∏ i, (X - C (x i : ℂ)) :=
      hH.charpoly_eq.symm.trans hHchar
    obtain ⟨σ, hσ⟩ := exists_perm_eq_of_prod_X_sub_C_eq (fun i => (hH.eigenvalues i : ℂ))
      (fun i => (x i : ℂ)) hchar
    have heq : hH.eigenvalues = x ∘ σ := by
      funext i
      exact Complex.ofReal_injective (hσ i).symm
    have hm : Majorized hH.eigenvalues x := by rw [heq]; exact majorized_comp_perm x σ
    exact (majorized_real_parts_eigenvalues_selfAdjointPart A z hA).trans hm

/-- Complete real-part majorization contract: exact forward majorization,
unconditional realization of every compatible pair of eigenvalue lists,
and Bendixson's two extreme bounds for every eigenvalue. Characteristic
polynomials certify repeated values and all lists use arbitrary finite
indices. Horn--Johnson (2013), Theorem 4.3.50 and Corollary 4.3.51.
atlas: real-part-eigenvalue-majorization -/
theorem real_part_eigenvalue_majorization (x : n → ℝ) (z : n → ℂ) :
    (Majorized (fun i => (z i).re) x ↔
      ∃ A : Matrix n n ℂ, A.charpoly = ∏ i, (X - C (z i)) ∧
        (selfAdjointPart ℝ A : Matrix n n ℂ).charpoly = ∏ i, (X - C (x i : ℂ))) ∧
    (∀ A : Matrix n n ℂ, A.charpoly = ∏ i, (X - C (z i)) →
      Majorized (fun i => (z i).re)
        (Matrix.IsHermitian.eigenvalues (selfAdjointPart ℝ A).property) ∧
      ∀ i : n,
        let hdim : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
        let hH : (selfAdjointPart ℝ A : Matrix n n ℂ).IsHermitian := (selfAdjointPart ℝ A).property
        (z i).re ∈ Set.Icc
          (hH.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hdim (by decide)⟩)
          (hH.eigenvalues₀ ⟨0, hdim⟩)) := by
  refine ⟨majorized_real_parts_iff_exists_charpoly_and_selfAdjointPart_charpoly x z, ?_⟩
  intro A hA
  exact ⟨majorized_real_parts_eigenvalues_selfAdjointPart A z hA,
    real_part_eigenvalue_mem_Icc_selfAdjointPart A z hA⟩

end NLAlib
