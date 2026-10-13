import NLAlib.Matrix.Inequalities.HermitianPartConverse
import NLAlib.Matrix.Inequalities.HermitianPart
/-!
# Real-part eigenvalue majorization: the characterisation

Majorization is the exact compatibility condition between a list of complex eigenvalues and
a prescribed Hermitian-part spectrum (forward direction `HermitianPart.lean`, converse
`HermitianPartConverse.lean`). Horn–Johnson 2013, Theorem 4.3.50.
Atlas: `real-part-eigenvalue-majorization`.
-/

noncomputable section
open Matrix Polynomial
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Real-part majorization (Horn–Johnson Thm 4.3.50).** `Re z ≺ x` if and only if some complex
matrix has eigenvalues `z` (as a characteristic polynomial) and Hermitian part with eigenvalues
`x`; multiplicities, arbitrary orderings and empty dimensions are included.
atlas: real-part-eigenvalue-majorization -/
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

end NLAlib
