import NLAlib.Matrix.Spectral.SingularValueInvariance
import NLAlib.Matrix.Inequalities.TraceTail

/-!
# Spectral sums of the two Gram matrices

The two Gram matrices have the same nonzero spectrum with multiplicity.
Zero padding of singular values proves equality for any scalar test
vanishing at zero. Horn--Johnson, Matrix Analysis, Section 7.3.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- Any zero-preserving function of a singular-value list may be summed
over any sufficiently long zero-padded prefix. -/
theorem sum_range_singularValues_map_eq_of_min_le {R : Type*} [AddCommMonoid R]
    (A : Matrix m n 𝕜) (f : ℝ → R) (hf : f 0=0) {N : ℕ}
    (hN : min (Fintype.card m) (Fintype.card n) ≤ N) :
    (∑ i ∈ Finset.range N, f (singularValues A i)) =
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), f (singularValues A i) := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro i _ hi
  rw [singularValues_eq_zero_of_min_le A (by simpa only [Finset.mem_range, not_lt] using hi), hf]

omit [DecidableEq m] in
/-- Every scalar spectral sum of a column Gram matrix is its corresponding
squared-singular-value sum, including the padded zero values. -/
theorem sum_eigenvalues_gram_eq_sum_singularValues (A : Matrix m n 𝕜) (f : ℝ → ℝ) :
    (∑ i, f ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)) =
      ∑ i ∈ Finset.range (Fintype.card n), f (singularValues A i ^ 2) := by
  rw [sum_eigenvalues_eq_sum_sorted]
  simp_rw [← sq_singularValues_eq_eigenvalues₀]
  exact Fin.sum_univ_eq_sum_range (fun i => f (singularValues A i ^ 2)) (Fintype.card n)

/-- The two Gram matrices have identical scalar spectral sums for every
test function vanishing at zero, with arbitrary rectangular dimensions. -/
theorem sum_eigenvalues_mul_adjoint_eq_adjoint_mul (A : Matrix m n 𝕜)
    (f : ℝ → ℝ) (hf : f 0=0) :
    (∑ i, f ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i)) =
      ∑ i, f ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) := by
  have hl := sum_eigenvalues_gram_eq_sum_singularValues A.conjTranspose f
  simp only [Matrix.conjTranspose_conjTranspose] at hl
  rw [hl, sum_eigenvalues_gram_eq_sum_singularValues]
  simp only [singularValues_conjTranspose]
  rw [sum_range_singularValues_map_eq_of_min_le A (fun x => f (x^2)) (by simpa using hf) (min_le_left _ _),
    sum_range_singularValues_map_eq_of_min_le A (fun x => f (x^2)) (by simpa using hf) (min_le_right _ _)]

end NLAlib
