import NLAlib.Matrix.Inequalities.FiniteExponentialGram
/-!
# Exact positivity of the entrywise exponential

The finite Vandermonde certificate and PSD exponential tail prove positive
definiteness exactly when the original PSD matrix has distinct rows. The
same criterion holds for the first `card n` exponential terms.
Source: Horn--Johnson (2013), Theorem 7.5.9;
atlas `schur-product-inequalities`.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If the entrywise exponential is positive definite, the original matrix
has pairwise distinct rows, since equality of rows survives entrywise maps.
Horn--Johnson (2013), Theorem 7.5.9; helper for the exact positivity test. -/
theorem rows_injective_of_posDef_map_exp {A : Matrix n n ℝ}
    (h : (A.map Real.exp).PosDef) : Function.Injective A.row := by
  have hinj : Function.Injective (A.map Real.exp).row :=
    (Matrix.linearIndependent_rows_iff_isUnit.mpr h.isUnit).injective
  intro i j hij
  apply hinj
  funext k
  exact congrArg Real.exp (congrFun hij k)

/-- The entrywise exponential of a PSD real matrix is positive definite
exactly when no two rows of the original matrix coincide. Singular matrices,
zero rows, and empty/singleton dimensions are included.
Horn--Johnson (2013), Theorem 7.5.9.
atlas: schur-product-inequalities (partial) -/
theorem posDef_map_exp_iff_rows_injective {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosDef ↔ Function.Injective A.row := by
  constructor
  · exact rows_injective_of_posDef_map_exp
  · intro hrows
    exact posDef_of_posDef_le (posDef_sum_inv_factorial_map_pow_of_rows_injective hA hrows)
      (sum_inv_factorial_smul_map_pow_le_map_exp hA (Fintype.card n))

/-- The first `card n` exponential terms are already positive definite
exactly when the PSD matrix has distinct rows. Exponent zero is the all-ones
feature, and all empty/singleton conventions are included.
Horn--Johnson (2013), Theorem 7.5.9; strengthened finite certificate.
atlas: schur-product-inequalities (partial) -/
theorem posDef_sum_inv_factorial_map_pow_iff_rows_injective {A : Matrix n n ℝ}
    (hA : A.PosSemidef) :
    (∑ k ∈ Finset.range (Fintype.card n), (k.factorial : ℝ)⁻¹ • A.map (fun t => t ^ k)).PosDef ↔
      Function.Injective A.row := by
  constructor
  · intro h
    exact rows_injective_of_posDef_map_exp (posDef_of_posDef_le h
      (sum_inv_factorial_smul_map_pow_le_map_exp hA (Fintype.card n)))
  · exact posDef_sum_inv_factorial_map_pow_of_rows_injective hA

end NLAlib
