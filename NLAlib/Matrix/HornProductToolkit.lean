import NLAlib.Matrix.HornPowerSums

/-!
# Complete horn product inequality contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open scoped BigOperators ENNReal
namespace NLAlib
universe u_1 u_2 u_3

/-- All clauses of the horn-product-inequality result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `prod_toEuclideanLin_singularValues_mul_le`, `sum_range_toEuclideanLin_singularValues_mul_rpow_le`.
Source: hj91, Thm 3.3.4 (Horn), Thm 3.3.14 (weak majorization); mo11, 9.H.1.
atlas: horn-product-inequality -/
theorem horn_product_toolkit_properties :
    (∀ {m : Type u_1} {p : Type u_2} {n : Type u_3} [_inst : Fintype m] [_inst_1 : Fintype p]
  [_inst_2 : Fintype n] [_inst_3 : DecidableEq p] [_inst_4 : DecidableEq n] (A : Matrix m p ℝ)
  (B : Matrix p n ℝ) (k : ℕ),
  ∏ i ∈ Finset.range k, (Matrix.toEuclideanLin (A * B)).singularValues i ≤
    ∏ i ∈ Finset.range k,
      (Matrix.toEuclideanLin A).singularValues i * (Matrix.toEuclideanLin B).singularValues i) ∧
    (∀ {m : Type u_1} {n : Type u_2} {q : Type u_3} [_inst : Fintype m] [_inst_1 : Fintype n]
  [_inst_2 : Fintype q] [_inst_3 : DecidableEq n] [_inst_4 : DecidableEq q] (A : Matrix m n ℝ)
  (B : Matrix n q ℝ) (N : ℕ) {p : ℝ},
  0 < p →
    ∑ i ∈ Finset.range N, (Matrix.toEuclideanLin (A * B)).singularValues i ^ p ≤
      ∑ i ∈ Finset.range N,
        ((Matrix.toEuclideanLin A).singularValues i * (Matrix.toEuclideanLin B).singularValues i) ^
          p) := by
  exact ⟨@NLAlib.prod_toEuclideanLin_singularValues_mul_le,
    @NLAlib.sum_range_toEuclideanLin_singularValues_mul_rpow_le⟩

end NLAlib
