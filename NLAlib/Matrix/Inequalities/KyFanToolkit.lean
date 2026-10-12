import NLAlib.Matrix.Inequalities.KyFanNorms
import NLAlib.Matrix.Inequalities.KyFanSums
/-!
# Complete ky fan maximum principle contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open scoped BigOperators ENNReal
namespace NLAlib
universe u_1 u_2 u_3

/-- All clauses of the ky-fan-maximum-principle result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `trace_compression_le_eigenvaluePrefix`, `exists_trace_compression_eq_eigenvaluePrefix`, `sum_bottom_eigenvalues_le_trace_compression`, `exists_trace_compression_eq_bottom_eigenvalues`, `trace_twoSided_compression_le_kyFanNorm`, `exists_trace_twoSided_compression_eq_kyFanNorm`, `majorized_eigenvalues₀_add`, `weaklyMajorized_singularValues_add`.
Source: fan49, Thm 1; hj13, Cor 4.3.39; hj91, Thm 3.4.1.
atlas: ky-fan-maximum-principle -/
theorem ky_fan_toolkit_properties :
    (∀ {n : Type u_1} {r : Type u_2} [_inst : Fintype n] [_inst_1 : Fintype r] [_inst_2 : DecidableEq n]
  [_inst_3 : DecidableEq r] {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : Matrix n r ℝ}
  (hQ : NLAlib.HasOrthonormalCols Q),
  (Q.transpose * A * Q).trace ≤
    NLAlib.eigenvaluePrefix hA (NLAlib.card_le_card_of_hasOrthonormalCols hQ)) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
  {k : ℕ} (hk : k ≤ Fintype.card n),
  ∃ (Q : Matrix n (Fin k) ℝ),
    NLAlib.HasOrthonormalCols Q ∧ (Q.transpose * A * Q).trace = NLAlib.eigenvaluePrefix hA hk) ∧
    (∀ {n : Type u_1} {r : Type u_2} [_inst : Fintype n] [_inst_1 : Fintype r] [_inst_2 : DecidableEq n]
  [_inst_3 : DecidableEq r] {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : Matrix n r ℝ}
  (hQ : NLAlib.HasOrthonormalCols Q),
  ∑ i : Fin (Fintype.card r),
      hA.eigenvalues₀
        ⟨↑i + (Fintype.card n - Fintype.card r), by
          have := NLAlib.card_le_card_of_hasOrthonormalCols hQ; omega⟩ ≤
    (Q.transpose * A * Q).trace) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
  {k : ℕ} (hk : k ≤ Fintype.card n),
  ∃ (Q : Matrix n (Fin k) ℝ),
    NLAlib.HasOrthonormalCols Q ∧
      (Q.transpose * A * Q).trace =
        ∑ i : Fin k,
          hA.eigenvalues₀
            ⟨↑i + (Fintype.card n - k), by omega⟩) ∧
    (∀ {m : Type u_1} {n : Type u_2} {r : Type u_3} [_inst : Fintype m] [_inst_1 : Fintype n]
  [_inst_2 : Fintype r] [_inst_3 : DecidableEq n] [_inst_4 : DecidableEq r] (A : Matrix m n ℝ)
  {U : Matrix m r ℝ} {V : Matrix n r ℝ},
  NLAlib.HasOrthonormalCols U →
    NLAlib.HasOrthonormalCols V → (U.transpose * A * V).trace ≤ NLAlib.kyFanNorm A (Fintype.card r)) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A : Matrix m n ℝ) {k : ℕ},
  k ≤ Min.min (Fintype.card m) (Fintype.card n) →
    ∃ (U : Matrix m (Fin k) ℝ) (V : Matrix n (Fin k) ℝ),
      NLAlib.HasOrthonormalCols U ∧
        NLAlib.HasOrthonormalCols V ∧ (U.transpose * A * V).trace = NLAlib.kyFanNorm A k) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A B : Matrix n n ℝ}
  (hA : A.IsHermitian) (hB : B.IsHermitian),
  NLAlib.Majorized (Matrix.IsHermitian.add hA hB).eigenvalues₀ (hA.eigenvalues₀ + hB.eigenvalues₀)) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [DecidableEq m]
  [_inst_3 : DecidableEq n] (A B : Matrix m n ℝ),
  NLAlib.WeaklyMajorized
    (fun (i : Fin (Min.min (Fintype.card m) (Fintype.card n))) =>
      singularValues (A + B) ↑i)
    fun (i : Fin (Min.min (Fintype.card m) (Fintype.card n))) =>
    singularValues A ↑i + singularValues B ↑i) := by
  exact ⟨@NLAlib.trace_compression_le_eigenvaluePrefix,
    @NLAlib.exists_trace_compression_eq_eigenvaluePrefix,
    @NLAlib.sum_bottom_eigenvalues_le_trace_compression,
    @NLAlib.exists_trace_compression_eq_bottom_eigenvalues,
    @NLAlib.trace_twoSided_compression_le_kyFanNorm,
    @NLAlib.exists_trace_twoSided_compression_eq_kyFanNorm,
    @NLAlib.majorized_eigenvalues₀_add,
    @NLAlib.weaklyMajorized_singularValues_add⟩

end NLAlib
