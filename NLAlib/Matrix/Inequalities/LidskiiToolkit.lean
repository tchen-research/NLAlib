import NLAlib.Matrix.Norms.NuclearHermitian
import NLAlib.Matrix.Norms.FanDominance
import NLAlib.Matrix.Inequalities.MirskyPadded
/-!
# Complete lidskii contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open scoped BigOperators ENNReal
namespace NLAlib
universe u_1 u_2

/-- All clauses of the lidskii result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `majorized_eigenvalues₀_add_sub`, `weaklyMajorized_abs_singularValues_add_sub`, `weaklyMajorized_abs_singularValues_add_sub_padded`, `invariantNorm_rectangularDiagonal_singularValues_add_sub_le`, `sum_abs_eigenvalues₀_add_sub_le_nuclearNorm`.
Source: bhatia97, Thm III.4.1 (Lidskii), Thm IV.3.4 (Mirsky); mo11, 9.G.
atlas: lidskii -/
theorem lidskii_toolkit_properties :
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A B : Matrix n n ℝ}
  (hA : A.IsHermitian) (hB : B.IsHermitian),
  NLAlib.Majorized
    (fun (i : Fin (Fintype.card n)) =>
      (Matrix.IsHermitian.add hA hB).eigenvalues₀ i - hA.eigenvalues₀ i)
    hB.eigenvalues₀) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A E : Matrix m n ℝ),
  NLAlib.WeaklyMajorized
    (fun (i : Fin (Min.min (Fintype.card m) (Fintype.card n))) =>
      |singularValues (A + E) ↑i -
          singularValues A ↑i|)
    fun (i : Fin (Min.min (Fintype.card m) (Fintype.card n))) =>
    singularValues E ↑i) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq n]
  (A E : Matrix m n ℝ) (d : ℕ),
  NLAlib.WeaklyMajorized
    (fun (i : Fin d) =>
      |singularValues (A + E) ↑i -
          singularValues A ↑i|)
    fun (i : Fin d) => singularValues E ↑i) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (ν : NLAlib.OrthogonallyInvariantNorm m n) (A E : Matrix m n ℝ),
  ν.seminorm
      (NLAlib.rectangularDiagonalMatrix fun (i : Fin (Min.min (Fintype.card m) (Fintype.card n))) =>
        singularValues (A + E) ↑i -
          singularValues A ↑i) ≤
    ν.seminorm E) ∧
    (∀ {n : Type u_1} [_inst : Fintype n] [_inst_1 : DecidableEq n] {A E : Matrix n n ℝ}
  (hA : A.IsHermitian) (hE : E.IsHermitian),
  ∑ i : Fin (Fintype.card n), |(Matrix.IsHermitian.add hA hE).eigenvalues₀ i - hA.eigenvalues₀ i| ≤
    NLAlib.nuclearNorm E) := by
  exact ⟨@NLAlib.majorized_eigenvalues₀_add_sub,
    @NLAlib.weaklyMajorized_abs_singularValues_add_sub,
    @NLAlib.weaklyMajorized_abs_singularValues_add_sub_padded,
    @NLAlib.invariantNorm_rectangularDiagonal_singularValues_add_sub_le,
    @NLAlib.sum_abs_eigenvalues₀_add_sub_le_nuclearNorm⟩

end NLAlib
