import NLAlib.Matrix.Norms.FanDominance
/-!
# Complete unitarily invariant norm def contract

The clauses below are the actual universally quantified public statements,
assembled so that a full atlas tag certifies the entire family. Individual
clauses remain available in the imported topic modules.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open scoped BigOperators ENNReal
namespace NLAlib
universe u_1 u_2

/-- All clauses of the unitarily-invariant-norm-def result, with their original hypotheses,
constants, finite indices and endpoint conventions.
Components: `OrthogonallyInvariantNorm.exists_symmetricGauge_representation`, `OrthogonallyInvariantNorm.value_toSymmetricGauge`, `forall_invariantNorm_le_iff_weaklyMajorized`.
Source: bhatia97, Thm IV.2.1 (von Neumann), Thm IV.2.2 (Fan dominance); hj13, §7.4.7–7.4.8.
atlas: unitarily-invariant-norm-def -/
theorem invariant_norm_toolkit_properties :
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (ν : NLAlib.OrthogonallyInvariantNorm m n),
  ∃ (Φ : NLAlib.SymmetricGauge (Fin (Min.min (Fintype.card m) (Fintype.card n)))),
    ∀ (A : Matrix m n ℝ), ν.seminorm A = Φ.matrixValue A) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (ν : NLAlib.OrthogonallyInvariantNorm m n)
  (x : Fin (Min.min (Fintype.card m) (Fintype.card n)) → ℝ),
  ν.toSymmetricGauge.value x = ν.seminorm (NLAlib.rectangularDiagonalMatrix x)) ∧
    (∀ {m : Type u_1} {n : Type u_2} [_inst : Fintype m] [_inst_1 : Fintype n] [_inst_2 : DecidableEq m]
  [_inst_3 : DecidableEq n] (A B : Matrix m n ℝ),
  (∀ (ν : NLAlib.OrthogonallyInvariantNorm m n), ν.seminorm A ≤ ν.seminorm B) ↔
    NLAlib.WeaklyMajorized (NLAlib.singularValueVector A) (NLAlib.singularValueVector B)) ∧
    (∀ {m : Type u_1} {n : Type u_2} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Φ : SymmetricGauge (Fin (min (Fintype.card m) (Fintype.card n)))) (A : Matrix m n ℝ),
    (Φ.toOrthogonallyInvariantNorm (m := m) (n := n)).seminorm A = Φ.matrixValue A) := by
  exact ⟨@NLAlib.OrthogonallyInvariantNorm.exists_symmetricGauge_representation,
    @NLAlib.OrthogonallyInvariantNorm.value_toSymmetricGauge,
    @NLAlib.forall_invariantNorm_le_iff_weaklyMajorized,
    (by intro m n _ _ _ _ Φ A; rfl)⟩

end NLAlib
