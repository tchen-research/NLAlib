/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.ExactSparseRoundedBounds

set_option autoImplicit false

/-!
# Exact-s public matrix embedding theorem

The full explicit parameter package and concrete orthonormal-matrix embedding endpoints.
Ported from `SparseFockFormal.UniformExactSMainTheorem` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace NLAlib.SparseFock.UniformExactS

open ParsevalFrame SparseIIDCoupling ProductFock VacuumMoment
open ConcreteLadder FiniteHilbert PaperParameters

noncomputable section

variable {b s n d : ℕ}

/-! ## Literal vector OSE and the operator-norm event -/

/-- Every conclusion of the canonical uniform signed exact-`s` OSNAP
theorem for a fixed Parseval frame.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
structure UniformExactSMainConclusions
    {n d : ℕ} (delta eps : ℝ) (F : Frame n d)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) : Prop where
  operatorFailure :
    (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
      {X | eps < ‖gramError F X‖} ≤ delta
  oseSuccess :
    1 - delta ≤
      (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
        {X | IsUniformExactSOSE F X eps}
  exactColumnSparsity :
    ∀ (X : ExactSample
        (roundedS (failureOrder d delta) eps *
          roundedB d (failureOrder d delta) eps)
        (roundedS (failureOrder d delta) eps) n) (i : Fin n),
      Fintype.card
        {r : Fin (roundedS (failureOrder d delta) eps *
          roundedB d (failureOrder d delta) eps) //
          sketchMatrix X r i ≠ 0} =
        roundedS (failureOrder d delta) eps
  qAtLeastOne : 1 ≤ failureOrder d delta
  sparsityStrict :
    (roundedS (failureOrder d delta) eps : ℝ) <
      1356 * (failureOrder d delta : ℝ) / eps
  rowsStrict :
    (roundedM d (failureOrder d delta) eps : ℝ) <
      306456 * ((d : ℝ) + failureOrder d delta) / eps ^ 2
  bAtLeastTwo : 2 ≤ roundedB d (failureOrder d delta) eps
  rowsFactor :
    roundedM d (failureOrder d delta) eps =
      roundedS (failureOrder d delta) eps *
        roundedB d (failureOrder d delta) eps

/-- Hypothesis-free canonical theorem for independent uniform signed exact-`s`
columns.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_main
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d) :
    UniformExactSMainConclusions delta eps F heps0 heps1 := by
  have hparams := main_parameter_package
    (d := d) (delta := delta) hd heps0 heps1
  rcases hparams with ⟨_hsLower, _hmLower, hsStrict, hmStrict, hbTwo⟩
  refine
    { operatorFailure :=
        uniformExactS_rounded_operator_norm_failure_le_delta
          hd hdelta0 hdelta1 heps0 heps1 F
      oseSuccess :=
        uniformExactS_rounded_ose_success
          hd hdelta0 hdelta1 heps0 heps1 F
      exactColumnSparsity := ?_
      qAtLeastOne := one_le_failureOrder d delta
      sparsityStrict := hsStrict
      rowsStrict := hmStrict
      bAtLeastTwo := hbTwo
      rowsFactor := roundedM_eq_s_mul_b d (failureOrder d delta) eps }
  intro X i
  exact exactly_s_nonzeros_per_column X
    (roundedS_pos (q := failureOrder d delta) heps0) i

/-! ## Literal source-matrix form -/

open MatrixFrameBridge

/-- Literal vector OSE property for an `n × d` matrix with orthonormal
columns.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def IsMatrixUniformExactSOSE
    (U : Matrix (Fin n) (Fin d) ℝ)
    (X : ExactSample (s * b) s n) (eps : ℝ) : Prop :=
  ∀ x : EVec d,
    (1 - eps) * ‖x‖ ^ 2 ≤
        ‖MatrixTail.applyRectMatrix (sketchMatrix X * U) x‖ ^ 2 ∧
      ‖MatrixTail.applyRectMatrix (sketchMatrix X * U) x‖ ^ 2 ≤
        (1 + eps) * ‖x‖ ^ 2

/-- The matrix-based exact-s Gram error equals the error of its constructed Parseval frame.
Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem gramError_frameOfMatrix_exactS
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ))
    (X : ExactSample (s * b) s n) :
    gramError (frameOfMatrix U hU) X =
      U.transpose * (sketchGram X * U) - 1 := by
  simp [gramError, embeddedGram]

/-- The exact-s action on a constructed frame equals the literal sketch applied to the input matrix vector.
Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem exactSVector_frameOfMatrix
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ))
    (X : ExactSample (s * b) s n) (x : EVec d) :
    exactSVector (frameOfMatrix U hU) X x =
      MatrixTail.applyRectMatrix (sketchMatrix X * U) x := by
  simp [exactSVector]

/-- Literal source-matrix operator-norm tail.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_matrix_operator_failure
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) :
    (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
      {X | eps <
        ‖U.transpose * (sketchGram X * U) - 1‖} ≤ delta := by
  let F := frameOfMatrix U hU
  simpa [F] using
    (uniformExactS_rounded_operator_norm_failure_le_delta
      hd hdelta0 hdelta1 heps0 heps1 F)

/-- Literal source-matrix vector OSE success probability.

Source: ported from `SparseFockFormal.UniformExactSMainTheorem`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem uniformExactS_matrix_ose_success
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) :
    1 - delta ≤
      (exactSampleLaw (n := n)
        (exactS_le_rows (s := roundedS (failureOrder d delta) eps)
          (MainTheoremAssembly.canonicalB_pos
            (d := d) (delta := delta) heps0 heps1))).prob
        {X | IsMatrixUniformExactSOSE U X eps} := by
  let F := frameOfMatrix U hU
  simpa [F, IsUniformExactSOSE, IsMatrixUniformExactSOSE] using
    (uniformExactS_rounded_ose_success
      hd hdelta0 hdelta1 heps0 heps1 F)

end

end NLAlib.SparseFock.UniformExactS
