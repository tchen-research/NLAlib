/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.MatrixTail
import Mathlib.Tactic

set_option autoImplicit false

/-!
# From an orthonormal-column matrix to the Parseval-frame representation

The paper starts with an `n × d` matrix `U` satisfying `UᵀU = I`.  The
operator proof uses its rows as a Parseval frame.  This file makes that change
of representation literal and reversible at the matrix level.
-/

namespace NLAlib.SparseFock.MatrixFrameBridge

open ParsevalFrame
open SparseStackModel

noncomputable section

/-- The Euclidean row family of a real matrix.

Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def matrixRows {n d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ) : Fin n → EVec d :=
  fun i ↦ WithLp.toLp 2 (fun a ↦ U i a)

/-- The Euclidean matrix-row family reads the original matrix entries.
Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem matrixRows_apply {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) (a : Fin d) :
    matrixRows U i a = U i a := rfl

/-- Converting matrix rows back to their coordinate matrix recovers the input.
Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem rowMatrix_matrixRows {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ) :
    rowMatrix (matrixRows U) = U := by
  rfl

/-- An orthonormal-column matrix, represented as the exact Parseval structure
used by the sparse-Fock proof.

Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def frameOfMatrix {n d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) : Frame n d where
  u := matrixRows U
  parseval := by
    apply (parseval_iff_transpose_mul (matrixRows U)).2
    simpa using hU

/-- The Parseval frame of an orthonormal-column matrix consists of its Euclidean rows.
Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem frameOfMatrix_u {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ))
    (i : Fin n) (a : Fin d) :
    (frameOfMatrix U hU).u i a = U i a := rfl

/-- The coordinate row matrix of the constructed Parseval frame recovers the input.
Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem frameOfMatrix_rowMatrix {n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ)) :
    rowMatrix (frameOfMatrix U hU).u = U := by
  rfl

/-- The embedded Gram matrix becomes the paper's literal
`Uᵀ (Piᵀ Pi) U`.

Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem embeddedGram_frameOfMatrix {s b n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ))
    (Z : Sample s b n) :
    embeddedGram (frameOfMatrix U hU) Z =
      U.transpose * (sketchGram Z * U) := by
  simp [embeddedGram]

/-- Consequently the formal Gram error is exactly the displayed matrix in the
main probability event.

Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem gramError_frameOfMatrix {s b n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ))
    (Z : Sample s b n) :
    gramError (frameOfMatrix U hU) Z =
      U.transpose * (sketchGram Z * U) - 1 := by
  simp [gramError]

/-- The vector in the OSE conclusion is literally the stack matrix applied to
`U x`.

Source: ported from `SparseFockFormal.MatrixFrameBridge`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem sparseStackVector_frameOfMatrix {s b n d : ℕ}
    (U : Matrix (Fin n) (Fin d) ℝ)
    (hU : U.transpose * U = (1 : Matrix (Fin d) (Fin d) ℝ))
    (Z : Sample s b n) (x : EVec d) :
    MatrixTail.sparseStackVector (frameOfMatrix U hU) Z x =
      MatrixTail.applyRectMatrix (stackMatrix Z * U) x := by
  simp [MatrixTail.sparseStackVector]

end

end NLAlib.SparseFock.MatrixFrameBridge
