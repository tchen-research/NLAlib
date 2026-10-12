/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.SparseFock.ParsevalFrame
import NLAlib.Sketching.Properties.SubspaceEmbedding.Gram

set_option autoImplicit false

/-!
# Gram error of a sketch on a Parseval frame

For a sketch matrix `S` with `n` columns and a Parseval frame `F` of `n` vectors in `ℝ^d`, put
`U = rowMatrix F.u` (so `UᵀU = I`, `Frame.hasOrthonormalCols`). The embedded Gram matrix is
`Uᵀ (SᵀS) U` and the Gram error is `Uᵀ SᵀS U - I`. Its operator norm is at most `ε` exactly
when `S` is an `ε`-subspace embedding for the column space of `U`
(`norm_gramError_le_iff_isSubspaceEmbedding`, through the library lemma
`isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le`).

This is the Gram layer shared by the SparseStack model (`S = stackMatrix Z`) and the uniform
exact-`s` model (`S = sketchMatrix X`). Each model formerly carried its own copy of
`sketchGram`, `embeddedGram` and `gramError`, and its own vector form of the embedding event
(`MatrixTail.IsSparseStackOSE`, `UniformExactS.IsUniformExactSOSE`).

Ported from `SparseFockFormal.SparseStackModel` and `SparseFockFormal.MatrixTail` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib.SparseFock

open ParsevalFrame

noncomputable section

variable {k : Type*} [Fintype k] {n d : ℕ}

/-- The row matrix of a Parseval frame has orthonormal columns: the bridge from `Frame` to the
library predicate `HasOrthonormalCols`.

Source: ported from `SparseFockFormal.ParsevalFrame` (`transpose_mul_rowMatrix`),
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ParsevalFrame.Frame.hasOrthonormalCols (F : Frame n d) :
    HasOrthonormalCols (rowMatrix F.u) :=
  transpose_mul_rowMatrix F

/-- The sketch Gram matrix `SᵀS`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def sketchGram (S : Matrix k (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Sᵀ * S

/-- The embedded Gram matrix `Uᵀ (SᵀS) U` of a sketch on a Parseval frame.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def embeddedGram (F : Frame n d) (S : Matrix k (Fin n) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (rowMatrix F.u)ᵀ * (sketchGram S * rowMatrix F.u)

/-- The Gram error `Uᵀ SᵀS U - I_d`.

Source: ported from `SparseFockFormal.SparseStackModel`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def gramError (F : Frame n d) (S : Matrix k (Fin n) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  embeddedGram F S - 1

/-- The embedded Gram matrix is the Gram matrix `(SU)ᵀ(SU)` of the sketched frame.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem embeddedGram_eq_transpose_mul_self (F : Frame n d) (S : Matrix k (Fin n) ℝ) :
    embeddedGram F S = (S * rowMatrix F.u)ᵀ * (S * rowMatrix F.u) := by
  simp [embeddedGram, sketchGram, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The embedded Gram matrix is real symmetric.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem embeddedGram_isHermitian (F : Frame n d) (S : Matrix k (Fin n) ℝ) :
    (embeddedGram F S).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  change (embeddedGram F S)ᵀ = embeddedGram F S
  simp [embeddedGram, sketchGram, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The Gram error is real symmetric.

Source: ported from `SparseFockFormal.MatrixTail`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem gramError_isHermitian (F : Frame n d) (S : Matrix k (Fin n) ℝ) :
    (gramError F S).IsHermitian :=
  (embeddedGram_isHermitian F S).sub Matrix.isHermitian_one

/-- The Gram error has operator norm at most `ε` exactly when the sketch is an
`ε`-subspace embedding for the column space of the frame's row matrix.

Source: ported from `SparseFockFormal.MatrixTail`
(`sparseStack_gramError_norm_le_iff_vector_ose`),
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_gramError_le_iff_isSubspaceEmbedding (F : Frame n d)
    (S : Matrix k (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖gramError F S‖ ≤ ε ↔ IsSubspaceEmbedding S (rowMatrix F.u) ε := by
  rw [isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le F.hasOrthonormalCols hε,
    specNorm_eq_norm, gramError, embeddedGram_eq_transpose_mul_self]

end

end NLAlib.SparseFock
