import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
/-!
# Hermitian dilation

The Hermitian dilation `[0 A; Aᴴ 0]` of a rectangular matrix over any ring with a star (complex
matrices for matrix concentration, real matrices, where `Aᴴ = Aᵀ`, for the Mirsky and Lidskii
arguments), with its immediate API: it is Hermitian (`isHermitian_dilation`) and additive
(`dilation_add`).

Tropp 2015, §2.1.17. Atlas: `hermitian-dilation`.
-/

namespace NLAlib

/-- The Hermitian dilation `fromBlocks 0 A Aᴴ 0` of a rectangular matrix `A`. Tropp 2015,
Def. 2.1.5; over `ℝ` this is the symmetric dilation `[0 A; Aᵀ 0]` of Bhatia 1997, Section III.4.
Stated over any `α` with `0` and `star` (generalised from `ℂ`).
atlas: hermitian-dilation -/
def dilation {α : Type*} [Zero α] [Star α] {m n : Type*} (A : Matrix m n α) :
    Matrix (Sum m n) (Sum m n) α := Matrix.fromBlocks 0 A A.conjTranspose 0

/-- The dilation is Hermitian (symmetric over `ℝ`). Bhatia 1997, Section III.4;
Tropp 2015, §2.1.16. -/
theorem isHermitian_dilation {α : Type*} [AddMonoid α] [StarAddMonoid α] {m n : Type*}
    (A : Matrix m n α) : (dilation A).IsHermitian := by
  simp [dilation, Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]

/-- The dilation is additive. Bhatia 1997, Section III.4. -/
theorem dilation_add {α : Type*} [AddMonoid α] [StarAddMonoid α] {m n : Type*}
    (A B : Matrix m n α) : dilation (A + B) = dilation A + dilation B := by
  simp [dilation, Matrix.fromBlocks_add]

end NLAlib
