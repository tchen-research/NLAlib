import NLAlib.Krylov.Spaces.Polynomial
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A matrix of Krylov generators

The unorthogonalized matrix `[b, A b, ..., A^(q-1) b]` represents the existing
`krylovSpace` for every grade, including zero width and dependent columns.
Source: Saad (2003), Section 6.1.
-/

open scoped Matrix
namespace NLAlib

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- The first `q` powers of the matrix applied to `b`, as columns. -/
def krylovMatrix (A : Matrix n n K) (b : n → K) (q : ℕ) : Matrix n (Fin q) K :=
  fun i j => (A ^ (j : ℕ) *ᵥ b) i

/-- The generator matrix spans the native Krylov space even at and after breakdown. -/
theorem range_krylovMatrix (A : Matrix n n K) (b : n → K) (q : ℕ) :
    LinearMap.range (krylovMatrix A b q).mulVecLin = krylovSpace A b q := by
  rw [Matrix.range_mulVecLin]
  rfl

/-- Multiplication by `A` shifts every generator by one power. -/
theorem mul_krylovMatrix_apply (A : Matrix n n K) (b : n → K) (q : ℕ)
    (i : n) (j : Fin q) :
    (A * krylovMatrix A b q) i j = (A ^ ((j : ℕ) + 1) *ᵥ b) i := by
  change (A *ᵥ (A ^ (j : ℕ) *ᵥ b)) i = _
  rw [Matrix.mulVec_mulVec, ← pow_succ']

end NLAlib
