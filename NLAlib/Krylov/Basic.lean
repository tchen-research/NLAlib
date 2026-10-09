import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Krylov subspaces

`NLAlib.krylovSpace A b q = span {b, A b, …, A^(q−1) b}`. The polynomial characterisation
`K_q(A,b) = {p(A) b : deg p < q}` and the Lanczos recurrence are atlas targets `krylov-subspace`,
`lanczos-recurrence`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Krylov subspace `span {A^i b : i < q}`. -/
def krylovSpace (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) : Submodule ℝ (n → ℝ) :=
  Submodule.span ℝ (Set.range fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b)

end NLAlib
