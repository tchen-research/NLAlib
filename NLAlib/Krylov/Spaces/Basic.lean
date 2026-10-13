import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Krylov subspaces

`NLAlib.krylovSpace A b q = span {b, A b, …, A^(q−1) b}`. The theorems about it (polynomial
characterisation, monotonicity, dimension bound) are in `NLAlib.Krylov.Spaces.Polynomial`.

Atlas: `krylov-subspace` (definition).
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Krylov subspace `K_q(A, b) = span {A^i b : i < q}`, over any field `K` (the
theorems about it are stated over `ℝ`). Source: Golub–Meurant (2010) [`gm10`], Ch. 4.
Atlas: `krylov-subspace`.
atlas: krylov-subspace -/
def krylovSpace {K : Type*} [Field K] (A : Matrix n n K) (b : n → K) (q : ℕ) :
    Submodule K (n → K) :=
  Submodule.span K (Set.range fun i : Fin q => (A ^ (i : ℕ)) *ᵥ b)

end NLAlib
