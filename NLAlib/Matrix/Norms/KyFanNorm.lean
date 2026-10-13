import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Ky Fan norms and the nuclear norm

Definitions only, over `ℝ` or `ℂ` (any `[RCLike 𝕜]`).

* `NLAlib.kyFanNorm A k`: the sum of the `k` largest singular values of `A`, with Mathlib's
  zero-padded singular values of `Matrix.toEuclideanLin A`;
* `NLAlib.nuclearNorm A`: the sum of all singular values, `kyFanNorm A (min m n)`.

Both are real-valued for every `𝕜`, and at `𝕜 := ℝ` they are the real definitions verbatim.
The norm axioms, the Ky Fan maximum principle and the duality with the spectral norm are in
`NLAlib.Matrix.Inequalities.KyFan` and `NLAlib.Matrix.Norms.NuclearNorm`.
Source: Horn–Johnson (1991), §3.4. Atlas: `ky-fan-norms-def`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Ky Fan `k` sum of a matrix over `ℝ` or `ℂ`, with the existing zero-padded
singular-value convention. For positive `k` up to the smaller matrix dimension it is a norm; at
zero it is the zero seminorm. Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def (partial) -/
def kyFanNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, A.toEuclideanLin.singularValues i

/-- The nuclear norm of a matrix over `ℝ` or `ℂ` is the sum of all singular values, including
matrices with an empty dimension. Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def (partial) -/
def nuclearNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : ℝ :=
  kyFanNorm A (min (Fintype.card m) (Fintype.card n))

end NLAlib
