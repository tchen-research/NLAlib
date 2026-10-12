import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Ky Fan norms and the nuclear norm

Definitions only.

* `NLAlib.kyFanNorm A k`: the sum of the `k` largest singular values of `A`, with Mathlib's
  zero-padded singular values of `Matrix.toEuclideanLin A`;
* `NLAlib.nuclearNorm A`: the sum of all singular values, `kyFanNorm A (min m n)`.

The norm axioms, the Ky Fan maximum principle and the duality with the spectral norm are in
`NLAlib.Matrix.Inequalities.KyFan` and `NLAlib.Matrix.Norms.NuclearNorm`.
Source: Horn–Johnson (1991), §3.4. Atlas: `ky-fan-norms-def`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

/-- The Ky Fan `k` sum, with the existing zero-padded singular-value convention.
For positive `k` up to the smaller matrix dimension it is a norm; at zero it is
the zero seminorm. Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def (partial) -/
def kyFanNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, A.toEuclideanLin.singularValues i

/-- The nuclear norm is the sum of all singular values, including matrices with
an empty dimension. Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def (partial) -/
def nuclearNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : ℝ :=
  kyFanNorm A (min (Fintype.card m) (Fintype.card n))

end NLAlib
