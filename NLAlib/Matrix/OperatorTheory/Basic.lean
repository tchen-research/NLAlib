import NLAlib.Matrix.Functions.ExpLog

/-!
# Matrix functions, relative entropy, operator convexity

Matrix relative entropy, operator convexity on an interval, and the matrix perspective. The standard
matrix function `f(A)` (Tropp 2015, §2.1.6) is Mathlib's continuous functional calculus `cfc f A`.
`relativeEntropy` and `matrixPerspective` are over `[RCLike 𝕜]`; `OperatorConvexOn` quantifies
over complex matrices of every size.

Tropp 2015, §8.1, Def. 8.4.6 and Def. 8.6.1. Atlas: `operator-monotone-convex`.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder
open scoped MatrixOrder

noncomputable section
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **matrix relative entropy** `D(A; H) = re tr (A (log A − log H) − (A − H))`. Tropp 2015,
eq. (8.1.1).
atlas: operator-monotone-convex -/
def relativeEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (A H : Matrix d d 𝕜) : ℝ :=
  RCLike.re (Matrix.trace (A * (matrixLog A - matrixLog H) - (A - H)))

/-- Over `ℂ` the relative entropy is a `Complex.re`, by `rfl`. -/
theorem relativeEntropy_complex {d : Type*} [Fintype d] [DecidableEq d] (A H : Matrix d d ℂ) :
    relativeEntropy A H = (Matrix.trace (A * (matrixLog A - matrixLog H) - (A - H))).re :=
  rfl

/-- `f` is **operator convex** on the convex set `I`: `f (t A + (1−t) H) ≼ t f(A) + (1−t) f(H)`
for all Hermitian complex matrices `A`, `H` of every size with spectra in `I`. "Every size" is
encoded as `∀ d : ℕ, … Matrix (Fin d) (Fin d) ℂ` (universe-safe; `Fintype` index types reduce to
it by reindexing, `OperatorConvexOn.cfc_conjTranspose_mul_mul_le`); the size `d = 0` holds
trivially. The definition is over `ℂ`; the real case follows by complexification. Tropp 2015,
Def. 8.4.6.
atlas: operator-monotone-convex -/
def OperatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ I ∧ ∀ (d : ℕ) (A H : Matrix (Fin d) (Fin d) ℂ),
    A.IsHermitian → H.IsHermitian → spectrum ℝ A ⊆ I → spectrum ℝ H ⊆ I →
    ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      (cfc f (t • A + (1 - t) • H)) ≤
        (t • cfc f A + (1 - t) • cfc f H)

/-- The **matrix perspective** `A^{1/2} f(A^{−1/2} H A^{−1/2}) A^{1/2}` (junk, through Mathlib's
`cfc`, when `A` is not positive definite). Tropp 2015, Def. 8.6.1.
atlas: operator-monotone-convex -/
def matrixPerspective {d : Type*} [Fintype d] [DecidableEq d]
    (f : ℝ → ℝ) (A H : Matrix d d 𝕜) : Matrix d d 𝕜 :=
  let S := cfc Real.sqrt A
  let R := cfc (fun x => (Real.sqrt x)⁻¹) A
  S * cfc f (R * H * R) * S

end NLAlib
