import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Conditional expectation preserves positive semidefinite matrix order

The actual closed convex positive semidefinite cone gives conditional positivity and
Loewner monotonicity on arbitrary underlying measurable spaces.
-/

noncomputable section

open MeasureTheory Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] [DecidableEq n]
variable {μ : Measure Ω}

omit [Fintype n] [DecidableEq n] in
/-- The cone of positive semidefinite complex matrices is convex as a real set.
Source: quadratic-form positivity; helper for operator rederivations Section 3.1
and atlas `matrix-freedman`. -/
theorem convex_setOf_posSemidef_complex :
    Convex ℝ {A : Matrix n n ℂ | A.PosSemidef} := by
  intro A hA B hB a b ha hb hab
  exact (hA.smul ha).add (hB.smul hb)

/-- The cone of positive semidefinite complex matrices is closed.
Source: the closed positive cone of a C-star algebra; helper for operator
rederivations Section 3.1 and atlas `matrix-freedman`. -/
theorem isClosed_setOf_posSemidef_complex :
    IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
  simpa only [Set.Ici, Matrix.nonneg_iff_posSemidef] using
    (isClosed_Ici : IsClosed (Set.Ici (0 : Matrix n n ℂ)))

/-- Conditional expectation preserves actual positive semidefinite matrix values almost
everywhere. Closed convex conditional-mean membership proves this for arbitrary `Ω`.
Source: Mathlib conditional Jensen membership; operator rederivations Section 3.1.
atlas: matrix-freedman (partial) -/
theorem ae_posSemidef_condExp_of_ae_posSemidef (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {X : Ω → Matrix n n ℂ} (hX : Integrable X μ) (hpos : ∀ᵐ ω ∂μ, (X ω).PosSemidef) :
    ∀ᵐ ω ∂μ, (μ[X | m] ω).PosSemidef :=
  convex_setOf_posSemidef_complex.condExp_mem hm hX isClosed_setOf_posSemidef_complex hpos

/-- Actual conditional expectations preserve Loewner order for integrable complex matrix
functions. This is derived from conditional positivity of the difference.
Source: operator rederivations Section 3.1; atlas `matrix-freedman` (helper). -/
theorem ae_condExp_le_condExp_of_ae_le (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {X Y : Ω → Matrix n n ℂ} (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY : X ≤ᵐ[μ] Y) : μ[X | m] ≤ᵐ[μ] μ[Y | m] := by
  have hpos := ae_posSemidef_condExp_of_ae_posSemidef hm (hY.sub hX)
    (hXY.mono fun ω hω => Matrix.le_iff.mp hω)
  filter_upwards [hpos, condExp_sub hY hX m] with ω hpos heq
  rw [heq] at hpos
  exact Matrix.le_iff.mpr hpos

end NLAlib
