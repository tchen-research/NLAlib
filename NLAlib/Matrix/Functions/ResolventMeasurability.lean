import NLAlib.ForMathlib.MeasureTheory.MatrixInverse
import NLAlib.Matrix.Functions.ResolventMoments
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of total matrix resolvents

The native total resolvent is measurable on every finite complex matrix,
including singular shifts. Hermitian nonreal hypotheses are needed for norm
and inverse identities, but not for measurability. Normalized Gram
moments inherit global measurability from this total resolvent.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The native total matrix resolvent is measurable on the whole matrix space. -/
theorem measurable_matrix_resolvent (ζ : ℂ) :
    Measurable (fun A : Matrix n n ℂ => resolvent A ζ) := by
  simp_rw [resolvent_matrix_eq_inv]
  apply Matrix.measurable_inv.comp
  apply Matrix.measurable_iff_entries.mpr
  intro i j
  exact measurable_const.sub (Matrix.measurable_entry i j)

/-- Native normalized Gram moments are measurable on the whole matrix space,
including singular and real shifts. -/
theorem measurable_resolventEvenMoment (z : ℂ) (p : ℕ) :
    Measurable (fun A : Matrix n n ℂ => resolventEvenMoment A z p) := by
  have hc : Continuous (fun B : Matrix n n ℂ => (normalizedTrace ((Bᴴ * B) ^ p)).re) := by
    unfold normalizedTrace
    fun_prop
  exact hc.measurable.comp (measurable_matrix_resolvent z)

end NLAlib
