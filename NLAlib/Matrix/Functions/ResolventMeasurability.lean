import NLAlib.ForMathlib.MeasureTheory.MatrixInverse
import NLAlib.Matrix.Functions.HermitianResolvent
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of total matrix resolvents

The native total resolvent is measurable on every finite complex matrix,
including singular shifts. Hermitian nonreal hypotheses are needed for norm
and inverse identities, but not for this measurability statement.
-/

noncomputable section
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

end NLAlib
