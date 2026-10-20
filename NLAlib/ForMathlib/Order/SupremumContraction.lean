import Mathlib.Order.ConditionallyCompleteLattice.Group
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A two-sign supremum contraction inequality

Pairwise contraction of one real coordinate decreases its two signed
suprema. The parameter class is arbitrary and need not have a maximizer.
This algebraic step underlies Rademacher contraction.
-/

noncomputable section
set_option autoImplicit false

namespace Real

/-- Contracting the differences of one coordinate decreases the sum of its
two signed supremum values. The parameter class can be arbitrary. -/
theorem ciSup_add_ciSup_le_of_abs_sub_le {T : Type*} [Nonempty T]
    (b x y : T → ℝ)
    (hplus : BddAbove (Set.range fun t => b t + x t))
    (hminus : BddAbove (Set.range fun t => b t - x t))
    (hcontract : ∀ t u, |y t - y u| ≤ |x t - x u|) :
    (⨆ t, b t + y t) + (⨆ t, b t - y t) ≤
      (⨆ t, b t + x t) + (⨆ t, b t - x t) := by
  apply ciSup_add_ciSup_le
  intro t u
  have hd := (le_abs_self (y t - y u)).trans (hcontract t u)
  rcases le_total (x t) (x u) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hd
    have ht := le_ciSup hminus t
    have hu := le_ciSup hplus u
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hd
    have ht := le_ciSup hplus t
    have hu := le_ciSup hminus u
    linarith

end Real
