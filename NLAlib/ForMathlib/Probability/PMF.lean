import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite probability mass function expectations

The real masses of a finite probability mass function sum to one.
-/

noncomputable section
namespace PMF

/-- The real masses of a finite probability mass function sum to one. -/
theorem sum_toReal {J : Type*} [Fintype J] (q : PMF J) : ∑ j, (q j).toReal = 1 := by
  classical
  rw [← ENNReal.toReal_sum (fun j _ => q.apply_ne_top j)]
  have hsum : ∑ j, q j = 1 := by simpa only [tsum_fintype] using q.tsum_coe
  simp [hsum]

end PMF
