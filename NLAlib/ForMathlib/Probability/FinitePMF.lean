import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Real masses of finite probability kernels

On a finite source space, binding probability mass functions is an ordinary
finite sum of products of their real masses.
-/

namespace PMF

/-- A finite probability-kernel composition has the usual real weighted-sum
formula. All PMF masses are finite, so no additional finiteness premise is needed. -/
theorem toReal_bind_eq_sum {α β : Type*} [Fintype α] (p : PMF α)
    (q : α → PMF β) (b : β) :
    ((p.bind q) b).toReal = ∑ a, (p a).toReal * (q a b).toReal := by
  rw [bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)

end PMF
