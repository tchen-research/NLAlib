import NLAlib.Matrix.Perturbation.Sylvester
/-!
# Two coupled norm inequalities

The scalar engine of Wedin's theorem retains constant one for the maximum
operator norm and the paired Euclidean/Frobenius norm. It uses two component
inequalities and Cauchy–Schwarz, without Hermitian dilation.
-/

noncomputable section
namespace NLAlib

/-- Two coupled nonnegative scalar inequalities give the maximum-norm
separation bound. Wedin (1972), direct two-residual proof. -/
theorem sub_mul_max_le_max_of_coupled {α β x y f g : ℝ}
    (hβ : 0 ≤ β) (hx : α*x ≤ β*y+f) (hy : α*y ≤ β*x+g) :
    (α-β)*max x y ≤ max f g := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]
    have hh := mul_le_mul_of_nonneg_left h hβ
    exact (show (α-β)*y ≤ g by nlinarith).trans (le_max_right _ _)
  · rw [max_eq_left h]
    have hh := mul_le_mul_of_nonneg_left h hβ
    exact (show (α-β)*x ≤ f by nlinarith).trans (le_max_left _ _)

/-- The paired squared-norm separation estimate from two coupled
nonnegative inequalities. Wedin (1972), with no loss in the constant. -/
theorem sub_sq_mul_add_sq_le_add_sq_of_coupled {α β x y f g : ℝ}
    (hδ : 0 ≤ α-β) (hβ : 0 ≤ β) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (_hf0 : 0 ≤ f) (_hg0 : 0 ≤ g)
    (hx : α*x ≤ β*y+f) (hy : α*y ≤ β*x+g) :
    (α-β)^2*(x^2+y^2) ≤ f^2+g^2 := by
  have hxx := mul_le_mul_of_nonneg_right hx hx0
  have hyy := mul_le_mul_of_nonneg_right hy hy0
  have hdiff := mul_nonneg hβ (sq_nonneg (x-y))
  have hbase : (α-β)*(x^2+y^2) ≤ f*x+g*y := by nlinarith
  have hcs : (f*x+g*y)^2 ≤ (f^2+g^2)*(x^2+y^2) := by
    nlinarith [sq_nonneg (f*y-g*x)]
  have hs0 : 0 ≤ (α-β)*(x^2+y^2) := mul_nonneg hδ (by positivity)
  have hsq := pow_le_pow_left₀ hs0 hbase 2
  by_cases hz : x^2+y^2=0
  · rw [hz, mul_zero]
    positivity
  have hs : 0 < x^2+y^2 := lt_of_le_of_ne (by positivity) (Ne.symm hz)
  have hmul : ((α-β)^2*(x^2+y^2))*(x^2+y^2) ≤ (f^2+g^2)*(x^2+y^2) := by
    nlinarith [hsq, hcs]
  exact (mul_le_mul_iff_left₀ hs).mp (by simpa only [mul_comm (x^2+y^2)] using hmul)

end NLAlib
