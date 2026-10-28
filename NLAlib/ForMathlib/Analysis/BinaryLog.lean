import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A quadratic lower bound for binary relative entropy

The elementary bound is proved by differentiating in the second parameter.
It is useful in exact Chernoff estimates for normalized Gaussian coordinates.
-/

noncomputable section
open Real Set

/-- Binary relative entropy dominates twice the squared parameter difference
on the upper tail. Both parameters lie strictly between zero and one. -/
theorem two_mul_sub_sq_le_binary_log {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpq : p ≤ q) (hq1 : q < 1) :
    2 * (q - p) ^ 2 ≤ p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
  let F : ℝ → ℝ := fun x => p * (log p - log x) +
    (1 - p) * (log (1 - p) - log (1 - x)) - 2 * (x - p) ^ 2
  let F' : ℝ → ℝ := fun x => -p / x + (1 - p) / (1 - x) - 4 * (x - p)
  have hd (x : ℝ) (hx : x ∈ Icc p q) : HasDerivAt F (F' x) x := by
    have hx0 : x ≠ 0 := ne_of_gt (hp.trans_le hx.1)
    have hx1 : 1 - x ≠ 0 := ne_of_gt (by linarith [hx.2] : 0 < 1 - x)
    have h := (((hasDerivAt_const x (log p)).sub (hasDerivAt_log hx0)).const_mul p).add
      (((hasDerivAt_const x (log (1 - p))).sub
        (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log hx1)).const_mul (1-p))
    convert h.sub ((((hasDerivAt_id x).sub_const p).pow 2).const_mul 2) using 1
    all_goals first | rfl | (dsimp [F, F']; ring)
  have hc : ContinuousOn F (Icc p q) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm : MonotoneOn F (Icc p q) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p q) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hxc := interior_subset hx
    have hx0 : 0 < x := hp.trans_le hxc.1
    have hx1 : 0 < 1-x := by linarith [hxc.2]
    have he : F' x = (x-p) * (1 - 4*x*(1-x)) / (x*(1-x)) := by
      dsimp [F']
      field_simp
      ring
    rw [he]
    apply div_nonneg
    · apply mul_nonneg (sub_nonneg.mpr hxc.1)
      nlinarith [sq_nonneg (2*x-1)]
    · positivity
  have h := hm (show p ∈ Icc p q from ⟨le_rfl, hpq⟩)
    (show q ∈ Icc p q from ⟨hpq, le_rfl⟩) hpq
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := ne_of_gt (hp.trans_le hpq)
  rw [log_div hp0 hq0, log_div (by linarith : 1-p ≠ 0) (by linarith : 1-q ≠ 0)]
  dsimp [F] at h
  nlinarith
