import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz invariance under real reflection and translation

This general distance identity is used in the sharp Jackson integration by parts.
-/

noncomputable section

namespace NLAlib

/-- Reflection followed by translation preserves the actual Lipschitz constant.
Source: real distance invariance; helper for operator rederivations `rt:periodic-jackson`
and atlas `jackson-lipschitz`. Relocated unchanged from `Polynomial/JacksonPeriodic`. -/
theorem lipschitzWith_comp_const_sub {g : ℝ → ℝ} {L : NNReal} (hg : LipschitzWith L g) (x : ℝ) :
    LipschitzWith L (fun t : ℝ => g (x - t)) := by
  have hlin : LipschitzWith 1 (fun t : ℝ => x - t) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    have heq : (x - a) - (x - b) = -(a - b) := by ring
    rw [heq, abs_neg]
  simpa only [mul_one, Function.comp_def] using hg.comp hlin

end NLAlib
