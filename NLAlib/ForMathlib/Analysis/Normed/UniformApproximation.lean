import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Descent directions for uniform approximation

A continuous perturbation agreeing with the error's sign on every extremal point strictly
reduces its supremum norm after multiplication by a sufficiently small positive scalar.
-/

noncomputable section

open scoped Topology

namespace NLAlib

/-- A direction with the correct sign at every extremal point decreases the uniform norm
for some positive step. Source: Cheney (1966), Chapter 3, the perturbation argument for
the alternation theorem; operator rederivations, `polybest:improvement`.
The proof uses compactness to make the pointwise strict squared-error inequalities uniform. -/
theorem exists_pos_norm_sub_smul_lt_of_extremal_sign {K : Type*}
    [TopologicalSpace K] [CompactSpace K] (e h : C(K, ℝ)) (hE : 0 < ‖e‖)
    (hsign : ∀ x, |e x| = ‖e‖ → 0 < e x * h x) :
    ∃ t : ℝ, 0 < t ∧ ‖e - t • h‖ < ‖e‖ := by
  have hlocal : ∀ x : K, ∀ᶠ z : ℝ × K in 𝓝 (0, x),
      0 < z.1 → |e z.2 - z.1 * h z.2| < ‖e‖ := by
    intro x
    by_cases hx : |e x| = ‖e‖
    · have hneg : -2 * e x * h x < 0 := by nlinarith [hsign x hx]
      have hc : Continuous (fun z : ℝ × K => -2 * e z.2 * h z.2 + z.1 * (h z.2) ^ 2) :=
        by fun_prop
      have hev : ∀ᶠ z : ℝ × K in 𝓝 (0, x),
          -2 * e z.2 * h z.2 + z.1 * (h z.2) ^ 2 < 0 :=
        hc.continuousAt.eventually (gt_mem_nhds (by simpa using hneg))
      filter_upwards [hev] with z hz
      intro ht
      have hbound : |e z.2| ≤ ‖e‖ := e.norm_coe_le_norm z.2
      have hsq : (e z.2) ^ 2 ≤ ‖e‖ ^ 2 := by
        nlinarith [sq_abs (e z.2), abs_nonneg (e z.2)]
      have hmul := mul_neg_of_pos_of_neg ht hz
      apply (abs_lt).mpr
      constructor <;> nlinarith [sq_nonneg (e z.2 - z.1 * h z.2 + ‖e‖),
        sq_nonneg (e z.2 - z.1 * h z.2 - ‖e‖)]
    · have hxlt : |e x| < ‖e‖ := lt_of_le_of_ne (e.norm_coe_le_norm x) hx
      have hc : Continuous (fun z : ℝ × K => |e z.2 - z.1 * h z.2|) := by fun_prop
      have hev : ∀ᶠ z : ℝ × K in 𝓝 (0, x), |e z.2 - z.1 * h z.2| < ‖e‖ :=
        hc.continuousAt.eventually (gt_mem_nhds (by simpa using hxlt))
      exact hev.mono fun z hz _ => hz
  have huniform : ∀ᶠ t : ℝ in 𝓝 0, ∀ x : K,
      0 < t → |e x - t * h x| < ‖e‖ :=
    isCompact_univ.eventually_forall_of_forall_eventually (fun x _ => hlocal x) |>.mono
      (fun _ ht x => ht x (Set.mem_univ x))
  obtain ⟨δ, hδ, hstep⟩ := Metric.eventually_nhds_iff.mp huniform
  refine ⟨δ / 2, by positivity, ?_⟩
  have hnear : dist (δ / 2) (0 : ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  apply (ContinuousMap.norm_lt_iff _ hE).mpr
  intro x
  simpa [Real.norm_eq_abs] using hstep hnear x (by positivity : 0 < δ / 2)

end NLAlib
