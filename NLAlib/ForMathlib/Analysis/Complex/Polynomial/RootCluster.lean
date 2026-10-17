import Mathlib.Analysis.Complex.Polynomial.Basic
import NLAlib.ForMathlib.Analysis.Complex.CircleIntegralAnalytic
import NLAlib.ForMathlib.Analysis.Complex.UpperHalfPlaneCircle

/-!
# Contour formulas for polynomial root clusters

Weighted logarithmic derivatives recover sums of roots inside a fixed circle,
with their algebraic multiplicities. These are the local root-cluster identities
used in the planar approach to `trace-exponential-stahl`.
-/

noncomputable section

open Complex Metric Set
open scoped Interval Topology Polynomial
attribute [local instance] Classical.propDecidable

namespace Polynomial

private theorem sub_ne_zero_on_circle {c w : ℂ} {r : ℝ}
    (hw : dist w c ≠ r) {z : ℂ} (hz : z ∈ sphere c r) : z - w ≠ 0 := by
  intro h
  have hzw : z = w := sub_eq_zero.mp h
  exact hw (hzw ▸ mem_sphere.mp hz)

private theorem circleIntegral_div_sub (c w : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hw : dist w c ≠ r) :
    (∮ z in C(c, r), z / (z - w)) =
      if dist w c < r then (2 * Real.pi * I) * w else 0 := by
  by_cases hinside : dist w c < r
  · rw [if_pos hinside]
    simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm, id_eq] using
      (differentiableOn_id : DifferentiableOn ℂ (fun z : ℂ => z)
        (closedBall c r)).circleIntegral_sub_inv_smul (mem_ball.mpr hinside)
  · rw [if_neg hinside]
    have houtside : r < dist w c := lt_of_le_of_ne (le_of_not_gt hinside) hw.symm
    have hd : DifferentiableOn ℂ (fun z : ℂ => z / (z - w)) (closedBall c r) := by
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_id.div (differentiableAt_id.sub_const w)
      intro h
      have : z = w := sub_eq_zero.mp h
      subst z
      exact (not_le_of_gt houtside) (mem_closedBall.mp hz)
    exact (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr

private theorem circleIntegrable_div_sub (c w : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hw : dist w c ≠ r) : CircleIntegrable (fun z : ℂ => z / (z - w)) c r := by
  exact (continuousOn_id.div (continuousOn_id.sub continuousOn_const)
    (fun _ hz => sub_ne_zero_on_circle hw hz)).circleIntegrable hr

private theorem circleIntegrable_multiset_div_sub (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (m : Multiset ℂ) (h : ∀ w ∈ m, dist w c ≠ r) :
    CircleIntegrable (fun z : ℂ => (m.map (fun w => z / (z - w))).sum) c r := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons w m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (circleIntegrable_div_sub c w hr (h w (by simp))).add
      (ih (fun v hv => h v (Multiset.mem_cons_of_mem hv)))

private theorem circleIntegral_multiset_sum (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (m : Multiset ℂ) (h : ∀ w ∈ m, dist w c ≠ r) :
    (∮ z in C(c, r), (m.map (fun w => z / (z - w))).sum) =
      (m.map (fun w => if dist w c < r then (2 * Real.pi * I) * w else 0)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | @cons w m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have hm : ∀ v ∈ m, dist v c ≠ r := fun v hv => h v (Multiset.mem_cons_of_mem hv)
    rw [circleIntegral.integral_add (circleIntegrable_div_sub c w hr (h w (by simp))) ?_,
      circleIntegral_div_sub c w hr (h w (by simp)), ih hm]
    exact circleIntegrable_multiset_div_sub c hr m hm

/-- Integrating a polynomial's weighted logarithmic derivative around a root-free circle
gives the sum of its enclosed roots, retaining algebraic multiplicities. The polynomial
need not be squarefree; roots within the selected cluster may collide. -/
theorem circleIntegral_mul_derivative_div_eq_sum_roots (p : ℂ[X]) (c : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hp : ∀ z ∈ sphere c r, p.eval z ≠ 0) :
    (∮ z in C(c, r), z * (p.derivative.eval z / p.eval z)) =
      (p.roots.map
        (fun w => if dist w c < r then (2 * Real.pi * I) * w else 0)).sum := by
  rw [circleIntegral.integral_congr hr (fun z hz => ?_)]
  · exact circleIntegral_multiset_sum c hr p.roots (fun w hw => by
      intro heq
      exact hp w (mem_sphere.mpr heq) ((mem_roots (by
        intro hzero
        simp [hzero] at hw)).mp hw))
  · rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero (hp z hz),
      ← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro w _
    simp [div_eq_mul_inv]

/-- The normalized weighted logarithmic derivative gives the enclosed root sum,
with algebraic multiplicities. -/
theorem two_pi_i_inv_mul_circleIntegral_mul_derivative_div_eq_sum_roots
    (p : ℂ[X]) (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hp : ∀ z ∈ sphere c r, p.eval z ≠ 0) :
    (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(c, r), z * (p.derivative.eval z / p.eval z)) =
      (p.roots.map (fun w => if dist w c < r then w else 0)).sum := by
  rw [circleIntegral_mul_derivative_div_eq_sum_roots p c hr hp]
  have heq : (p.roots.map
      (fun w => if dist w c < r then (2 * Real.pi * I) * w else 0)).sum =
      (2 * Real.pi * I : ℂ) *
        (p.roots.map (fun w => if dist w c < r then w else 0)).sum := by
    rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro w _
    split_ifs <;> simp
  rw [heq, ← mul_assoc, inv_mul_cancel₀, one_mul]
  simp [Real.pi_ne_zero]

private def circleEval (c : ℂ) (r : ℝ) (p : ℂ[X]) : C(sphere c r, ℂ) :=
  ⟨fun z => p.eval z, p.continuous.comp continuous_subtype_val⟩

private theorem circleEval_sum_smul {ι : Type*} [Fintype ι]
    (c : ℂ) (r : ℝ) (a : ι → ℂ) (q : ι → ℂ[X]) :
    circleEval c r (∑ i, a i • q i) = ∑ i, a i • circleEval c r (q i) := by
  ext z
  simp [circleEval, eval_finsetSum]

/-- For a finite family of fixed polynomials with analytic scalar coefficients,
the sum of roots inside any root-free fixed circle depends analytically on the
parameter. No simplicity or distinctness of roots inside the circle is required.
This is the separated-cluster holomorphy step in the planar route to Stahl's theorem.

atlas: trace-exponential-stahl (partial) -/
theorem analyticAt_sum_roots_in_circle {ι : Type*} [Fintype ι]
    (q : ι → ℂ[X]) (a : ι → ℂ → ℂ) {u c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i, AnalyticAt ℂ (a i) u)
    (hzero : ∀ z ∈ sphere c r, (∑ i, a i u • q i).eval z ≠ 0) :
    AnalyticAt ℂ (fun v => ((∑ i, a i v • q i).roots.map
      (fun w => if dist w c < r then w else 0)).sum) u := by
  let P : ℂ → ℂ[X] := fun v => ∑ i, a i v • q i
  let F : ℂ → C(sphere c r, ℂ) := fun v => circleEval c r (P v)
  let Z : C(sphere c r, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  let G : ℂ → C(sphere c r, ℂ) := fun v => Z * circleEval c r (P v).derivative
  have hF : AnalyticAt ℂ F u := by
    simp only [F, P, circleEval_sum_smul]
    exact Finset.univ.analyticAt_fun_sum fun i _ => (ha i).smul analyticAt_const
  have hG : AnalyticAt ℂ G u := by
    simp only [G, P, derivative_sum, derivative_smul, circleEval_sum_smul]
    exact analyticAt_const.mul
      (Finset.univ.analyticAt_fun_sum fun i _ => (ha i).smul analyticAt_const)
  have hz : ∀ z, F u z ≠ 0 := fun z => hzero z z.property
  have hA := (analyticAt_const (v := (2 * Real.pi * I : ℂ)⁻¹)).mul
    (circleIntegral.analyticAt_integral_div hr hF hG hz)
  apply hA.congr
  have hunit : IsUnit (F u) := (F u).isUnit_iff_forall_ne_zero.mpr hz
  have hevent : ∀ᶠ v in 𝓝 u, IsUnit (F v) :=
    hF.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
  filter_upwards [hevent] with v hv
  have hnonzero : ∀ z ∈ sphere c r, (P v).eval z ≠ 0 :=
    fun z hz => ((F v).isUnit_iff_forall_ne_zero.mp hv) ⟨z, hz⟩
  have heq : (∮ z in C(c, r),
      if hz : z ∈ sphere c r then G v ⟨z, hz⟩ / F v ⟨z, hz⟩ else 0) =
      ∮ z in C(c, r), z * ((P v).derivative.eval z / (P v).eval z) := by
    apply circleIntegral.integral_congr hr
    intro z hz
    simp only [dif_pos hz, G, F, Z, circleEval, ContinuousMap.mul_apply,
      ContinuousMap.coe_mk]
    ring
  simp only [Pi.mul_apply]
  rw [heq]
  exact two_pi_i_inv_mul_circleIntegral_mul_derivative_div_eq_sum_roots (P v) c hr hnonzero

private theorem sum_map_ite_eq_sum_filter (m : Multiset ℂ) (p : ℂ → Prop)
    [DecidablePred p] : (m.map (fun z => if p z then z else 0)).sum = (m.filter p).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons z m ih =>
    by_cases hz : p z <;> simp [hz, ih]

/-- An upper hemicontinuous polynomial root family avoiding the real axis has an
analytic sum of upper-half-plane roots when its coefficients are analytic. Algebraic
multiplicities are retained, and collisions within either half-plane are allowed.
The root-continuity assumption is available for characteristic polynomials from
upper hemicontinuity of the spectrum in a Banach algebra.

atlas: trace-exponential-stahl (partial) -/
theorem analyticAt_sum_filter_roots_upper_of_upperHemicontinuous
    {ι : Type*} [Fintype ι] (q : ι → ℂ[X]) (a : ι → ℂ → ℂ) {u : ℂ}
    (ha : ∀ i, AnalyticAt ℂ (a i) u) (hp : (∑ i, a i u • q i) ≠ 0)
    (hroots : UpperHemicontinuousAt
      (fun v => {z | z ∈ (∑ i, a i v • q i).roots}) u)
    (hreal : ∀ z ∈ (∑ i, a i u • q i).roots, z.im ≠ 0) :
    AnalyticAt ℂ (fun v => ((∑ i, a i v • q i).roots.filter
      (fun z => 0 < z.im)).sum) u := by
  obtain ⟨r, hr, hselect⟩ := Complex.exists_tangent_circle_eventually_mem_iff_im_pos
    hroots (Multiset.finite_toSet _) hreal
  have hbase := hselect.self_of_nhds
  have hzero : ∀ z ∈ sphere ((r : ℂ) * I) r,
      (∑ i, a i u • q i).eval z ≠ 0 := by
    intro z hz heval
    have hmem : z ∈ (∑ i, a i u • q i).roots := (mem_roots hp).mpr heval
    exact (hbase z hmem).2 (mem_sphere.mp hz)
  apply (analyticAt_sum_roots_in_circle q a hr.le ha hzero).congr
  filter_upwards [hselect] with v hv
  rw [← sum_map_ite_eq_sum_filter]
  congr 1
  apply Multiset.map_congr rfl
  intro z hz
  simp only [(hv z hz).1]

/-- The sum of the roots strictly in the upper half-plane has nonnegative
imaginary part, with algebraic multiplicities retained. -/
theorem im_sum_filter_roots_upper_nonneg (p : ℂ[X]) :
    0 ≤ ((p.roots.filter (fun z => 0 < z.im)).sum).im := by
  change 0 ≤ Complex.imAddGroupHom ((p.roots.filter (fun z => 0 < z.im)).sum)
  rw [map_multiset_sum]
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
  exact (Multiset.mem_filter.mp hz).2.le

end Polynomial
