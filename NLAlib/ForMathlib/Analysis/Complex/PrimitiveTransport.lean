import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import NLAlib.ForMathlib.Topology.PathSubdivision
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! # Local primitive increments along continuous paths

Primitive differences along a continuous path are independent of the choice
of local primitive whenever that path lies in both open primitive charts.
Finite sums of these increments are invariant under changes of charts on the
same subdivision and under refinement inside a single primitive chart. These
are prerequisites for constructing homotopy-invariant continuous-path
transport; no global Cauchy or Jordan-curve conclusion is asserted here.

Ported from the local deferred Jordan-contour development of 2026-10-14;
the imports are restricted to the generic calculus used by these proofs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset MeasureTheory Metric
open scoped unitInterval
namespace Complex

/-- Two complex primitives of the same function have equal increments along
any continuous path contained in both of their open domains. The path requires
no differentiability. The domains' intersection need not be connected. -/
theorem sub_eq_sub_of_hasDerivAt_of_path {a b : ℂ} (γ : Path a b)
    {U V : Set ℂ} {G H g : ℂ → ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z)
    (hH : ∀ z ∈ V, HasDerivAt H (g z) z)
    (hγU : ∀ t, γ t ∈ U) (hγV : ∀ t, γ t ∈ V) :
    G b - G a = H b - H a := by
  have hd (z : ℂ) (hz : z ∈ U ∩ V) : HasDerivAt (fun z => G z - H z) 0 z := by
    simpa only [sub_self] using (hG z hz.1).fun_sub (hH z hz.2)
  have hlocal : IsLocallyConstant (fun t : unitInterval => G (γ t) - H (γ t)) := by
    apply IsLocallyConstant.iff_isOpen_fiber.mpr
    intro w
    have ho := (hU.inter hV).isOpen_inter_preimage_of_deriv_eq_zero
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z hz).deriv) {w}
    have heq : (fun t : unitInterval => G (γ t) - H (γ t)) ⁻¹' {w} =
        γ ⁻¹' ((U ∩ V) ∩ (fun z => G z - H z) ⁻¹' {w}) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
      simp only [hγU t, hγV t, true_and]
    rw [heq]
    exact γ.continuous.isOpen_preimage _ ho
  have h := hlocal.apply_eq_of_preconnectedSpace 1 0
  simp only [γ.target, γ.source] at h
  linear_combination h

/-- The preceding chart independence applied to any closed parameter interval
of a continuous parameterization. It is valid for repeated subdivision points. -/
theorem sub_eq_sub_of_hasDerivAt_of_continuous
    {γ : ℝ → ℂ} (hγ : Continuous γ) {u v : ℝ} (huv : u ≤ v)
    {U V : Set ℂ} {G H g : ℂ → ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z)
    (hH : ∀ z ∈ V, HasDerivAt H (g z) z)
    (hγU : ∀ t ∈ Icc u v, γ t ∈ U) (hγV : ∀ t ∈ Icc u v, γ t ∈ V) :
    G (γ v) - G (γ u) = H (γ v) - H (γ u) := by
  apply sub_eq_sub_of_hasDerivAt_of_path ((Path.segment u v).map hγ) hU hV hG hH
  · intro t
    apply hγU
    exact (convex_Icc u v).lineMap_mem ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ t.property
  · intro t
    apply hγV
    exact (convex_Icc u v).lineMap_mem ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ t.property

/-- The sum of local primitive increments on a finite parameter subdivision.
The accompanying theorems give its chart-choice and refinement invariance
under the actual primitive and path-containment hypotheses. -/
def primitiveSubdivisionTransport (γ : ℝ → ℂ) (p : ℕ → ℝ)
    (G : ℕ → ℂ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ range n, (G i (γ (p (i + 1))) - G i (γ (p i)))

/-- On a fixed finite subdivision, the transport sum does not depend on the
choice of primitive or chart. Both chart families are required to contain the
actual continuous path on their respective subdivision intervals. -/
theorem primitiveSubdivisionTransport_eq_of_hasDerivAt
    {γ : ℝ → ℂ} (hγ : Continuous γ) {p : ℕ → ℝ} {n : ℕ}
    {G H : ℕ → ℂ → ℂ} {U V : ℕ → Set ℂ} {g : ℂ → ℂ}
    (hp : ∀ i < n, p i ≤ p (i + 1))
    (hU : ∀ i < n, IsOpen (U i)) (hV : ∀ i < n, IsOpen (V i))
    (hG : ∀ i < n, ∀ z ∈ U i, HasDerivAt (G i) (g z) z)
    (hH : ∀ i < n, ∀ z ∈ V i, HasDerivAt (H i) (g z) z)
    (hγU : ∀ i < n, ∀ t ∈ Icc (p i) (p (i + 1)), γ t ∈ U i)
    (hγV : ∀ i < n, ∀ t ∈ Icc (p i) (p (i + 1)), γ t ∈ V i) :
    primitiveSubdivisionTransport γ p G n = primitiveSubdivisionTransport γ p H n := by
  unfold primitiveSubdivisionTransport
  apply sum_congr rfl
  intro i hi
  have hin : i < n := mem_range.mp hi
  exact sub_eq_sub_of_hasDerivAt_of_continuous hγ (hp i hin)
    (hU i hin) (hV i hin) (hG i hin) (hH i hin) (hγU i hin) (hγV i hin)

/-- Refining a path portion lying in one primitive chart does not change its
transport, even when each refined interval uses its own primitive chart. The
finite increments telescope after genuine chart independence is applied. -/
theorem primitiveSubdivisionTransport_eq_sub_of_hasDerivAt
    {γ : ℝ → ℂ} (hγ : Continuous γ) {p : ℕ → ℝ} {n : ℕ}
    {G : ℂ → ℂ} {H : ℕ → ℂ → ℂ} {U : Set ℂ} {V : ℕ → Set ℂ} {g : ℂ → ℂ}
    (hp : ∀ i < n, p i ≤ p (i + 1)) (hU : IsOpen U)
    (hV : ∀ i < n, IsOpen (V i))
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z)
    (hH : ∀ i < n, ∀ z ∈ V i, HasDerivAt (H i) (g z) z)
    (hγU : ∀ i < n, ∀ t ∈ Icc (p i) (p (i + 1)), γ t ∈ U)
    (hγV : ∀ i < n, ∀ t ∈ Icc (p i) (p (i + 1)), γ t ∈ V i) :
    primitiveSubdivisionTransport γ p H n = G (γ (p n)) - G (γ (p 0)) := by
  rw [primitiveSubdivisionTransport_eq_of_hasDerivAt hγ hp hV
    (fun _ _ => hU) hH (fun _ _ => hG) hγV hγU]
  simpa only [primitiveSubdivisionTransport] using sum_range_sub (fun i => G (γ (p i))) n

/-- The actual finite local-primitive transport equals Mathlib's native curve
integral on a C¹ path. The integrability and fundamental-theorem hypotheses
are derived interval by interval from the primitive charts and path regularity. -/
theorem primitiveSubdivisionTransport_eq_curveIntegral_of_hasDerivAt
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend I)
    {p : ℕ → ℝ} {n : ℕ} {G : ℕ → ℂ → ℂ} {U : ℕ → Set ℂ} {g : ℂ → ℂ}
    (hp : ∀ i < n, p i ≤ p (i + 1)) (hp0 : p 0 = 0) (hpn : p n = 1)
    (hpI : ∀ i ≤ n, p i ∈ I)
    (hG : ∀ i < n, ∀ z ∈ U i, HasDerivAt (G i) (g z) z)
    (hg : ∀ i < n, ContinuousOn g (U i))
    (hγU : ∀ i < n, ∀ t ∈ Icc (p i) (p (i + 1)), γ.extend t ∈ U i) :
    primitiveSubdivisionTransport γ.extend p G n =
      curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ := by
  let F := curveIntegralFun (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ
  have hcell (i : ℕ) (hi : i < n) :
      IntervalIntegrable F volume (p i) (p (i + 1)) ∧
      (∫ t in (p i)..(p (i + 1)), F t) =
        G i (γ.extend (p (i + 1))) - G i (γ.extend (p i)) := by
    have hpi := hpI i hi.le
    have hpnext := hpI (i + 1) hi
    have hsubset : Icc (p i) (p (i + 1)) ⊆ I :=
      fun t ht => ⟨hpi.1.trans ht.1, ht.2.trans hpnext.2⟩
    have hc : ContinuousOn (fun t => g (γ.extend t)) (Icc (p i) (p (i + 1))) :=
      (hg i hi).comp γ.continuous_extend.continuousOn (hγU i hi)
    have hd : ContinuousOn (fun t => derivWithin γ.extend I t)
        (Icc (p i) (p (i + 1))) :=
      (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).mono hsubset
    have hFeq : F = fun t => g (γ.extend t) * derivWithin γ.extend I t := by
      funext t
      simp only [F, curveIntegralFun_def, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
    have hF : ContinuousOn F (Icc (p i) (p (i + 1))) := by
      rw [hFeq]
      exact hc.fun_mul hd
    have hint : IntervalIntegrable F volume (p i) (p (i + 1)) :=
      hF.intervalIntegrable_of_Icc (hp i hi)
    refine ⟨hint, ?_⟩
    have hcontG : ContinuousOn (G i) (U i) :=
      fun z hz => (hG i hi z hz).continuousAt.continuousWithinAt
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (hp i hi)
      (hcontG.comp γ.continuous_extend.continuousOn (hγU i hi)) _ hint
    intro r hr
    have hrI : r ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt hpi.1 hr.1, lt_of_lt_of_le hr.2 hpnext.2⟩
    have hnhds : I ∈ nhds r := Icc_mem_nhds hrI.1 hrI.2
    have hderγ := (hγ.differentiableOn (by norm_num) r
      (Ioo_subset_Icc_self hrI)).differentiableAt hnhds
    have hDerG := hG i hi (γ.extend r) (hγU i hi r (Ioo_subset_Icc_self hr))
    have hdcomp := (hDerG.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r hderγ.hasDerivAt
    simpa [F, curveIntegralFun_def, derivWithin_of_mem_nhds hnhds,
      smul_eq_mul, mul_comm] using hdcomp
  unfold primitiveSubdivisionTransport
  calc
    (∑ i ∈ range n, (G i (γ.extend (p (i + 1))) - G i (γ.extend (p i)))) =
        ∑ i ∈ range n, ∫ t in (p i)..(p (i + 1)), F t := by
      apply sum_congr rfl
      intro i hi
      exact (hcell i (mem_range.mp hi)).2.symm
    _ = ∫ t in (0 : ℝ)..1, F t := by
      simpa only [hp0, hpn] using
        intervalIntegral.sum_integral_adjacent_intervals (fun i hi => (hcell i hi).1)
    _ = curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ :=
      (curveIntegral_def _ γ).symm

/-- Every continuous path inside an open holomorphy domain admits a finite
uniform subdivision into actual open primitive charts. Both the subdivision
and the primitive functions are derived; a scalar Cauchy formula is not assumed. -/
theorem exists_primitive_subdivision_of_differentiableOn
    {a b : ℂ} (γ : Path a b) {Ω : Set ℂ} {g : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hγΩ : ∀ t, γ t ∈ Ω) :
    ∃ n : ℕ, 0 < n ∧ ∃ U : ℕ → Set ℂ, ∃ G : ℕ → ℂ → ℂ,
      ∀ i < n, IsOpen (U i) ∧ (∀ z ∈ U i, HasDerivAt (G i) (g z) z) ∧
        ContinuousOn g (U i) ∧
        (∀ t ∈ Icc ((i : ℝ) / n) ((i + 1 : ℝ) / n), γ.extend t ∈ U i) := by
  classical
  have hrad : ∀ z : Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball (z : ℂ) r ⊆ Ω :=
    fun z => Metric.mem_nhds_iff.mp (hΩ.mem_nhds z.property)
  choose r hr hball using hrad
  let B : Ω → Set ℂ := fun z => Metric.ball (z : ℂ) (r z)
  have hprimitive : ∀ z : Ω, ∃ G : ℂ → ℂ, ∀ w ∈ B z, HasDerivAt G (g w) w := by
    intro z
    obtain ⟨G, hG⟩ := (convex_ball (z : ℂ) (r z)).exists_forall_hasDerivWithinAt
      (hg.mono (hball z))
    exact ⟨G, fun w hw => (hG w hw).hasDerivAt (isOpen_ball.mem_nhds hw)⟩
  choose G hG using hprimitive
  have hγext : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ Ω := by
    intro t ht
    rw [γ.extend_apply ht]
    exact hγΩ ⟨t, ht⟩
  have hcover : γ.extend '' Icc (0 : ℝ) 1 ⊆ ⋃ z : Ω, B z := by
    rintro z ⟨t, ht, rfl⟩
    apply mem_iUnion.mpr
    exact ⟨⟨γ.extend t, hγext t ht⟩, mem_ball_self (hr _)⟩
  obtain ⟨n, hn, hmesh⟩ := exists_uniform_subdivision_subordinate_open_cover γ.extend
    γ.continuous_extend B (fun _ => isOpen_ball) hcover
  choose J hJ using hmesh
  let K : ℕ → Ω := fun i => if hi : i < n then J i hi else J 0 hn
  refine ⟨n, hn, B ∘ K, G ∘ K, ?_⟩
  intro i hi
  have hKi : K i = J i hi := dif_pos hi
  refine ⟨isOpen_ball, hG (K i), hg.continuousOn.mono (hball (K i)), ?_⟩
  simpa only [Function.comp_apply, hKi] using hJ i hi

end Complex
