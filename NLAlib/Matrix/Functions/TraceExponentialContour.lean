import NLAlib.ForMathlib.Analysis.Complex.ExteriorCircleCauchy
import NLAlib.ForMathlib.MeasureTheory.CircleIntegralFubini
import NLAlib.Matrix.Functions.ExpLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exterior-circle identities for the trace-exponential representation

These results verify the atomic and continuous transform terms in Stahl's
candidate representation from explicit exterior holomorphic branches. They do
not construct those branches, prove positivity of the density, or assert the
full positive-measure representation. These are helpers toward atlas item
`trace-exponential-stahl`. Source: Stahl, BMV conjecture, Theorem 2.
-/

noncomputable section

open Complex Set Metric Filter Bornology MeasureTheory
open scoped Topology Matrix.Norms.L2Operator

namespace NLAlib

/-- Stahl's candidate circle density sums the branches whose real slopes lie
below the density parameter. It is complex-valued until branch reflection has
been established; no positivity is built into this definition.
Source: Stahl 2013, Theorem 2; helper for `trace-exponential-stahl`. -/
def traceExponentialCircleDensity {ι : Type*} [Fintype ι]
    (branch : ι → ℂ → ℂ) (a : ι → ℝ) (r s : ℝ) : ℂ :=
  ∑ i, if a i < s then
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch i z + s * z)) else 0

/-- The circle integral defining each density contribution is independent of
its positive radius inside an exterior holomorphy domain. This allows one fixed
candidate density to be used for every real Laplace parameter.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem circleIntegral_exp_add_mul_eq_of_differentiableOn_exterior
    {branch : ℂ → ℂ} {R r u : ℝ} (s : ℝ)
    (hbranch : DifferentiableOn ℂ branch {z | R < ‖z‖})
    (hr : 0 < r) (hu : 0 < u) (hRr : R < r) (hRu : R < u) :
    (∮ z in C(0, r), exp (branch z + s * z)) =
      ∮ z in C(0, u), exp (branch z + s * z) :=
  circleIntegral_eq_of_differentiableOn_exterior
    (Complex.differentiable_exp.comp_differentiableOn
      (hbranch.add (differentiableOn_id.const_mul (s : ℂ)))) hr hu hRr hRu

/-- The finite candidate density is independent of the exterior circle radius.
Its complex value and support cutoffs are preserved pointwise.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem traceExponentialCircleDensity_eq_of_differentiableOn_exterior
    {ι : Type*} [Fintype ι] {branch : ι → ℂ → ℂ} {a : ι → ℝ} {R r u : ℝ}
    (hbranch : ∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖})
    (hr : 0 < r) (hu : 0 < u) (hRr : R < r) (hRu : R < u) (s : ℝ) :
    traceExponentialCircleDensity branch a r s = traceExponentialCircleDensity branch a u s := by
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [circleIntegral_exp_add_mul_eq_of_differentiableOn_exterior s
      (hbranch i) hr hu hRr hRu]
  · rfl

/-- An exterior eigenvalue branch with asymptotic `branch(z) + bz → a` gives the
atomic Cauchy term `exp a` in Stahl's trace-exponential formula. The branch is
only required outside a disk, and the evaluation point lies inside the circle.
Source: Stahl 2013, Theorem 2, exterior Cauchy step.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem two_pi_i_inv_mul_circleIntegral_exp_add_mul_div_sub_eq
    {branch : ℂ → ℂ} {a b t : ℂ} {R r : ℝ}
    (hbranch : DifferentiableOn ℂ branch {z | R < ‖z‖}) (hr : 0 < r) (hRr : R < r)
    (htr : ‖t‖ < r) (hlim : Tendsto (fun z => branch z + b * z) (cobounded ℂ) (𝓝 a)) :
    (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(0, r), exp (branch z + b * z) / (z - t)) = exp a := by
  apply NLAlib.two_pi_i_inv_mul_circleIntegral_div_sub_eq_of_tendsto
    (Complex.differentiable_exp.comp_differentiableOn (hbranch.add (differentiableOn_id.const_mul b)))
    hr hRr htr
  exact Complex.continuous_exp.continuousAt.tendsto.comp hlim

/-- A continuous exterior branch gives an integrable exponentially weighted
circle-density contribution on every compact real interval. This verifies the
integrability needed by the transform step toward `trace-exponential-stahl`. -/
theorem intervalIntegrable_exp_mul_circleIntegral_exp_add_mul
    {branch : ℂ → ℂ} {a b t r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r)
    (hbranch : ContinuousOn branch (sphere 0 r)) :
    IntervalIntegrable (fun s => exp (-(t : ℂ) * s) *
      ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch z + s * z))))
      volume a b := by
  let F : ℝ → ℂ → ℂ := fun s z => exp (-(t : ℂ) * s) * exp (branch z + s * z)
  have hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ sphere 0 r) := by
    have hb : ContinuousOn (fun p : ℝ × ℂ => branch p.2) (Icc a b ×ˢ sphere 0 r) :=
      hbranch.comp continuous_snd.continuousOn (fun _ hp => hp.2)
    apply ContinuousOn.mul
    · fun_prop
    · apply Complex.continuous_exp.comp_continuousOn
      exact hb.add (by fun_prop)
  have heq : (fun s : ℝ => exp (-(t : ℂ) * s) *
      ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch z + s * z)))) =
      (fun s => (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), F s z)) := by
    funext s
    dsimp [F]
    rw [circleIntegral.integral_const_mul]
    ring
  rw [heq]
  exact (intervalIntegrable_circleIntegral_and_integral_circleIntegral_eq hab hr hF).1.const_mul _

/-- The finite candidate circle density, multiplied by a real Laplace weight,
is integrable on any compact real interval. The finite slope cutoffs are
measurable, so their possible jumps create no integrability gap.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem intervalIntegrable_exp_mul_traceExponentialCircleDensity
    {ι : Type*} [Fintype ι] {branch : ι → ℂ → ℂ} {a : ι → ℝ}
    {l u t r : ℝ} (hlu : l ≤ u) (hr : 0 ≤ r)
    (hbranch : ∀ i, ContinuousOn (branch i) (sphere 0 r)) :
    IntervalIntegrable (fun s => exp (-(t : ℂ) * s) *
      traceExponentialCircleDensity branch a r s) volume l u := by
  have hi (i : ι) : IntervalIntegrable (fun s : ℝ => if a i < s then
      exp (-(t : ℂ) * s) * ((2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, r), exp (branch i z + s * z))) else 0) volume l u := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlu]
    have h := intervalIntegrable_exp_mul_circleIntegral_exp_add_mul hlu hr (hbranch i)
      (t := t)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlu] at h
    have hi' : Integrable _ (volume.restrict (Ioc l u)) := h
    have hpoint : ((Ioi (a i)).indicator (fun s : ℝ => exp (-(t : ℂ) * s) *
        ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch i z + s * z))))) =
        (fun s : ℝ => if a i < s then exp (-(t : ℂ) * s) *
          ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch i z + s * z))) else 0) := by
      funext s
      by_cases hs : a i < s <;> simp [Set.indicator, hs]
    rw [← hpoint]
    exact hi'.indicator measurableSet_Ioi
  simp only [traceExponentialCircleDensity, Finset.mul_sum, mul_ite, mul_zero]
  exact (IntervalIntegrable.sum (s := Finset.univ) (fun i _ => hi i)).congr
    (fun s _ => by simp only [Finset.sum_apply])

private theorem integral_ite_lt_eq_integral_lower
    {f : ℝ → ℂ} {l a u : ℝ} (hla : l ≤ a) (hau : a ≤ u) :
    (∫ s in l..u, if a < s then f s else 0) = ∫ s in a..u, f s := by
  change (∫ s in l..u, (Ioi a).indicator f s) = _
  rw [intervalIntegral.integral_of_le (hla.trans hau), intervalIntegral.integral_of_le hau,
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi a ∩ Ioc l u = Ioc a u := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun hs => ⟨hs.1, hs.2.2⟩
    · exact fun hs => ⟨hs.1, hla.trans_lt hs.1, hs.2⟩
  rw [hset]

/-- Integrating the finite density over an interval containing all slopes
equals the sum of its branch integrals from each slope to the upper endpoint.
This turns the branchwise transform identity into one density integral.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem integral_exp_mul_traceExponentialCircleDensity_eq_sum_integral
    {ι : Type*} [Fintype ι] {branch : ι → ℂ → ℂ} {a : ι → ℝ}
    {l u t r : ℝ} (hlu : l ≤ u) (hla : ∀ i, l ≤ a i) (hau : ∀ i, a i ≤ u)
    (hr : 0 ≤ r) (hbranch : ∀ i, ContinuousOn (branch i) (sphere 0 r)) :
    (∫ s in l..u, exp (-(t : ℂ) * s) * traceExponentialCircleDensity branch a r s) =
      ∑ i, ∫ s in a i..u, exp (-(t : ℂ) * s) *
        ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch i z + s * z))) := by
  have hi (i : ι) : IntervalIntegrable (fun s : ℝ => if a i < s then
      exp (-(t : ℂ) * s) * ((2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, r), exp (branch i z + s * z))) else 0) volume l u := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlu]
    have h := intervalIntegrable_exp_mul_circleIntegral_exp_add_mul hlu hr (hbranch i)
      (t := t)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlu] at h
    have hi' : Integrable _ (volume.restrict (Ioc l u)) := h
    have hpoint : ((Ioi (a i)).indicator (fun s : ℝ => exp (-(t : ℂ) * s) *
        ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch i z + s * z))))) =
        (fun s : ℝ => if a i < s then exp (-(t : ℂ) * s) *
          ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch i z + s * z))) else 0) := by
      funext s
      by_cases hs : a i < s <;> simp [Set.indicator, hs]
    rw [← hpoint]
    exact hi'.indicator measurableSet_Ioi
  simp only [traceExponentialCircleDensity, Finset.mul_sum, mul_ite, mul_zero]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_ite_lt_eq_integral_lower (hla i) (hau i)

/-- The Laplace transform of a single circle-density contribution equals a
circle integral of its explicit exponential antiderivative. Joint integrability
and the contour/interval interchange follow from continuity on a compact product.
Source: Stahl 2013, Theorem 2, transform-verification calculation.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem integral_exp_mul_circleIntegral_exp_add_mul
    {branch : ℂ → ℂ} {a b t r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) (htr : |t| < r)
    (hbranch : ContinuousOn branch (sphere 0 r)) :
    (∫ s in a..b, exp (-(t : ℂ) * s) *
      ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch z + s * z)))) =
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r),
      exp (branch z) * (exp ((z - t) * b) - exp ((z - t) * a)) / (z - t)) := by
  let F : ℝ → ℂ → ℂ := fun s z => exp (-(t : ℂ) * s) * exp (branch z + s * z)
  have hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ sphere 0 r) := by
    have hbranch' : ContinuousOn (fun p : ℝ × ℂ => branch p.2) (Icc a b ×ˢ sphere 0 r) :=
      hbranch.comp continuous_snd.continuousOn (fun _ hp => hp.2)
    apply ContinuousOn.mul
    · fun_prop
    · apply Complex.continuous_exp.comp_continuousOn
      exact hbranch'.add (by fun_prop)
  have hswap := integral_circleIntegral_eq_circleIntegral_integral hab hr hF
  have hkernel (z : ℂ) (hz : z ∈ sphere 0 r) :
      (∫ s in a..b, F s z) =
        exp (branch z) * (exp ((z - t) * b) - exp ((z - t) * a)) / (z - t) := by
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    have hne : z - (t : ℂ) ≠ 0 := by
      intro heq
      have : ‖(t : ℂ)‖ = r := by simpa only [sub_eq_zero.mp heq] using hz'
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      exact htr.ne this
    have heq (s : ℝ) : F s z = exp (branch z) * exp ((z - t) * s) := by
      dsimp [F]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hne]
    ring
  calc
    _ = (2 * Real.pi * I : ℂ)⁻¹ *
        (∫ s in a..b, ∮ z in C(0, r), F s z) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [F]
      rw [circleIntegral.integral_const_mul]
      ring
    _ = (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, r), ∫ s in a..b, F s z) := by rw [hswap]
    _ = _ := by
      congr 1
      exact circleIntegral.integral_congr hr hkernel

/-- Each exterior branch contributes its upper-endpoint circle integral minus
its explicit atom to the Laplace transform. This combines the contour
interchange with exterior Cauchy, without any surface positivity hypothesis.
Source: Stahl 2013, Theorem 2, branchwise transform calculation.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem integral_exp_mul_circleIntegral_exp_add_mul_eq_sub_atom
    {branch : ℂ → ℂ} {q : ℂ} {a b t R r : ℝ} (hab : a ≤ b)
    (hr : 0 < r) (hRr : R < r) (htr : |t| < r)
    (hbranch : DifferentiableOn ℂ branch {z | R < ‖z‖})
    (hlim : Tendsto (fun z => branch z + (a : ℂ) * z) (cobounded ℂ) (𝓝 q)) :
    (∫ s in a..b, exp (-(t : ℂ) * s) *
      ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch z + s * z)))) =
    (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(0, r), exp (branch z + (z - t) * b) / (z - t)) -
        exp (q - (t : ℂ) * a) := by
  have hsub : sphere (0 : ℂ) r ⊆ {z | R < ‖z‖} := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    exact hRr.trans_eq hz'.symm
  have hc : ContinuousOn branch (sphere 0 r) := hbranch.continuousOn.mono hsub
  have hne (z : ℂ) (hz : z ∈ sphere 0 r) : z - (t : ℂ) ≠ 0 := by
    intro heq
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    have ht : |t| = r := by simpa [sub_eq_zero.mp heq] using hz'
    exact htr.ne ht
  have hci (s : ℝ) : CircleIntegrable
      (fun z => exp (branch z + (z - t) * s) / (z - t)) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    apply ContinuousOn.div _ (by fun_prop) hne
    apply Complex.continuous_exp.comp_continuousOn
    exact hc.add (by fun_prop)
  have hsplit : (∮ z in C(0, r),
      exp (branch z) * (exp ((z - t) * b) - exp ((z - t) * a)) / (z - t)) =
      (∮ z in C(0, r), exp (branch z + (z - t) * b) / (z - t)) -
      (∮ z in C(0, r), exp (branch z + (z - t) * a) / (z - t)) := by
    rw [← circleIntegral.integral_sub (hci b) (hci a)]
    apply circleIntegral.integral_congr hr.le
    intro z _
    simp only [Complex.exp_add]
    ring
  have htail : (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(0, r), exp (branch z + (z - t) * a) / (z - t)) =
        exp (q - (t : ℂ) * a) := by
    have heq (z : ℂ) : exp (branch z + (z - t) * a) / (z - t) =
        exp (-(t : ℂ) * a) * (exp (branch z + a * z) / (z - t)) := by
      rw [← mul_div_assoc, ← Complex.exp_add]
      congr 2
      ring
    simp_rw [heq]
    rw [circleIntegral.integral_const_mul]
    calc
      _ = exp (-(t : ℂ) * a) * ((2 * Real.pi * I : ℂ)⁻¹ *
          (∮ z in C(0, r), exp (branch z + a * z) / (z - t))) := by ring
      _ = exp (-(t : ℂ) * a) * exp q := by
        rw [two_pi_i_inv_mul_circleIntegral_exp_add_mul_div_sub_eq
          hbranch hr hRr (by simpa using htr) hlim]
      _ = exp (q - (t : ℂ) * a) := by rw [← Complex.exp_add]; congr 1; ring
  rw [integral_exp_mul_circleIntegral_exp_add_mul hab hr.le htr hc, hsplit, mul_sub, htail]

/-- Summing the branchwise transforms produces one trace-type circle integral
minus the explicit finite atomic transform. This is the atom-plus-density
identity before the interior trace Cauchy formula is applied.
Source: Stahl 2013, Theorem 2, transform verification; helper for
`trace-exponential-stahl`, with exterior branches still explicit hypotheses. -/
theorem sum_integral_exp_mul_circleIntegral_exp_add_mul_eq_sub_atoms
    {ι : Type*} [Fintype ι] {branch : ι → ℂ → ℂ} {q : ι → ℂ} {a : ι → ℝ}
    {b t R r : ℝ} (hab : ∀ i, a i ≤ b) (hr : 0 < r) (hRr : R < r) (htr : |t| < r)
    (hbranch : ∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖})
    (hlim : ∀ i, Tendsto (fun z => branch i z + (a i : ℂ) * z)
      (cobounded ℂ) (𝓝 (q i))) :
    (∑ i, ∫ s in a i..b, exp (-(t : ℂ) * s) *
      ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch i z + s * z)))) =
    (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(0, r), (∑ i, exp (branch i z)) * exp ((z - t) * b) / (z - t)) -
        ∑ i, exp (q i - (t : ℂ) * a i) := by
  have hsub : sphere (0 : ℂ) r ⊆ {z | R < ‖z‖} := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    exact hRr.trans_eq hz'.symm
  have hne (z : ℂ) (hz : z ∈ sphere 0 r) : z - (t : ℂ) ≠ 0 := by
    intro heq
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    have ht : |t| = r := by simpa [sub_eq_zero.mp heq] using hz'
    exact htr.ne ht
  have hci (i : ι) : CircleIntegrable
      (fun z => exp (branch i z + (z - t) * b) / (z - t)) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    apply ContinuousOn.div _ (by fun_prop) hne
    apply Complex.continuous_exp.comp_continuousOn
    exact ((hbranch i).continuousOn.mono hsub).add (by fun_prop)
  calc
    _ = ∑ i, ((2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, r), exp (branch i z + (z - t) * b) / (z - t)) -
          exp (q i - (t : ℂ) * a i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_exp_mul_circleIntegral_exp_add_mul_eq_sub_atom
        (hab i) hr hRr htr (hbranch i) (hlim i)
    _ = (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(0, r), ∑ i, exp (branch i z + (z - t) * b) / (z - t)) -
          ∑ i, exp (q i - (t : ℂ) * a i) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        circleIntegral.integral_fun_sum (fun i _ => hci i)]
    _ = _ := by
      congr 2
      apply circleIntegral.integral_congr hr.le
      intro z _
      simp only [Complex.exp_add, Finset.sum_div, Finset.sum_mul]

/-- The atom-plus-density Laplace identity follows from exterior branches with
the stated asymptotics and an interior holomorphic trace function agreeing with
their exponential sum on the contour. Branch existence, trace agreement, and
nonnegativity of the candidate density remain separate mathematical tasks.
Source: Stahl 2013, Theorem 2, transform verification; helper for
`trace-exponential-stahl`. -/
theorem sum_integral_exp_mul_circleIntegral_exp_add_mul_eq_of_trace
    {ι : Type*} [Fintype ι] {branch : ι → ℂ → ℂ} {q : ι → ℂ} {a : ι → ℝ}
    {T : ℂ → ℂ} {b t R r : ℝ} (hab : ∀ i, a i ≤ b)
    (hr : 0 < r) (hRr : R < r) (htr : |t| < r)
    (hbranch : ∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖})
    (hlim : ∀ i, Tendsto (fun z => branch i z + (a i : ℂ) * z)
      (cobounded ℂ) (𝓝 (q i)))
    (hT : DifferentiableOn ℂ T (closedBall 0 r))
    (htrace : ∀ z ∈ sphere 0 r, (∑ i, exp (branch i z)) = T z) :
    (∑ i, ∫ s in a i..b, exp (-(t : ℂ) * s) *
      ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch i z + s * z)))) =
      T t - ∑ i, exp (q i - (t : ℂ) * a i) := by
  rw [sum_integral_exp_mul_circleIntegral_exp_add_mul_eq_sub_atoms
    hab hr hRr htr hbranch hlim]
  congr 1
  let F : ℂ → ℂ := fun z => T z * exp ((z - t) * b)
  have hF : DifferentiableOn ℂ F (closedBall 0 r) :=
    hT.mul (Complex.differentiable_exp.comp_differentiableOn
      ((differentiableOn_id.sub_const (t : ℂ)).mul_const (b : ℂ)))
  have ht : (t : ℂ) ∈ ball 0 r := by simpa [mem_ball, dist_zero_right] using htr
  have hcauchy : (∮ z in C(0, r), F z / (z - t)) =
      (2 * Real.pi * I : ℂ) * T t := by
    simpa [F, div_eq_mul_inv, mul_comm] using hF.circleIntegral_sub_inv_smul ht
  calc
    _ = (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), F z / (z - t)) := by
      congr 1
      apply circleIntegral.integral_congr hr.le
      intro z hz
      dsimp only [F]
      rw [htrace z hz]
    _ = T t := by
      rw [hcauchy, inv_mul_cancel_left₀ (by simp [Real.pi_ne_zero])]

/-- The complex trace of `exp (A - zB)` is entire for arbitrary fixed matrices.
No Hermitian or commutation condition is needed for this analytic statement.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem differentiable_trace_matrixExp_sub_smul
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    Differentiable ℂ (fun z : ℂ => Matrix.trace (matrixExp (A - z • B))) := by
  have hp : Differentiable ℂ (fun z : ℂ => A - z • B) :=
    (differentiable_const A).sub (differentiable_id.smul_const B)
  have he : Differentiable ℂ (fun z : ℂ => matrixExp (A - z • B)) := by
    intro z
    exact (NormedSpace.exp_analytic (𝕂 := ℂ) (A - z • B)).differentiableAt.comp z (hp z)
  exact (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap.differentiable.comp he

/-- Explicit exterior eigenvalue branches give Stahl's atom-plus-density
transform identity for the matrix exponential. The branch existence,
their boundary trace identity, and density positivity are not assumed proved.
The right side uses the complex trace; taking real parts gives `traceExp`.
Source: Stahl 2013, Theorem 2, transform verification; helper toward
`trace-exponential-stahl`.
atlas: trace-exponential-stahl (partial) -/
theorem sum_integral_exp_mul_circleIntegral_exp_add_mul_eq_trace_matrixExp_sub_atoms
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A B : Matrix n n ℂ) {branch : ι → ℂ → ℂ} {q : ι → ℂ} {a : ι → ℝ}
    {b t R r : ℝ} (hab : ∀ i, a i ≤ b) (hr : 0 < r) (hRr : R < r) (htr : |t| < r)
    (hbranch : ∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖})
    (hlim : ∀ i, Tendsto (fun z => branch i z + (a i : ℂ) * z)
      (cobounded ℂ) (𝓝 (q i)))
    (htrace : ∀ z ∈ sphere 0 r,
      (∑ i, exp (branch i z)) = Matrix.trace (matrixExp (A - z • B))) :
    (∑ i, ∫ s in a i..b, exp (-(t : ℂ) * s) *
      ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), exp (branch i z + s * z)))) =
      Matrix.trace (matrixExp (A - (t : ℂ) • B)) - ∑ i, exp (q i - (t : ℂ) * a i) := by
  exact sum_integral_exp_mul_circleIntegral_exp_add_mul_eq_of_trace hab hr hRr htr hbranch hlim
    (differentiable_trace_matrixExp_sub_smul A B).differentiableOn htrace

/-- Stahl's candidate density satisfies the matrix trace-exponential
Laplace identity when the exterior branches, their asymptotics, and their trace
identity are supplied. This proves the transform calculation and integrability,
while branch construction and density positivity remain independent obligations.
Source: Stahl 2013, Theorem 2.
atlas: trace-exponential-stahl (partial) -/
theorem integral_exp_mul_traceExponentialCircleDensity_eq_trace_matrixExp_sub_atoms
    {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (A B : Matrix n n ℂ) {branch : ι → ℂ → ℂ} {q : ι → ℂ} {a : ι → ℝ}
    {l u t R r : ℝ} (hlu : l ≤ u) (hla : ∀ i, l ≤ a i) (hau : ∀ i, a i ≤ u)
    (hr : 0 < r) (hRr : R < r) (htr : |t| < r)
    (hbranch : ∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖})
    (hlim : ∀ i, Tendsto (fun z => branch i z + (a i : ℂ) * z)
      (cobounded ℂ) (𝓝 (q i)))
    (htrace : ∀ z ∈ sphere 0 r,
      (∑ i, exp (branch i z)) = Matrix.trace (matrixExp (A - z • B))) :
    (∫ s in l..u, exp (-(t : ℂ) * s) * traceExponentialCircleDensity branch a r s) =
      Matrix.trace (matrixExp (A - (t : ℂ) • B)) - ∑ i, exp (q i - (t : ℂ) * a i) := by
  have hc (i : ι) : ContinuousOn (branch i) (sphere 0 r) := by
    apply (hbranch i).continuousOn.mono
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    exact hRr.trans_eq hz'.symm
  rw [integral_exp_mul_traceExponentialCircleDensity_eq_sum_integral hlu hla hau hr.le hc]
  exact sum_integral_exp_mul_circleIntegral_exp_add_mul_eq_trace_matrixExp_sub_atoms
    A B hau hr hRr htr hbranch hlim htrace

end NLAlib
