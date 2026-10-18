import NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesUniqueness
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Measure.Support

/-!
# Support exclusion from imaginary Stieltjes bounds

A locally uniform `O(η)` imaginary-part estimate across a real interval
forces the representing positive measure to vanish there. Cauchy
probability regularization proves this without boundary-value hypotheses.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology BoundedContinuousFunction
namespace MeasureTheory

/-- A nonnegative compact test supported where the imaginary Cauchy
transform is uniformly `O(η)` has zero integral under the source measure. -/
theorem integral_eq_zero_of_im_cauchyKernel_le_mul
    (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ →ᵇ ℝ)
    (hfint : Integrable f) (hfnonneg : ∀ x, 0 ≤ f x) (U : Set ℝ)
    (hfzero : ∀ x ∉ U, f x = 0) (C : ℝ)
    (hb : ∀ y ∈ U, ∀ γ : NNReal, γ ≠ 0 →
      (∫ x : ℝ, ((x : ℂ) - ((y : ℂ) + (γ : ℝ) * Complex.I))⁻¹ ∂μ).im ≤ C * γ) :
    ∫ x : ℝ, f x ∂μ = 0 := by
  let γ (n : ℕ) : NNReal := ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hγne (n : ℕ) : γ n ≠ 0 := by
    apply NNReal.coe_ne_zero.mp
    change 1 / ((n : ℝ) + 1) ≠ 0
    positivity
  have hγ : Tendsto (fun n => (γ n : ℝ)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have hle (n : ℕ) :
      (∫ y : ℝ, f y * (∫ x : ℝ, cauchyPDFReal x (γ n) y ∂μ)) ≤
        (Real.pi⁻¹ * C * γ n) * ∫ y : ℝ, f y := by
    have hi := (integrable_boundedContinuousFunction_mul_cauchyPDFReal_prod
      μ f (γ n) (hγne n)).integral_prod_right
    simp_rw [integral_const_mul] at hi
    rw [← integral_const_mul]
    apply integral_mono hi (hfint.const_mul _)
    intro y
    change f y * (∫ x : ℝ, cauchyPDFReal x (γ n) y ∂μ) ≤
      (Real.pi⁻¹ * C * γ n) * f y
    by_cases hy : y ∈ U
    · rw [Complex.integral_cauchyPDFReal_eq_inv_pi_mul_im_integral μ y _ (hγne n)]
      nlinarith [mul_le_mul_of_nonneg_left (hb y hy (γ n) (hγne n))
        (mul_nonneg (hfnonneg y) (le_of_lt (inv_pos.mpr Real.pi_pos)))]
    · simp only [hfzero y hy, zero_mul, mul_zero, le_refl]
  have hlim := tendsto_integral_cauchyRegularization μ f hγne hγ
  have hlimzero : Tendsto (fun n =>
      (Real.pi⁻¹ * C * γ n) * ∫ y : ℝ, f y) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hγ.const_mul (Real.pi⁻¹ * C)).mul_const
      (∫ y : ℝ, f y)
  have hval := le_of_tendsto_of_tendsto hlim hlimzero (Filter.Eventually.of_forall hle)
  exact le_antisymm hval (integral_nonneg hfnonneg)

/-- A locally uniform imaginary-part bound of order height excludes a
real point from the support of its representing measure. -/
theorem notMem_support_of_im_cauchyKernel_le_mul
    (μ : Measure ℝ) [IsFiniteMeasure μ] (x r C : ℝ) (hr : 0 < r)
    (hb : ∀ y ∈ ball x r, ∀ γ : NNReal, γ ≠ 0 →
      (∫ t : ℝ, ((t : ℂ) - ((y : ℂ) + (γ : ℝ) * Complex.I))⁻¹ ∂μ).im ≤ C * γ) :
    x ∉ μ.support := by
  obtain ⟨g, hgx, hgzero, hgcompact, hgrange⟩ :=
    exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := x))
      isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (singleton_subset_iff.mpr (mem_ball_self hr)))
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g g.continuous 1
    (fun y => by rw [Real.norm_of_nonneg (hgrange y).1]; exact (hgrange y).2)
  have hfx : f x = 1 := hgx (mem_singleton x)
  have hfint : Integrable f :=
    g.continuous.integrable_of_hasCompactSupport hgcompact
  have hzero : ∫ y : ℝ, f y ∂μ = 0 :=
    integral_eq_zero_of_im_cauchyKernel_le_mul μ f hfint (fun y => (hgrange y).1)
      (ball x r) (fun y hy => hgzero hy) C hb
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).mono'
    f.continuous.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => by
      change ‖g y‖ ≤ 1
      rw [Real.norm_of_nonneg (hgrange y).1]; exact (hgrange y).2))
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => (hgrange y).1) hfi).mp hzero
  have hnull : μ {y : ℝ | 0 < f y} = 0 := by
    apply measure_mono_null (t := {y : ℝ | f y ≠ 0})
    · intro y hy
      exact ne_of_gt hy
    · change μ {y : ℝ | g y ≠ 0} = 0
      simpa only [Filter.EventuallyEq, ae_iff, Pi.zero_apply] using hae
  apply Measure.notMem_support_iff_exists.mpr
  refine ⟨{y : ℝ | 0 < f y}, ?_, hnull⟩
  exact (isOpen_lt continuous_const f.continuous).mem_nhds
    (show 0 < f x by rw [hfx]; exact zero_lt_one)

/-- Uniform imaginary-part bounds of order height beyond every strictly
larger radius force the real Stieltjes measure to have the stated compact
spectral support. This is the support step in the matrix Dyson formula. -/
theorem support_subset_Icc_of_im_cauchyKernel_le_mul
    (μ : Measure ℝ) [IsFiniteMeasure μ] (κ : ℝ)
    (hb : ∀ a : ℝ, κ < a → ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      (∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ).im ≤ C * z.im) :
    μ.support ⊆ Icc (-κ) κ := by
  intro x hx
  by_contra hnot
  have hout : κ < |x| := by
    apply lt_of_not_ge
    intro hh
    exact hnot ((abs_le.mp hh))
  let a : ℝ := (|x| + κ) / 2
  have hκa : κ < a := by dsimp [a]; linarith
  have hax : a < |x| := by dsimp [a]; linarith
  obtain ⟨C, hC⟩ := hb a hκa
  apply (notMem_support_of_im_cauchyKernel_le_mul μ x (|x| - a) C
    (sub_pos.mpr hax) ?_) hx
  intro y hy γ hγ
  have hdist : |x - y| < |x| - a := by
    simpa only [mem_ball, Real.dist_eq, abs_sub_comm] using hy
  have htri : |x| ≤ |x - y| + |y| := by
    simpa only [sub_add_cancel] using abs_add_le (x - y) y
  have hay : a ≤ |y| := by linarith
  have hγpos : 0 < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, Complex.add_re,
    Complex.mul_re, sub_zero, add_zero] using
    hC ((y : ℂ) + (γ : ℝ) * Complex.I) (by simpa using hγpos) (by simpa using hay)

/-- The compact support conclusion also gives the almost-everywhere
support formulation used by integral representations. -/
theorem ae_mem_Icc_of_im_cauchyKernel_le_mul
    (μ : Measure ℝ) [IsFiniteMeasure μ] (κ : ℝ)
    (hb : ∀ a : ℝ, κ < a → ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      (∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂μ).im ≤ C * z.im) :
    ∀ᵐ x : ℝ ∂μ, x ∈ Icc (-κ) κ := by
  filter_upwards [μ.support_mem_ae] with x hx
  exact support_subset_Icc_of_im_cauchyKernel_le_mul μ κ hb hx

end MeasureTheory
