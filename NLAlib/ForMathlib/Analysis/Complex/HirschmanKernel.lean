import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The exact Stein--Hirschman strip densities

The displayed densities are kept explicit. Antiderivatives give their actual
Lebesgue normalization; no unspecified harmonic measure is substituted.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, equations (30), (32).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Real

/-- The explicit Stein--Hirschman probability density for `0 < r < 1`. -/
def hirschmanDensity (r t : ℝ) : ℝ :=
  sin (π * r) / (2 * r * (cosh (π * t) + cos (π * r)))

/-- Its explicit limiting density at the zero interpolation parameter. -/
def hirschmanDensityZero (t : ℝ) : ℝ := π / (2 * (cosh (π * t) + 1))

/-- An explicit primitive of the limiting strip density. -/
def hirschmanPrimitiveZero (t : ℝ) : ℝ := (1 + exp (-(π * t)))⁻¹

theorem hirschmanDensityZero_pos (t : ℝ) : 0 < hirschmanDensityZero t := by
  exact div_pos pi_pos (mul_pos (by norm_num) (by linarith [cosh_pos (π * t)]))

@[simp] theorem hirschmanDensityZero_neg (t : ℝ) :
    hirschmanDensityZero (-t) = hirschmanDensityZero t := by
  simp [hirschmanDensityZero]

/-- The logistic primitive differentiates to precisely the displayed zero-parameter kernel. -/
theorem hasDerivAt_hirschmanPrimitiveZero (t : ℝ) :
    HasDerivAt hirschmanPrimitiveZero (hirschmanDensityZero t) t := by
  have hden : 1 + exp (-(π * t)) ≠ 0 := by positivity
  have h := (((hasDerivAt_id t).const_mul π).neg.exp.const_add 1).inv hden
  change HasDerivAt (fun x : ℝ => (1 + exp (-(π * x)))⁻¹)
    (-(exp (-(π * t)) * -(π * 1)) / (1 + exp (-(π * t))) ^ 2) t at h
  have h' : HasDerivAt (fun x : ℝ => (1 + exp (-(π * x)))⁻¹)
      (π * exp (-(π * t)) / (1 + exp (-(π * t))) ^ 2) t := by
    convert h using 1
    ring
  apply h'.congr_deriv
  dsimp [hirschmanDensityZero]
  rw [cosh_eq, exp_neg]
  have he := exp_pos (π * t)
  field_simp
  ring

theorem tendsto_hirschmanPrimitiveZero_atTop :
    Tendsto hirschmanPrimitiveZero atTop (𝓝 1) := by
  have he : Tendsto (fun t : ℝ => exp (-(π * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop pi_pos)
  change Tendsto (fun t : ℝ => (1 + exp (-(π * t)))⁻¹) atTop (𝓝 1)
  simpa only [add_zero, inv_one] using
    (tendsto_const_nhds.add he).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)

theorem tendsto_hirschmanPrimitiveZero_atBot :
    Tendsto hirschmanPrimitiveZero atBot (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_const_nhds.add_atTop
    (tendsto_exp_atTop.comp (tendsto_neg_atBot_atTop.comp (tendsto_id.const_mul_atBot pi_pos)))

private theorem integrable_of_even_nonneg_primitive {f F : ℝ → ℝ} {l : ℝ}
    (hf : Function.Even f) (hnonneg : ∀ t, 0 ≤ f t)
    (hF : ∀ t, HasDerivAt F (f t) t) (htop : Tendsto F atTop (𝓝 l)) : Integrable f := by
  have hpos : IntegrableOn f (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hF t) (fun t _ => hnonneg t) htop
  have hci : IntegrableOn f (Ici (0 : ℝ)) := Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hneg : IntegrableOn f (Iic (0 : ℝ)) := by
    have hci' : IntegrableOn f (Ici (-(0 : ℝ))) := by simpa only [neg_zero] using hci
    have h : IntegrableOn (fun t => f (-t)) (Iic (0 : ℝ)) := hci'.comp_neg_Iic
    have heq : (fun t => f (-t)) = f := funext hf
    rwa [heq] at h
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact integrableOn_union.mpr ⟨hneg, hpos⟩

/-- The explicit zero-parameter kernel is genuinely Lebesgue integrable. -/
theorem integrable_hirschmanDensityZero : Integrable hirschmanDensityZero :=
  integrable_of_even_nonneg_primitive hirschmanDensityZero_neg
    (fun t => (hirschmanDensityZero_pos t).le) hasDerivAt_hirschmanPrimitiveZero
    tendsto_hirschmanPrimitiveZero_atTop

/-- Its actual integral is one. -/
theorem integral_hirschmanDensityZero : (∫ t, hirschmanDensityZero t) = 1 := by
  simpa using integral_of_hasDerivAt_of_tendsto hasDerivAt_hirschmanPrimitiveZero
    integrable_hirschmanDensityZero tendsto_hirschmanPrimitiveZero_atBot
    tendsto_hirschmanPrimitiveZero_atTop

/-- The denominator in the exact interior strip density stays positive. -/
theorem hirschmanDenominator_pos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < cosh (π * t) + cos (π * r) := by
  have hangle : π * r < π := by nlinarith [pi_pos, hr.2]
  have hc := cos_lt_cos_of_nonneg_of_le_pi (mul_pos pi_pos hr.1).le le_rfl hangle
  rw [cos_pi] at hc
  have hch : 1 ≤ cosh (π * t) := by
    nlinarith [cosh_sq (π * t), sq_nonneg (sinh (π * t)), cosh_pos (π * t)]
  linarith

/-- The exact interior strip density is strictly positive. -/
theorem hirschmanDensity_pos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < hirschmanDensity r t := by
  exact div_pos (sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1) (by nlinarith [pi_pos, hr.2]))
    (mul_pos (mul_pos (by norm_num) hr.1) (hirschmanDenominator_pos hr t))

@[simp] theorem hirschmanDensity_neg (r t : ℝ) : hirschmanDensity r (-t) = hirschmanDensity r t := by
  simp [hirschmanDensity]

/-- The exact arctangent primitive of the interior strip density. -/
def hirschmanPrimitive (r t : ℝ) : ℝ :=
  arctan ((exp (π * t) + cos (π * r)) / sin (π * r)) / (π * r)

theorem hasDerivAt_hirschmanPrimitive {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    HasDerivAt (hirschmanPrimitive r) (hirschmanDensity r t) t := by
  have hs : 0 < sin (π * r) :=
    sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1) (by nlinarith [pi_pos, hr.2])
  have h := (((((hasDerivAt_id t).const_mul π).exp.add_const (cos (π * r))).div_const
    (sin (π * r))).arctan).div_const (π * r)
  change HasDerivAt (hirschmanPrimitive r)
    ((1 / (1 + ((exp (π * t) + cos (π * r)) / sin (π * r)) ^ 2)) *
      (exp (π * t) * (π * 1) / sin (π * r)) / (π * r)) t at h
  apply h.congr_deriv
  unfold hirschmanDensity
  rw [cosh_eq, exp_neg]
  have he := exp_pos (π * t)
  have hd := hirschmanDenominator_pos hr t
  have hpos : 0 < 1 + ((exp (π * t) + cos (π * r)) / sin (π * r)) ^ 2 := by positivity
  field_simp
  have hp : sin (π * r) ^ 2 + (exp (π * t) + cos (π * r)) ^ 2 =
      exp (π * t) ^ 2 + 1 + exp (π * t) * cos (π * r) * 2 := by
    nlinarith [sin_sq_add_cos_sq (π * r)]
  have hDp : 0 < exp (π * t) ^ 2 + 1 + exp (π * t) * cos (π * r) * 2 := by
    rw [← hp]
    positivity
  rw [hp]
  apply (eq_div_iff (mul_ne_zero (ne_of_gt hr.1) (ne_of_gt hDp))).2
  field_simp [ne_of_gt hr.1]

theorem tendsto_hirschmanPrimitive_atTop {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Tendsto (hirschmanPrimitive r) atTop (𝓝 ((π / 2) / (π * r))) := by
  have hs : 0 < sin (π * r) :=
    sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1) (by nlinarith [pi_pos, hr.2])
  have hexp : Tendsto (fun t : ℝ => exp (π * t)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop pi_pos)
  have hin : Tendsto (fun t : ℝ => (exp (π * t) + cos (π * r)) / sin (π * r)) atTop atTop := by
    have hadd : Tendsto (fun t : ℝ => exp (π * t) + cos (π * r)) atTop atTop :=
      hexp.atTop_add tendsto_const_nhds
    simpa only [div_eq_mul_inv] using
      hadd.atTop_mul_const (inv_pos.2 hs)
  change Tendsto (fun t : ℝ => arctan ((exp (π * t) + cos (π * r)) / sin (π * r)) / (π * r)) _ _
  exact (((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hin).div_const (π * r))

theorem tendsto_hirschmanPrimitive_atBot {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Tendsto (hirschmanPrimitive r) atBot (𝓝 ((π / 2 - π * r) / (π * r))) := by
  have hs : 0 < sin (π * r) :=
    sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1) (by nlinarith [pi_pos, hr.2])
  have hexp : Tendsto (fun t : ℝ => exp (π * t)) atBot (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot pi_pos)
  have hc : arctan (cos (π * r) / sin (π * r)) = π / 2 - π * r := by
    rw [show cos (π * r) / sin (π * r) = tan (π / 2 - π * r) by
      rw [tan_pi_div_two_sub, tan_eq_sin_div_cos, inv_div]]
    apply arctan_tan <;> nlinarith [pi_pos, hr.1, hr.2]
  have hlim := ((continuous_arctan.tendsto _).comp
    ((hexp.add_const (cos (π * r))).div_const (sin (π * r)))).div_const (π * r)
  change Tendsto (fun t : ℝ => arctan ((exp (π * t) + cos (π * r)) / sin (π * r)) / (π * r)) _ _
  simpa only [Function.comp_def, zero_add, hc] using hlim

/-- The explicit interior strip kernel is Lebesgue integrable. -/
theorem integrable_hirschmanDensity {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Integrable (hirschmanDensity r) :=
  integrable_of_even_nonneg_primitive (hirschmanDensity_neg r)
    (fun t => (hirschmanDensity_pos hr t).le) (hasDerivAt_hirschmanPrimitive hr)
    (tendsto_hirschmanPrimitive_atTop hr)

/-- The displayed interior strip kernel has mass exactly one. -/
theorem integral_hirschmanDensity {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫ t, hirschmanDensity r t) = 1 := by
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_hirschmanPrimitive hr)
    (integrable_hirschmanDensity hr) (tendsto_hirschmanPrimitive_atBot hr)
    (tendsto_hirschmanPrimitive_atTop hr)]
  field_simp [ne_of_gt hr.1]
  ring

/-- The actual formula has the explicit zero-parameter density as its pointwise limit. -/
theorem tendsto_hirschmanDensity_zero (t : ℝ) :
    Tendsto (fun r => hirschmanDensity r t) (𝓝[>] 0) (𝓝 (hirschmanDensityZero t)) := by
  have heq : (fun r => hirschmanDensity r t) =ᶠ[𝓝[>] 0]
      (fun r => π * sinc (π * r) / (2 * (cosh (π * t) + cos (π * r)))) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    rw [sinc_of_ne_zero (mul_ne_zero pi_ne_zero hr0), hirschmanDensity]
    field_simp [hr0]
  apply Filter.Tendsto.congr' heq.symm
  have hcont : ContinuousAt (fun r : ℝ => π * sinc (π * r) /
      (2 * (cosh (π * t) + cos (π * r)))) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2)
        (by linarith [cosh_pos (π * t)] : 0 < cosh (π * t) + 1))
  simpa only [hirschmanDensityZero, mul_zero, sinc_zero, cos_zero, mul_one] using
    hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- A common integrable majorant for the zero-parameter limit. The constant
is explicit, so bounded boundary logarithms admit ordinary dominated convergence. -/
theorem hirschmanDensity_le_two_mul_zero {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (t : ℝ) :
    hirschmanDensity r t ≤ 2 * hirschmanDensityZero t := by
  have hangle : 0 ≤ π * r := (mul_pos pi_pos hr).le
  have hc : 0 ≤ cos (π * r) := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by
    nlinarith [pi_pos]⟩
  have hch : 1 ≤ cosh (π * t) := by
    nlinarith [cosh_sq (π * t), sq_nonneg (sinh (π * t)), cosh_pos (π * t)]
  have hs : 0 ≤ sin (π * r) := sin_nonneg_of_nonneg_of_le_pi hangle (by
    nlinarith [pi_pos])
  have hb : 0 < 2 * r * cosh (π * t) := mul_pos (mul_pos (by norm_num) hr) (cosh_pos _)
  calc
    hirschmanDensity r t ≤ sin (π * r) / (2 * r * cosh (π * t)) := by
      exact div_le_div_of_nonneg_left hs hb (by
        have hprod : 0 ≤ (2 * r) * cos (π * r) := mul_nonneg (by positivity) hc
        nlinarith)
    _ ≤ (π * r) / (2 * r * cosh (π * t)) :=
      div_le_div_of_nonneg_right (sin_le hangle) hb.le
    _ = π / (2 * cosh (π * t)) := by field_simp
    _ ≤ 2 * hirschmanDensityZero t := by
      calc
        _ ≤ π / (cosh (π * t) + 1) := div_le_div_of_nonneg_left pi_pos.le
          (by positivity) (by linarith)
        _ = _ := by unfold hirschmanDensityZero; field_simp

/-- The explicit strip density is continuous in its integration variable. -/
@[fun_prop] theorem continuous_hirschmanDensity {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Continuous (hirschmanDensity r) := by
  unfold hirschmanDensity
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) hr.1) (hirschmanDenominator_pos hr t))

/-- Bounded measurable boundary observables admit the actual weighted
zero-parameter limit with the exact displayed kernels. -/
theorem tendsto_integral_hirschmanDensity_smul_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hbound : ∀ᵐ t, ‖f t‖ ≤ B) :
    Tendsto (fun r => ∫ t, hirschmanDensity r t • f t) (𝓝[>] 0)
      (𝓝 (∫ t, hirschmanDensityZero t • f t)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun t => (2 * B) * hirschmanDensityZero t)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with r hr
    exact ((continuous_hirschmanDensity ⟨hr.1, by linarith [hr.2]⟩).aestronglyMeasurable).smul hf
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with r hr
    filter_upwards [hbound] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hirschmanDensity_pos ⟨hr.1, by linarith [hr.2]⟩ t)]
    exact (mul_le_mul (hirschmanDensity_le_two_mul_zero hr.1 hr.2.le t) ht (norm_nonneg _)
      (by positivity [hirschmanDensityZero_pos t])).trans_eq (by ring)
  · exact integrable_hirschmanDensityZero.const_mul _
  · exact ae_of_all _ (fun t => (tendsto_hirschmanDensity_zero t).smul tendsto_const_nhds)

/-- The left strip harmonic-measure density is exactly `(1-r)β_(1-r)`. -/
theorem one_sub_mul_hirschmanDensity_one_sub {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    (1 - r) * hirschmanDensity (1 - r) t =
      sin (π * r) / (2 * (cosh (π * t) - cos (π * r))) := by
  unfold hirschmanDensity
  rw [show π * (1 - r) = π - π * r by ring, sin_pi_sub, cos_pi_sub]
  have hr1 : 1 - r ≠ 0 := by linarith [hr.2]
  field_simp [hr1]
  ring

/-- The right strip harmonic-measure density is exactly `rβ_r`. -/
theorem mul_hirschmanDensity {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    r * hirschmanDensity r t = sin (π * r) / (2 * (cosh (π * t) + cos (π * r))) := by
  unfold hirschmanDensity
  field_simp [hr]

/-- The two explicit strip boundary weights have the required exact masses. -/
theorem integral_boundary_weights_hirschmanDensity {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫ t, (1 - r) * hirschmanDensity (1 - r) t) = 1 - r ∧
      (∫ t, r * hirschmanDensity r t) = r := by
  constructor
  · rw [integral_const_mul, integral_hirschmanDensity (by constructor <;> linarith [hr.1, hr.2]), mul_one]
  · rw [integral_const_mul, integral_hirschmanDensity hr, mul_one]

end Real
