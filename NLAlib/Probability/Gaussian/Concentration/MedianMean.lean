import NLAlib.Probability.Gaussian.Concentration.LipschitzConcentration

/-! # Gaussian mean and tail bounds from an actual sublevel probability

All laws, expectations and regularity are those of the actual objects.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- A true half-probability sublevel bound for a Euclidean Gaussian Lipschitz function controls its actual mean by the sublevel plus four Lipschitz constants. -/
theorem integral_le_of_half_measure_sublevel_gaussianVector
    {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) {L a : ℝ}
    (hL : 0 < L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hhalf : (1 / 2 : ℝ) ≤ (gaussianVector ι).real {x | f x ≤ a}) :
    (∫ x, f x ∂gaussianVector ι) ≤ a + 4 * L := by
  by_contra! hbad
  have hneg : ∀ x y, |(-f x) - (-f y)| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
    intro x y
    simpa only [neg_sub_neg, abs_sub_comm] using hLip x y
  have ht := measureReal_ge_le_of_lipschitz_gaussianVector (fun x => -f x) L
    hL hneg 4 (by norm_num)
  rw [integral_neg] at ht
  have hsub : {x | f x ≤ a} ⊆
      {x | -(∫ y, f y ∂gaussianVector ι) + L * 4 ≤ -f x} := by
    intro x hx
    change f x ≤ a at hx
    change -(∫ y, f y ∂gaussianVector ι) + L * 4 ≤ -f x
    linarith
  have hsmall : Real.exp (-(4 : ℝ)^2 / 2) < 1 / 2 := by
    have hx : (2 : ℝ) < Real.exp 8 :=
      lt_of_lt_of_le (by norm_num : (2 : ℝ) < 8 + 1) (Real.add_one_le_exp 8)
    have hh := (inv_lt_inv₀ (Real.exp_pos 8) (by norm_num : (0 : ℝ) < 2)).mpr hx
    simpa only [show -(4 : ℝ)^2 / 2 = -8 by norm_num, Real.exp_neg, one_div] using hh
  exact (not_lt_of_ge hhalf) (((measureReal_mono hsub).trans ht).trans_lt hsmall)

/-- A genuine Gaussian half-probability sublevel bound yields the explicit source-scale all-height tail.
Source: Ledoux Gaussian concentration, applied in arXiv:2406.11453v2, Theorem 2.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem measureReal_gt_sublevel_add_le_gaussianVector
    {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) {L a : ℝ}
    (hL : 0 < L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hhalf : (1 / 2 : ℝ) ≤ (gaussianVector ι).real {x | f x ≤ a})
    {t : ℝ} (ht : 0 ≤ t) :
    (gaussianVector ι).real {x | a + 4 * L + 2 * L * t < f x} ≤ Real.exp (-t^2) := by
  have hm := integral_le_of_half_measure_sublevel_gaussianVector f hL hLip hhalf
  have hc := measureReal_ge_le_of_lipschitz_gaussianVector f L hL hLip (2 * t) (by positivity)
  have hsub : {x | a + 4 * L + 2 * L * t < f x} ⊆
      {x | (∫ y, f y ∂gaussianVector ι) + L * (2 * t) ≤ f x} := by
    intro x hx
    change a + 4 * L + 2 * L * t < f x at hx
    change (∫ y, f y ∂gaussianVector ι) + L * (2 * t) ≤ f x
    linarith
  exact ((measureReal_mono hsub).trans hc).trans
    (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t]))

end NLAlib
