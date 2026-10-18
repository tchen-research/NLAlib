import NLAlib.ForMathlib.Analysis.Complex.HirschmanMajorants

/-!
# Exact scalar Stein--Hirschman interpolation

The boundary-majorant formulation uses the explicit normalized densities,
and is valid even when the analytic scalar function has zeros. It is the
form needed when a Schatten dual test is bounded by matrix boundary norms.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Appendix D, Lemma D.1.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace Complex

/-- Exact weighted scalar strip interpolation with bounded measurable
logarithmic boundary majorants. Positive regularization is actually removed;
no nonvanishing hypothesis on `g` or unspecified harmonic measure is used. -/
theorem norm_le_exp_hirschman_boundary_majorants {r B H : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (HadamardThreeLines.verticalStrip 0 1))
    (hbound : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖g z‖ ≤ B)
    (h₀ h₁ : ℝ → ℝ) (hm₀ : Measurable h₀) (hm₁ : Measurable h₁)
    (hb₀ : ∀ t, |h₀ t| ≤ H) (hb₁ : ∀ t, |h₁ t| ≤ H)
    (hleft : ∀ t : ℝ, ‖g ((t : ℂ) * I)‖ ≤ Real.exp (h₀ t))
    (hright : ∀ t : ℝ, ‖g (1 + (t : ℂ) * I)‖ ≤ Real.exp (h₁ t)) :
    ‖g (r : ℂ)‖ ≤ Real.exp (
      (∫ t : ℝ, ((1 - r) * hirschmanDensity (1 - r) t) * h₀ t) +
      ∫ t : ℝ, (r * hirschmanDensity r t) * h₁ t) := by
  have hcl : closure (HadamardThreeLines.verticalStrip 0 1) =
      HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp only [HadamardThreeLines.verticalStrip, HadamardThreeLines.verticalClosedStrip,
      closure_preimage_re, closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
  have hc := hg.continuousOn
  rw [hcl] at hc
  have ha : AnalyticOnNhd ℂ g (HadamardThreeLines.verticalStrip 0 1) :=
    (analyticOnNhd_iff_differentiableOn (isOpen_Ioo.preimage continuous_re)).mpr hg.differentiableOn
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hbound 0 (by
    simp [HadamardThreeLines.verticalClosedStrip]))
  have hH : 0 ≤ H := (abs_nonneg (h₀ 0)).trans (hb₀ 0)
  have hrr : 1 - r ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hmap₀ (t : ℝ) : (t : ℂ) * I ∈ HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [HadamardThreeLines.verticalClosedStrip]
  have hmap₁ (t : ℝ) : 1 + (t : ℂ) * I ∈ HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [HadamardThreeLines.verticalClosedStrip]
  have hcont₀ : Continuous (fun t : ℝ => g ((t : ℂ) * I)) := by
    simpa only [Function.comp_def] using hc.comp_continuous (by fun_prop) hmap₀
  have hcont₁ : Continuous (fun t : ℝ => g (1 + (t : ℂ) * I)) := by
    simpa only [Function.comp_def] using hc.comp_continuous (by fun_prop) hmap₁
  obtain ⟨ε, -, hε, hεlim⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ) < 1 by norm_num)
  have hlim₀ := tendsto_integral_hirschman_regularizedLogNorm_exp hrr hm₀ hH hb₀ hε hεlim
  have hlim₁ := tendsto_integral_hirschman_regularizedLogNorm_exp hr hm₁ hH hb₁ hε hεlim
  have hrightlim := (hlim₀.const_mul (1 - r)).add (hlim₁.const_mul r)
  have hfinal (n : ℕ) : sqrt (‖g (r : ℂ)‖ ^ 2 + (ε n) ^ 2) ≤
      Real.exp ((1 - r) * (∫ t : ℝ, hirschmanDensity (1 - r) t *
        regularizedLogNorm (ε n) ((Real.exp (h₀ t) : ℝ) : ℂ)) +
        r * (∫ t : ℝ, hirschmanDensity r t *
          regularizedLogNorm (ε n) ((Real.exp (h₁ t) : ℝ) : ℂ))) := by
    have hgint₀ := integrable_hirschmanDensity_mul_of_bounded hrr
      ((continuous_regularizedLogNorm (hε n).1).comp hcont₀).measurable
      (fun t => abs_regularizedLogNorm_le (hε n).1 hB (hbound _ (hmap₀ t)))
    have hgint₁ := integrable_hirschmanDensity_mul_of_bounded hr
      ((continuous_regularizedLogNorm (hε n).1).comp hcont₁).measurable
      (fun t => abs_regularizedLogNorm_le (hε n).1 hB (hbound _ (hmap₁ t)))
    have hmeas₀ := ((continuous_regularizedLogNorm (hε n).1).comp
      (continuous_ofReal.comp Real.continuous_exp)).measurable.comp hm₀
    have hmeas₁ := ((continuous_regularizedLogNorm (hε n).1).comp
      (continuous_ofReal.comp Real.continuous_exp)).measurable.comp hm₁
    have hhint₀ := integrable_hirschmanDensity_mul_of_bounded hrr hmeas₀
      (fun t => abs_regularizedLogNorm_exp_le (Ioo_subset_Icc_self (hε n)) hH (hb₀ t))
    have hhint₁ := integrable_hirschmanDensity_mul_of_bounded hr hmeas₁
      (fun t => abs_regularizedLogNorm_exp_le (Ioo_subset_Icc_self (hε n)) hH (hb₁ t))
    have hmono₀ := integral_mono hgint₀ hhint₀ (fun t =>
      mul_le_mul_of_nonneg_left (regularizedLogNorm_le_exp_of_norm_le (hε n).1 (hleft t))
        (hirschmanDensity_pos hrr t).le)
    have hmono₁ := integral_mono hgint₁ hhint₁ (fun t =>
      mul_le_mul_of_nonneg_left (regularizedLogNorm_le_exp_of_norm_le (hε n).1 (hright t))
        (hirschmanDensity_pos hr t).le)
    have hbase := regularizedLogNorm_le_hirschman_boundary_integrals hr hc ha hB hbound (hε n).1
    simp only [mul_assoc, integral_const_mul] at hbase
    have hlog : regularizedLogNorm (ε n) (g (r : ℂ)) ≤
        (1 - r) * (∫ t : ℝ, hirschmanDensity (1 - r) t *
          regularizedLogNorm (ε n) ((Real.exp (h₀ t) : ℝ) : ℂ)) +
        r * (∫ t : ℝ, hirschmanDensity r t *
          regularizedLogNorm (ε n) ((Real.exp (h₁ t) : ℝ) : ℂ)) :=
      hbase.trans (add_le_add (mul_le_mul_of_nonneg_left hmono₀ (by linarith [hr.2]))
        (mul_le_mul_of_nonneg_left hmono₁ hr.1.le))
    exact (Real.log_le_iff_le_exp (sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (hε n).1)))).mp hlog
  have hleftlim := ((tendsto_const_nhds (x := ‖g (r : ℂ)‖ ^ 2)).add (hεlim.pow 2)).sqrt
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, sqrt_sq (norm_nonneg _)] at hleftlim
  have h := le_of_tendsto_of_tendsto' hleftlim
    (Real.continuous_exp.continuousAt.tendsto.comp hrightlim) hfinal
  simpa only [Function.comp_def, mul_assoc, integral_const_mul] using h

end Complex
