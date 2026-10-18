import NLAlib.ForMathlib.Analysis.Complex.HirschmanRadial
import Mathlib.Topology.Order.IsLUB

/-!
# The actual strip boundary limit of regularized disk averages

Dominated convergence is applied after the explicit arctangent parametrization.
The only exceptional finite parameter maps to zero in the upper half-plane.
Source: Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Appendix D.
-/

noncomputable section

open Real Set Metric MeasureTheory Filter
open scoped Topology

namespace Complex

/-- Regularized logarithmic disk averages converge to the actual boundary
average, for a bounded function continuous only on the closed strip. -/
theorem tendsto_circleAverage_regularizedLogNorm_hirschman {r B ε : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {g : ℂ → ℂ}
    (hg : ContinuousOn g (HadamardThreeLines.verticalClosedStrip 0 1))
    (hB : 0 ≤ B)
    (hbound : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖g z‖ ≤ B)
    (hε : 0 < ε) {ρ : ℕ → ℝ} (hρ : ∀ n, ρ n ∈ Ioo (0 : ℝ) 1)
    (hρlim : Tendsto ρ atTop (𝓝 1)) :
    Tendsto (fun n => Real.circleAverage
      (fun z => regularizedLogNorm ε (g (hirschmanDiskToStrip r z))) 0 (ρ n)) atTop
      (𝓝 (Real.circleAverage (fun z => regularizedLogNorm ε
        (g (hirschmanDiskToStrip r z))) 0 1)) := by
  let C := |Real.log ε| + |Real.log (sqrt (B ^ 2 + ε ^ 2))|
  let P := ProbabilityTheory.cauchyPDFReal (0 : ℝ) (1 : NNReal)
  let U (n : ℕ) (q : ℝ) := (ρ n : ℂ) * circleMap 0 1 (hirschmanBoundaryAngle q)
  let W (q : ℝ) := log ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ) * (-I) / (π : ℂ)
  have hU (n : ℕ) (q : ℝ) : U n q ∈ ball (0 : ℂ) 1 := by
    have hn : ‖U n q‖ < 1 := by
      simpa [U, norm_mul, norm_circleMap_zero, abs_of_pos (hρ n).1] using (hρ n).2
    simpa using hn
  have hstrip (n : ℕ) (q : ℝ) :
      hirschmanDiskToStrip r (U n q) ∈ HadamardThreeLines.verticalClosedStrip 0 1 :=
    Ioo_subset_Icc_self (hirschmanDiskToStrip_re_mem_Ioo hr (hU n q))
  have hcont (n : ℕ) : Continuous (fun q : ℝ => regularizedLogNorm ε
      (g (hirschmanDiskToStrip r (U n q)))) :=
    (continuous_regularizedLogNorm hε).comp
      (hg.comp_continuous (continuous_hirschmanDiskToStrip_radial hr (hρ n)) (hstrip n))
  have hlim : ∀ᵐ q : ℝ, Tendsto (fun n => P q * regularizedLogNorm ε
      (g (hirschmanDiskToStrip r (U n q)))) atTop (𝓝 (P q * regularizedLogNorm ε (g (W q)))) := by
    have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
      (by nlinarith [pi_pos, hr.2])
    filter_upwards [volume.ae_ne (-Real.cos (π * r) / Real.sin (π * r))] with q hq
    have hw : Real.cos (π * r) + Real.sin (π * r) * q ≠ 0 := by
      intro h
      apply hq
      apply (eq_div_iff (ne_of_gt hs)).mpr
      linarith
    have hUl : Tendsto (fun n => U n q) atTop
        (𝓝 (circleMap 0 1 (hirschmanBoundaryAngle q))) := by
      have ht := ((continuous_ofReal.tendsto _).comp hρlim).mul_const
        (circleMap 0 1 (hirschmanBoundaryAngle q))
      simp only [ofReal_one, one_mul] at ht
      exact ht.congr' (Eventually.of_forall fun _ => rfl)
    have hφ := tendsto_hirschmanDiskToStrip_boundary hr (fun n => hU n q) hUl hw
    have hgl : Tendsto (fun n => g (hirschmanDiskToStrip r (U n q))) atTop (𝓝 (g (W q))) :=
      (hg _ (hirschmanLog_real_re_mem_Icc _)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hφ, Eventually.of_forall fun n => hstrip n q⟩)
    exact ((continuous_regularizedLogNorm hε).continuousAt.tendsto.comp hgl).const_mul (P q)
  have hDCT := tendsto_integral_of_dominated_convergence (fun q : ℝ => C * P q)
    (fun n => ((ProbabilityTheory.measurable_cauchyPDFReal 0 1).mul (hcont n).measurable).aestronglyMeasurable)
    ((ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := 1)).const_mul C)
    (fun n => ae_of_all _ fun q => by
      have hp : 0 ≤ P q := by dsimp [P, ProbabilityTheory.cauchyPDFReal]; positivity
      dsimp only [Pi.mul_apply, Function.comp_apply]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hp, Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (abs_regularizedLogNorm_le hε hB (hbound _ (hstrip n q))) hp)
    hlim
  have hEq (n : ℕ) : Real.circleAverage
      (fun z => regularizedLogNorm ε (g (hirschmanDiskToStrip r z))) 0 (ρ n) =
      ∫ q : ℝ, P q * regularizedLogNorm ε (g (hirschmanDiskToStrip r (U n q))) := by
    rw [circleAverage_zero_radius_eq_circleAverage_smul,
      circleAverage_eq_integral_hirschmanBoundaryAngle]
    simp_rw [hirschmanBoundaryWeight_eq_cauchy]
    rfl
  have hEqB : Real.circleAverage
      (fun z => regularizedLogNorm ε (g (hirschmanDiskToStrip r z))) 0 1 =
      ∫ q : ℝ, P q * regularizedLogNorm ε (g (W q)) := by
    rw [circleAverage_eq_integral_hirschmanBoundaryAngle]
    simp_rw [hirschmanBoundaryWeight_eq_cauchy]
    congr 1
    funext q
    simp only [hirschmanDiskToStrip, hirschmanDiskToHalfPlane_circleMap_boundary, W, P]
  simpa only [hEq, hEqB, Pi.mul_apply, P] using hDCT

/-- The actual bounded holomorphic strip function satisfies the logarithmic
boundary inequality after positive regularization. No nonvanishing hypothesis
on the function, on the center, or on either boundary is imposed. -/
theorem regularizedLogNorm_le_hirschman_boundary_integrals {r B ε : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {g : ℂ → ℂ}
    (hg : ContinuousOn g (HadamardThreeLines.verticalClosedStrip 0 1))
    (ha : AnalyticOnNhd ℂ g (HadamardThreeLines.verticalStrip 0 1))
    (hB : 0 ≤ B)
    (hbound : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖g z‖ ≤ B)
    (hε : 0 < ε) :
    regularizedLogNorm ε (g (r : ℂ)) ≤
      (∫ t : ℝ, ((1 - r) * hirschmanDensity (1 - r) t) *
        regularizedLogNorm ε (g ((t : ℂ) * I))) +
      ∫ t : ℝ, (r * hirschmanDensity r t) *
        regularizedLogNorm ε (g (1 + (t : ℂ) * I)) := by
  obtain ⟨ρ, -, hρ, hρlim⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
  have hlim := tendsto_circleAverage_regularizedLogNorm_hirschman hr hg hB hbound hε hρ hρlim
  have hle : regularizedLogNorm ε (g (r : ℂ)) ≤
      Real.circleAverage (fun z => regularizedLogNorm ε (g (hirschmanDiskToStrip r z))) 0 1 := by
    apply ge_of_tendsto' hlim
    intro n
    have hf : AnalyticOnNhd ℂ (fun z => g (hirschmanDiskToStrip r z)) (closedBall 0 (ρ n)) := by
      intro z hz
      have hn : ‖z‖ ≤ ρ n := by simpa using hz
      have hb : z ∈ ball (0 : ℂ) 1 := by simpa using hn.trans_lt (hρ n).2
      exact (ha _ (hirschmanDiskToStrip_re_mem_Ioo hr hb)).comp
        (analyticOnNhd_hirschmanDiskToStrip hr _ hb)
    have hj := hf.log_sqrt_norm_sq_add_sq_le_circleAverage (hρ n).1 hε
    simpa only [hirschmanDiskToStrip_zero hr, regularizedLogNorm] using hj
  rw [circleAverage_hirschmanDiskToStrip_eq_boundary_integrals hr
    (fun z => regularizedLogNorm ε (g z))
    (integrable_cauchy_mul_regularizedLog_boundary hg hB hbound hε _ _)] at hle
  exact hle

end Complex
