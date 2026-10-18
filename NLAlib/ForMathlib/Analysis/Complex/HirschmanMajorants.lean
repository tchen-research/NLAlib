import NLAlib.ForMathlib.Analysis.Complex.HirschmanBoundaryLimit

/-!
# Removing the positive logarithmic regularization

Bounded boundary majorants retain the exact Stein--Hirschman densities while
allowing zeros of the scalar analytic function. Source:
Sutter--Berta--Tomamichel, arXiv:1604.03023v3, Appendix D.
-/

noncomputable section

open Set Filter MeasureTheory Real
open scoped Topology

namespace Real

/-- Every bounded measurable real observable is integrable against the
explicit normalized Stein--Hirschman density. -/
theorem integrable_hirschmanDensity_mul_of_bounded {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hbound : ∀ t, |f t| ≤ B) :
    Integrable (fun t => hirschmanDensity r t * f t) := by
  apply ((integrable_hirschmanDensity hr).const_mul B).mono'
    (((continuous_hirschmanDensity hr).measurable).mul hf).aestronglyMeasurable
  exact ae_of_all _ fun t => by
    dsimp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hirschmanDensity_pos hr t), Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound t) (hirschmanDensity_pos hr t).le

end Real

namespace Complex

/-- Exponential majorants retain a lower bound even as regularization tends
to zero, so negative logarithmic parts are controlled honestly. -/
theorem regularizedLogNorm_exp_bounds {ε H x : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1)
    (hx : |x| ≤ H) :
    -H ≤ regularizedLogNorm ε ((Real.exp x : ℝ) : ℂ) ∧
      regularizedLogNorm ε ((Real.exp x : ℝ) : ℂ) ≤
        Real.log (sqrt ((Real.exp H) ^ 2 + 1)) := by
  have hn : ‖((Real.exp x : ℝ) : ℂ)‖ = Real.exp x := by
    simp only [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
  have hpos : 0 < sqrt ((Real.exp x) ^ 2 + ε ^ 2) := sqrt_pos.mpr (by positivity)
  have hxH := (abs_le.mp hx).2
  have he : Real.exp x ≤ Real.exp H := Real.exp_le_exp.mpr hxH
  unfold regularizedLogNorm
  rw [hn]
  constructor
  · calc
      -H ≤ x := (abs_le.mp hx).1
      _ = Real.log (Real.exp x) := (Real.log_exp x).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos x) (by
        calc
          Real.exp x = sqrt ((Real.exp x) ^ 2) := (sqrt_sq (Real.exp_pos x).le).symm
          _ ≤ _ := sqrt_le_sqrt (by nlinarith [sq_nonneg ε]))
  · apply Real.log_le_log hpos
    apply sqrt_le_sqrt
    nlinarith [Real.exp_pos x, Real.exp_pos H, hε.1, hε.2]

/-- A uniform absolute bound for all regularizations between zero and one. -/
theorem abs_regularizedLogNorm_exp_le {ε H x : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1)
    (hH : 0 ≤ H) (hx : |x| ≤ H) :
    |regularizedLogNorm ε ((Real.exp x : ℝ) : ℂ)| ≤
      H + |Real.log (sqrt ((Real.exp H) ^ 2 + 1))| := by
  have h := regularizedLogNorm_exp_bounds hε hx
  rw [abs_le]
  constructor
  · linarith [abs_nonneg (Real.log (sqrt ((Real.exp H) ^ 2 + 1)))]
  · linarith [le_abs_self (Real.log (sqrt ((Real.exp H) ^ 2 + 1)))]

/-- At every real majorant value the regularized logarithm converges to that
same value, since its unregularized exponential is strictly positive. -/
theorem tendsto_regularizedLogNorm_exp {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => regularizedLogNorm (ε n) ((Real.exp x : ℝ) : ℂ)) atTop (𝓝 x) := by
  have ht := ((tendsto_const_nhds (x := (Real.exp x) ^ 2)).add (hε.pow 2)).sqrt
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, sqrt_sq (Real.exp_pos x).le] at ht
  have hl := (Real.continuousAt_log (Real.exp_ne_zero x)).tendsto.comp ht
  simpa only [Function.comp_def, regularizedLogNorm, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x),
    Real.log_exp] using hl

/-- Dominated convergence removes logarithmic regularization under the exact
Stein--Hirschman probability density. -/
theorem tendsto_integral_hirschman_regularizedLogNorm_exp {r H : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {h : ℝ → ℝ} (hh : Measurable h)
    (hH : 0 ≤ H) (hbound : ∀ t, |h t| ≤ H)
    {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Ioo (0 : ℝ) 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t : ℝ, hirschmanDensity r t *
      regularizedLogNorm (ε n) ((Real.exp (h t) : ℝ) : ℂ)) atTop
      (𝓝 (∫ t : ℝ, hirschmanDensity r t * h t)) := by
  let C := H + |Real.log (sqrt ((Real.exp H) ^ 2 + 1))|
  apply tendsto_integral_of_dominated_convergence (fun t => C * hirschmanDensity r t)
  · intro n
    have hm := ((continuous_regularizedLogNorm (hε n).1).comp
      (continuous_ofReal.comp Real.continuous_exp)).measurable.comp hh
    exact ((continuous_hirschmanDensity hr).measurable.mul hm).aestronglyMeasurable
  · exact (integrable_hirschmanDensity hr).const_mul C
  · intro n
    exact ae_of_all _ fun t => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hirschmanDensity_pos hr t), Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (abs_regularizedLogNorm_exp_le (Ioo_subset_Icc_self (hε n)) hH (hbound t))
        (hirschmanDensity_pos hr t).le
  · exact ae_of_all _ fun t => (tendsto_regularizedLogNorm_exp hεlim (h t)).const_mul _

/-- An exponential bound on the actual norm gives the same bound after
positive logarithmic regularization. -/
theorem regularizedLogNorm_le_exp_of_norm_le {ε x : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ ≤ Real.exp x) :
    regularizedLogNorm ε z ≤ regularizedLogNorm ε ((Real.exp x : ℝ) : ℂ) := by
  have h := (regularizedLogNorm_bounds hε (Real.exp_pos x).le hz).2
  simpa only [regularizedLogNorm, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using h

end Complex
