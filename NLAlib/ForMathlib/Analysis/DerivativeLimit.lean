import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Passing derivatives through bounded pointwise approximations

On the positive time axis, pointwise convergence of functions and their
uniformly bounded derivatives preserves the derivative when the limiting
derivative is continuous. The proof passes the fundamental theorem of
calculus through dominated convergence on a finite time interval.
Source: fundamental theorem of calculus and dominated convergence.
Atlas: `ornstein-uhlenbeck` (approximation foundation).
-/

noncomputable section
open MeasureTheory Filter Set

namespace NLAlib

/-- Bounded pointwise convergence of derivatives, together with pointwise
convergence of functions, transfers differentiation on the positive time
axis if the derivative limit is continuous. All finite-interval
integrability is derived from measurability and the common bound. Source:
FTC and dominated convergence. Atlas: `ornstein-uhlenbeck`. -/
theorem hasDerivAt_of_pointwise_tendsto_of_bounded_derivatives
    (F : ℕ → ℝ → ℝ) (D : ℕ → ℝ → ℝ) (f d : ℝ → ℝ) (B : ℝ)
    (hDm : ∀ n, Measurable (D n)) (hdm : Measurable d)
    (hdc : ContinuousOn d (Ioi 0))
    (hDeriv : ∀ n t, 0 < t → HasDerivAt (F n) (D n t) t)
    (hBound : ∀ n t, 0 < t → |D n t| ≤ B)
    (hFlim : ∀ t, 0 < t → Tendsto (fun n => F n t) atTop (nhds (f t)))
    (hDlim : ∀ t, 0 < t → Tendsto (fun n => D n t) atTop (nhds (d t)))
    (t : ℝ) (ht : 0 < t) : HasDerivAt f (d t) t := by
  have hpos {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : x ∈ uIcc a b) : 0 < x := by
    change min a b ≤ x ∧ x ≤ max a b at hx
    exact lt_of_lt_of_le (lt_min ha hb) hx.1
  have hdb (x : ℝ) (hx : 0 < x) : |d x| ≤ B :=
    le_of_tendsto' ((continuous_abs.tendsto (d x)).comp (hDlim x hx))
      (fun n => hBound n x hx)
  have hDi (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      IntervalIntegrable (D n) volume a b := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume a b).mono_fun'
      (hDm n).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Real.norm_eq_abs]
    exact hBound n x (hpos ha hb (uIoc_subset_uIcc hx))
  have hdi (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable d volume a b := by
    refine (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume a b).mono_fun'
      hdm.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Real.norm_eq_abs]
    exact hdb x (hpos ha hb (uIoc_subset_uIcc hx))
  have hidentity (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      f b - f a = ∫ s in a..b, d s := by
    have hN (n : ℕ) : (∫ s in a..b, D n s) = F n b - F n a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hDeriv n s (hpos ha hb hs)) (hDi n a b ha hb)
    have hI : Tendsto (fun n => ∫ s in a..b, D n s) atTop
        (nhds (∫ s in a..b, d s)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => B) (Eventually.of_forall fun n => (hDm n).aestronglyMeasurable.restrict)
        (Eventually.of_forall fun n => ae_of_all _ fun s hs => ?_)
        intervalIntegrable_const (ae_of_all _ fun s hs => ?_)
      · rw [Real.norm_eq_abs]
        exact hBound n s (hpos ha hb (uIoc_subset_uIcc hs))
      · exact hDlim s (hpos ha hb (uIoc_subset_uIcc hs))
    have he : (fun n => ∫ s in a..b, D n s) = fun n => F n b - F n a := funext hN
    rw [he] at hI
    exact tendsto_nhds_unique ((hFlim b hb).sub (hFlim a ha)) hI
  let a := t / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hc : ContinuousAt d t := hdc.continuousAt (isOpen_Ioi.mem_nhds ht)
  have hFTC := intervalIntegral.integral_hasDerivAt_right (hdi a t ha ht)
    hdm.stronglyMeasurable.stronglyMeasurableAtFilter hc
  apply (hFTC.const_add (f a)).congr_of_eventuallyEq
  have hnear : ∀ᶠ s in nhds t, 0 < s := isOpen_Ioi.mem_nhds ht
  filter_upwards [hnear] with s hs
  have h := hidentity a s ha hs
  linarith

end NLAlib
