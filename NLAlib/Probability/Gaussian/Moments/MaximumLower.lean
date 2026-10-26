import NLAlib.Probability.Gaussian.Concentration.LowerTail
import NLAlib.Probability.Gaussian.Basic.StandardVector
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Lower maxima of independent standard Gaussian coordinates

The scalar Gaussian lower tail and the exact product law give a uniform
positive probability of a maximum at the square-root logarithmic scale.
This is the lower maximal estimate used for selected independent entries
in Latała--van Handel--Youssef, arXiv:1711.00807v2, Section 3.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace NLAlib

/-- The actual maximum of independent standard Gaussian coordinates has
the product lower tail expressed in terms of the exact scalar tail. -/
theorem one_sub_exp_gaussian_tail_le_measure_norm_ge (N : ℕ) (t : ℝ) :
    1 - Real.exp (-(N : ℝ) * (gaussianReal 0 1).real {x : ℝ | t ≤ |x|}) ≤
      (gaussianVector (Fin N)).real {g | t ≤ ‖g‖} := by
  let q := (gaussianReal 0 1).real {x : ℝ | t ≤ |x|}
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := by
    have h : (gaussianReal 0 1).real {x : ℝ | t ≤ |x|} ≤ (gaussianReal 0 1).real univ :=
      measureReal_mono (subset_univ _) (by finiteness)
    simpa only [probReal_univ] using h
  have hs : (gaussianReal 0 1).real {x : ℝ | |x| < t} = 1 - q := by
    have he : {x : ℝ | |x| < t} = {x : ℝ | t ≤ |x|}ᶜ := by ext x; simp
    rw [he, measureReal_compl (measurableSet_le measurable_const measurable_abs), probReal_univ]
  have hprod : (gaussianVector (Fin N)).real {g | ∀ i, |g i| < t} = (1 - q) ^ N := by
    have he : {g : Fin N → ℝ | ∀ i, |g i| < t} =
        Set.univ.pi (fun _ => {x : ℝ | |x| < t}) := by ext g; simp
    rw [he, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
    change (∏ _i : Fin N, (gaussianReal 0 1).real {x : ℝ | |x| < t}) = _
    simp only [hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hbad : (gaussianVector (Fin N)).real {g | ‖g‖ < t} ≤ (1 - q) ^ N := by
    rw [← hprod]
    apply measureReal_mono ?_ (by finiteness)
    intro g hg i
    exact (norm_le_pi_norm g i).trans_lt hg
  have hcomp : (gaussianVector (Fin N)).real {g | t ≤ ‖g‖} =
      1 - (gaussianVector (Fin N)).real {g | ‖g‖ < t} := by
    have he : {g : Fin N → ℝ | t ≤ ‖g‖} = {g : Fin N → ℝ | ‖g‖ < t}ᶜ := by ext g; simp
    rw [he, measureReal_compl (measurableSet_lt measurable_norm measurable_const), probReal_univ]
  have hpow : (1 - q) ^ N ≤ Real.exp (-(N : ℝ) * q) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - q) (Real.one_sub_le_exp_neg q) N
    simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using h
  rw [hcomp]
  dsimp [q] at hpow hbad
  linarith

/-- An explicit positive universal constant for lower expected Gaussian
coordinate maxima. Its exact value is immaterial to dimension-free bounds. -/
def gaussianMaximumLowerConstant : ℝ :=
  1 - Real.exp (-(Real.exp (-1) / Real.sqrt (2 * Real.pi)) / 2)

/-- The universal Gaussian maximum lower constant is strictly positive. -/
theorem gaussianMaximumLowerConstant_pos : 0 < gaussianMaximumLowerConstant := by
  unfold gaussianMaximumLowerConstant
  have hc : 0 < Real.exp (-1) / Real.sqrt (2 * Real.pi) := by positivity
  have h := Real.exp_lt_one_iff.mpr (show -(Real.exp (-1) / Real.sqrt (2 * Real.pi)) / 2 < 0 by linarith)
  linarith

/-- The expected maximum absolute coordinate of an actual independent
standard Gaussian vector is bounded below at its square-root logarithmic
scale, uniformly over all dimensions including zero. -/
theorem gaussianMaximumLowerConstant_mul_sqrt_log_le_integral_norm_gaussianVector
    (N : ℕ) :
    gaussianMaximumLowerConstant * Real.sqrt (Real.log ((N : ℝ) + 1)) ≤
      ∫ g : Fin N → ℝ, ‖g‖ ∂gaussianVector (Fin N) := by
  have hV : MemLp (fun g : Fin N → ℝ => g) 2 (gaussianVector (Fin N)) := by
    apply memLp_pi_iff.mpr
    intro i
    exact memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector i)
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [Nat.cast_zero, zero_add, Real.log_one, Real.sqrt_zero, mul_zero]
    exact integral_nonneg fun g => norm_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  let t := Real.sqrt (Real.log ((N : ℝ) + 1))
  let c := Real.exp (-1) / Real.sqrt (2 * Real.pi)
  let q := (gaussianReal 0 1).real {x : ℝ | t ≤ |x|}
  have hc : 0 < c := by dsimp [c]; positivity
  have hq0 : 0 ≤ q := measureReal_nonneg
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hscalar : c / ((N : ℝ) + 1) ≤ q := by
    have h := exp_neg_sq_div_sqrt_two_pi_le_gaussianReal_abs_tail t ht
    have he : Real.exp (-t ^ 2) = ((N : ℝ) + 1)⁻¹ := by
      dsimp [t]
      rw [Real.sq_sqrt hlog, Real.exp_neg, Real.exp_log (by linarith : 0 < (N : ℝ) + 1)]
    rw [he] at h
    simpa only [c, q, div_eq_mul_inv] using h
  have hNq : c / 2 ≤ (N : ℝ) * q := by
    have h := (div_le_iff₀ (by linarith : 0 < (N : ℝ) + 1)).mp hscalar
    have hmul := mul_nonneg hq0 (sub_nonneg.mpr hN1)
    nlinarith
  have htail : gaussianMaximumLowerConstant ≤
      (gaussianVector (Fin N)).real {g | t ≤ ‖g‖} := by
    have h := one_sub_exp_gaussian_tail_le_measure_norm_ge N t
    have he := Real.exp_le_exp.mpr (show -(N : ℝ) * q ≤ -c / 2 by nlinarith)
    change 1 - Real.exp (-c / 2) ≤ _
    change 1 - Real.exp (-(N : ℝ) * q) ≤ _ at h
    linarith
  have hmean := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun g : Fin N → ℝ => norm_nonneg g))
      (hV.norm.integrable (by norm_num)) t
  calc
    _ ≤ t * (gaussianVector (Fin N)).real {g | t ≤ ‖g‖} := by
      change gaussianMaximumLowerConstant * t ≤ _
      nlinarith
    _ ≤ _ := hmean

end NLAlib
