import NLAlib.ForMathlib.Analysis.Complex.HirschmanBoundary

/-!
# The exponential coordinates on the two strip boundaries

The substitutions `w = ± exp(-πt)` identify the two Cauchy boundary pieces
with the exact densities used in Stein--Hirschman interpolation.
-/

noncomputable section

open Real Set MeasureTheory

namespace MeasureTheory

/-- Exponential coordinates give an exact whole-line substitution for the
positive half-line, with their actual Jacobian. -/
theorem integral_Ioi_zero_eq_exp_neg_pi (g : ℝ → ℝ) :
    (∫ w in Ioi (0 : ℝ), g w) =
      ∫ t : ℝ, (π * exp (-(π * t))) * g (exp (-(π * t))) := by
  have hRange : (fun t : ℝ => exp (-(π * t))) '' Set.univ = Ioi (0 : ℝ) := by
    ext w
    constructor
    · rintro ⟨t, _, rfl⟩
      exact exp_pos _
    · intro hw
      refine ⟨-(Real.log w) / π, Set.mem_univ _, ?_⟩
      change exp (-(π * (-(Real.log w) / π))) = w
      rw [show -(π * (-(Real.log w) / π)) = Real.log w by field_simp]
      exact exp_log hw
  have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ => exp (-(π * t)))
      (-(π * exp (-(π * t)))) t := by
    have h := ((hasDerivAt_id t).const_mul π).neg.exp
    change HasDerivAt (fun t : ℝ => exp (-(π * t))) (exp (-(π * t)) * -(π * 1)) t at h
    exact h.congr_deriv (by ring)
  have hchange := integral_image_eq_integral_abs_deriv_smul (s := Set.univ) MeasurableSet.univ
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (show Set.InjOn (fun t : ℝ => exp (-(π * t))) Set.univ from fun t _ s _ h => by
      have he := exp_injective h
      nlinarith [pi_pos]) g
  rw [hRange, Measure.restrict_univ] at hchange
  simpa only [abs_neg, abs_of_pos (mul_pos pi_pos (exp_pos _)), smul_eq_mul] using hchange

/-- The negative half-line has the same positive Jacobian after reflection. -/
theorem integral_Iio_zero_eq_neg_exp_neg_pi (g : ℝ → ℝ) :
    (∫ w in Iio (0 : ℝ), g w) =
      ∫ t : ℝ, (π * exp (-(π * t))) * g (-exp (-(π * t))) := by
  have hRange : (fun t : ℝ => -exp (-(π * t))) '' Set.univ = Iio (0 : ℝ) := by
    ext w
    constructor
    · rintro ⟨t, _, rfl⟩
      exact neg_neg_of_pos (exp_pos _)
    · intro hw
      refine ⟨-(Real.log (-w)) / π, Set.mem_univ _, ?_⟩
      change -exp (-(π * (-(Real.log (-w)) / π))) = w
      rw [show -(π * (-(Real.log (-w)) / π)) = Real.log (-w) by field_simp,
        exp_log (neg_pos.mpr hw), neg_neg]
  have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ => -exp (-(π * t)))
      (π * exp (-(π * t))) t := by
    have h := (((hasDerivAt_id t).const_mul π).neg.exp).neg
    change HasDerivAt (fun t : ℝ => -exp (-(π * t))) (-(exp (-(π * t)) * -(π * 1))) t at h
    exact h.congr_deriv (by ring)
  have hchange := integral_image_eq_integral_abs_deriv_smul (s := Set.univ) MeasurableSet.univ
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (show Set.InjOn (fun t : ℝ => -exp (-(π * t))) Set.univ from fun t _ s _ h => by
      have he := exp_injective (neg_injective h)
      nlinarith [pi_pos]) g
  rw [hRange, Measure.restrict_univ] at hchange
  simpa only [abs_of_pos (mul_pos pi_pos (exp_pos _)), smul_eq_mul] using hchange

end MeasureTheory

namespace Complex

/-- The positive exponential coordinate lies on the left boundary of the strip. -/
theorem hirschmanLog_positive_exp (t : ℝ) :
    log ((Real.exp (-(π * t)) : ℝ) : ℂ) * (-I) / (π : ℂ) = (t : ℂ) * I := by
  rw [← ofReal_log (Real.exp_pos _).le, Real.log_exp]
  push_cast
  field_simp

/-- The principal logarithm from the upper half-plane places the negative
exponential coordinate on the right boundary, with the same orientation. -/
theorem hirschmanLog_negative_exp (t : ℝ) :
    log ((-Real.exp (-(π * t)) : ℝ) : ℂ) * (-I) / (π : ℂ) = 1 + (t : ℂ) * I := by
  have hneg : -Real.exp (-(π * t)) < 0 := neg_neg_of_pos (Real.exp_pos _)
  rw [Complex.log, norm_real, Real.norm_eq_abs, abs_of_neg hneg, neg_neg,
    Real.log_exp, arg_ofReal_of_neg hneg]
  push_cast
  field_simp
  ring_nf
  simp [I_sq]
  ring

end Complex

namespace Real

/-- The positive Cauchy boundary has exactly the left strip weight. -/
theorem cauchyPDFReal_exp_neg_pi_mul_eq_hirschman_left {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    (π * exp (-(π * t))) * ProbabilityTheory.cauchyPDFReal (cos (π * r))
      (Real.toNNReal (sin (π * r))) (exp (-(π * t))) =
      (1 - r) * hirschmanDensity (1 - r) t := by
  have hs : 0 < sin (π * r) := sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  rw [one_sub_mul_hirschmanDensity_one_sub hr]
  unfold ProbabilityTheory.cauchyPDFReal
  rw [Real.coe_toNNReal _ hs.le]
  have hden : (exp (-(π * t)) - cos (π * r)) ^ 2 + sin (π * r) ^ 2 =
      2 * exp (-(π * t)) * (cosh (π * t) - cos (π * r)) := by
    rw [cosh_eq, exp_neg]
    field_simp
    nlinarith [sin_sq_add_cos_sq (π * r)]
  rw [hden, mul_inv_rev, mul_inv_rev]
  field_simp

/-- The negative Cauchy boundary has exactly the right strip weight. -/
theorem cauchyPDFReal_neg_exp_neg_pi_mul_eq_hirschman_right {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    (π * exp (-(π * t))) * ProbabilityTheory.cauchyPDFReal (cos (π * r))
      (Real.toNNReal (sin (π * r))) (-exp (-(π * t))) = r * hirschmanDensity r t := by
  have hs : 0 < sin (π * r) := sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  rw [mul_hirschmanDensity (ne_of_gt hr.1)]
  unfold ProbabilityTheory.cauchyPDFReal
  rw [Real.coe_toNNReal _ hs.le]
  have hden : (-exp (-(π * t)) - cos (π * r)) ^ 2 + sin (π * r) ^ 2 =
      2 * exp (-(π * t)) * (cosh (π * t) + cos (π * r)) := by
    rw [cosh_eq, exp_neg]
    field_simp
    nlinarith [sin_sq_add_cos_sq (π * r)]
  rw [hden, mul_inv_rev, mul_inv_rev]
  field_simp

end Real

namespace Complex

/-- The logarithmic image of the Cauchy boundary measure splits into exactly
the two Stein--Hirschman weights, with no unrecorded normalization constant. -/
theorem integral_cauchy_hirschmanLog_eq_boundary_integrals {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (G : ℂ → ℝ)
    (hG : Integrable (fun w : ℝ => ProbabilityTheory.cauchyPDFReal (Real.cos (π * r))
      (Real.toNNReal (Real.sin (π * r))) w * G (log (w : ℂ) * (-I) / (π : ℂ)))) :
    (∫ w : ℝ, ProbabilityTheory.cauchyPDFReal (Real.cos (π * r))
      (Real.toNNReal (Real.sin (π * r))) w * G (log (w : ℂ) * (-I) / (π : ℂ))) =
      (∫ t : ℝ, ((1 - r) * hirschmanDensity (1 - r) t) * G ((t : ℂ) * I)) +
      ∫ t : ℝ, (r * hirschmanDensity r t) * G (1 + (t : ℂ) * I) := by
  rw [← integral_add_compl measurableSet_Iic hG, compl_Iic, integral_Iic_eq_integral_Iio,
    integral_Iio_zero_eq_neg_exp_neg_pi, integral_Ioi_zero_eq_exp_neg_pi, add_comm]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp only
      rw [hirschmanLog_positive_exp, ← mul_assoc,
        cauchyPDFReal_exp_neg_pi_mul_eq_hirschman_left hr]
  · apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp only
      rw [hirschmanLog_negative_exp, ← mul_assoc,
        cauchyPDFReal_neg_exp_neg_pi_mul_eq_hirschman_right hr]

/-- The conformal disk boundary average equals the explicit weighted averages
on the two vertical strip boundaries. The integrability premise records only
the actual boundary function, not an assumed interpolation inequality. -/
theorem circleAverage_hirschmanDiskToStrip_eq_boundary_integrals {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (G : ℂ → ℝ)
    (hG : Integrable (fun w : ℝ => ProbabilityTheory.cauchyPDFReal (Real.cos (π * r))
      (Real.toNNReal (Real.sin (π * r))) w * G (log (w : ℂ) * (-I) / (π : ℂ)))) :
    Real.circleAverage (fun z => G (hirschmanDiskToStrip r z)) 0 1 =
      (∫ t : ℝ, ((1 - r) * hirschmanDensity (1 - r) t) * G ((t : ℂ) * I)) +
      ∫ t : ℝ, (r * hirschmanDensity r t) * G (1 + (t : ℂ) * I) := by
  have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  have hscale : (⟨Real.sin (π * r), hs.le⟩ : NNReal) = Real.toNNReal (Real.sin (π * r)) := by
    ext
    exact (Real.coe_toNNReal _ hs.le).symm
  have h := circleAverage_hirschmanDiskToHalfPlane_eq_cauchy (Real.cos (π * r)) hs
    (fun w => G (log w * (-I) / (π : ℂ)))
  rw [hscale] at h
  exact h.trans (integral_cauchy_hirschmanLog_eq_boundary_integrals hr G hG)

end Complex
