import NLAlib.ForMathlib.Analysis.FourierCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Fourier convolution identities on the circle of period two pi

Haar invariance gives the exact character-convolution formula, and normalized Haar
integration agrees with the normalized full-period interval integral.
-/

noncomputable section

open Complex MeasureTheory
open scoped Real ComplexConjugate

namespace NLAlib

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Subtracting circle arguments reverses the Fourier frequency in the second argument.
Source: Mathlib additive-circle Fourier characters; used by sharp `jackson-lipschitz`. -/
theorem fourier_apply_sub (k : ℤ) (x y : AddCircle (2 * Real.pi)) :
    fourier k (x - y) = fourier k x * fourier (-k) y := by
  rw [sub_eq_add_neg, fourier_apply_add]
  simp only [fourier_apply, smul_neg, neg_smul]

/-- Convolution with a Fourier character extracts the corresponding actual Fourier
coefficient. Haar invariance proves the identity for arbitrary functions.
Source: Fourier convolution identity; used by sharp `jackson-lipschitz`. -/
theorem integral_fourier_mul_comp_sub_eq_fourier_mul_coeff
    (g : AddCircle (2 * Real.pi) → ℂ) (k : ℤ) (a : AddCircle (2 * Real.pi)) :
    (∫ t : AddCircle (2 * Real.pi), fourier k t * g (a - t) ∂AddCircle.haarAddCircle) =
      fourier k a * fourierCoeff g k := by
  have h := MeasureTheory.integral_sub_left_eq_self
    (fun t : AddCircle (2 * Real.pi) => fourier (-k) t * g t) AddCircle.haarAddCircle a
  have hmul := congrArg (fun z : ℂ => fourier k a * z) h
  rw [← MeasureTheory.integral_const_mul] at hmul
  have hterm : ∀ t : AddCircle (2 * Real.pi),
      fourier k a * (fourier (-k) (a - t) * g (a - t)) = fourier k t * g (a - t) := by
    intro t
    rw [fourier_apply_sub, neg_neg]
    have hcancel : fourier k a * fourier (-k) a = 1 := by
      rw [← fourier_add, add_neg_cancel, fourier_zero]
    calc fourier k a * (fourier (-k) a * fourier k t * g (a - t)) =
        (fourier k a * fourier (-k) a) * (fourier k t * g (a - t)) := by ring
      _ = fourier k t * g (a - t) := by rw [hcancel, one_mul]
  simp_rw [hterm] at hmul
  simpa only [fourierCoeff, smul_eq_mul] using hmul

/-- Normalized Haar integration is the normalized full-period real interval integral.
Source: Mathlib's additive-circle Haar normalization; used by sharp `jackson-lipschitz`. -/
theorem integral_haarAddCircle_eq_inv_mul_intervalIntegral
    (f : AddCircle (2 * Real.pi) → ℝ) :
    (∫ t : AddCircle (2 * Real.pi), f t ∂AddCircle.haarAddCircle) =
      (2 * Real.pi)⁻¹ * ∫ t : ℝ in 0..2 * Real.pi, f (t : AddCircle (2 * Real.pi)) := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 f]
  simp only [zero_add, smul_eq_mul]

/-- Fourier coefficients of an even real-valued circle function are real. Haar reflection
and complex conjugation give this without an assumed coefficient-reality certificate.
Source: elementary Fourier symmetry; used by sharp `jackson-lipschitz`. -/
theorem im_fourierCoeff_of_even_real (g : AddCircle (2 * Real.pi) → ℝ)
    (heven : ∀ t, g (-t) = g t) (k : ℤ) :
    (fourierCoeff (fun t => (g t : ℂ)) k).im = 0 := by
  let f : AddCircle (2 * Real.pi) → ℂ := fun t => fourier (-k) t * (g t : ℂ)
  have h := MeasureTheory.integral_neg_eq_self f AddCircle.haarAddCircle
  have hterm : ∀ t : AddCircle (2 * Real.pi), f (-t) = conj (f t) := by
    intro t
    have hchar : fourier (-k) (-t) = fourier k t := by
      have hsub := fourier_apply_sub (-k) 0 t
      simpa only [zero_sub, neg_neg, fourier_eval_zero, one_mul] using hsub
    change fourier (-k) (-t) * (g (-t) : ℂ) = conj (fourier (-k) t * (g t : ℂ))
    rw [hchar, heven, map_mul, Complex.conj_ofReal, ← fourier_neg, neg_neg]
  simp_rw [hterm] at h
  rw [integral_conj] at h
  change conj (fourierCoeff (fun t => (g t : ℂ)) k) = fourierCoeff (fun t => (g t : ℂ)) k at h
  exact Complex.conj_eq_iff_im.mp h

/-- Real cosine-character convolution of an even continuous function is its actual real
Fourier coefficient times the same cosine character.
Source: Fourier convolution and even-real symmetry; used by sharp `jackson-lipschitz`. -/
theorem integral_re_fourier_mul_comp_sub_eq_re_fourier_mul_coeff
    {g : AddCircle (2 * Real.pi) → ℝ} (hg : Continuous g)
    (heven : ∀ t, g (-t) = g t) (k : ℤ) (a : AddCircle (2 * Real.pi)) :
    (∫ t : AddCircle (2 * Real.pi), (fourier k t).re * g (a - t) ∂AddCircle.haarAddCircle) =
      (fourier k a).re * (fourierCoeff (fun t => (g t : ℂ)) k).re := by
  have hsubC : Continuous (fun t : AddCircle (2 * Real.pi) => a - t) := continuous_const.sub continuous_id
  have hC : Continuous (fun t : AddCircle (2 * Real.pi) => fourier k t * (g (a - t) : ℂ)) :=
    (fourier k).continuous.mul (Complex.continuous_ofReal.comp (hg.comp hsubC))
  have hI : Integrable (fun t : AddCircle (2 * Real.pi) => fourier k t * (g (a - t) : ℂ))
      AddCircle.haarAddCircle := hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := Complex.reCLM.integral_comp_comm hI
  change (∫ t : AddCircle (2 * Real.pi), (fourier k t * (g (a - t) : ℂ)).re ∂AddCircle.haarAddCircle) =
    (∫ t : AddCircle (2 * Real.pi), fourier k t * (g (a - t) : ℂ) ∂AddCircle.haarAddCircle).re at h
  rw [integral_fourier_mul_comp_sub_eq_fourier_mul_coeff (fun t : AddCircle (2 * Real.pi) => (g t : ℂ)) k a] at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    im_fourierCoeff_of_even_real g heven k, mul_zero, sub_zero] using h

end NLAlib
