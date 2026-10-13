import NLAlib.Polynomial.FunctionApproximation.Basic
import NLAlib.Polynomial.BestApproximation.JacksonPolynomial
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Chebyshev coefficients and Fourier coefficients

The cosine-integral functionals are exactly the normalized Fourier coefficients of
an even cosine-circle pullback. This bridge does not assume analytic regularity.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real MeasureTheory Set
open scoped ComplexConjugate

namespace NLAlib

open scoped NLAlib.TwoPi

/-- The real Fourier coefficient of the cosine pullback is the normalized cosine integral.
Source: Trefethen, ATAP, Theorem 3.1; helper for `chebyshev-series-convergence`. -/
theorem re_fourierCoeff_realChebyshevCircleFunction {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (k : ℕ) :
    (fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ)).re =
      1 / Real.pi * ∫ θ in 0..Real.pi, f (cos θ) * cos ((k : ℝ) * θ) := by
  let g : AddCircle (2 * Real.pi) → ℝ := realChebyshevCircleFunction f
  let u : ℝ → ℝ := fun θ => f (cos θ) * cos ((k : ℝ) * θ)
  have hg : Continuous g := continuous_realChebyshevCircleFunction hf
  have hI : Integrable (fun t : AddCircle (2 * Real.pi) =>
      fourier (-(k : ℤ)) t * (g t : ℂ)) AddCircle.haarAddCircle :=
    ((fourier (-(k : ℤ))).continuous.mul (Complex.continuous_ofReal.comp hg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR := Complex.reCLM.integral_comp_comm hI
  change (∫ t : AddCircle (2 * Real.pi),
    (fourier (-(k : ℤ)) t * (g t : ℂ)).re ∂AddCircle.haarAddCircle) =
      (fourierCoeff (fun t => (g t : ℂ)) (k : ℤ)).re at hR
  rw [← hR, AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi)]
  simp only [smul_eq_mul]
  have hterm : ∀ θ : ℝ,
      (fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) *
        (g (θ : AddCircle (2 * Real.pi)) : ℂ)).re = u θ := by
    intro θ
    rw [fourier_neg, Complex.mul_re, Complex.conj_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, re_fourier_nat_coe_eq_cos]
    dsimp [g, u]
    rw [realChebyshevCircleFunction_coe]
    ring
  simp_rw [hterm]
  have hu : Continuous u :=
    (hf.comp_continuous continuous_cos (fun θ => ⟨neg_one_le_cos θ, cos_le_one θ⟩)).mul
      (by fun_prop)
  have heven : ∀ θ, u (-θ) = u θ := by
    intro θ
    simp [u, mul_neg]
  have hreflect : (∫ θ in -Real.pi..0, u θ) = ∫ θ in 0..Real.pi, u θ := by
    have h := intervalIntegral.integral_comp_neg (f := u) (a := 0) (b := Real.pi)
    simp only [neg_zero] at h
    simpa only [heven] using h.symm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hu.intervalIntegrable (-Real.pi) 0) (hu.intervalIntegrable 0 Real.pi)
  rw [hreflect] at hsplit
  have hbound : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hbound, ← hsplit]
  dsimp [u]
  field_simp
  ring

/-- The actual Chebyshev coefficient is the real Fourier coefficient, doubled except at zero.
Source: Trefethen, ATAP, Theorem 3.1; helper for `chebyshev-series-convergence`. -/
theorem chebyshevCoeff_eq_re_fourierCoeff {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (k : ℕ) :
    chebyshevCoeff f k = (if k = 0 then 1 else 2) *
      (fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (k : ℤ)).re := by
  rw [chebyshevCoeff_eq_cosine_integral, re_fourierCoeff_realChebyshevCircleFunction hf]
  ring

/-- Fourier coefficients of the even real cosine pullback are invariant under frequency negation.
Source: Trefethen, ATAP, Theorem 3.1; helper for `chebyshev-series-convergence`. -/
theorem fourierCoeff_realChebyshevCircleFunction_neg (f : ℝ → ℝ) (k : ℤ) :
    fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) (-k) =
      fourierCoeff (fun t => (realChebyshevCircleFunction f t : ℂ)) k := by
  rw [fourierCoeff, fourierCoeff]
  have h := MeasureTheory.integral_neg_eq_self
    (fun θ : AddCircle (2 * Real.pi) =>
      fourier (-k) θ • (realChebyshevCircleFunction f θ : ℂ)) AddCircle.haarAddCircle
  simp only [fourier_apply_neg, neg_neg, even_realChebyshevCircleFunction] at h ⊢
  exact h

end NLAlib
