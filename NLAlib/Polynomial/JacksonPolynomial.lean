import NLAlib.Polynomial.JacksonPeriodic
import NLAlib.Polynomial.CosineBasis
import NLAlib.ForMathlib.Analysis.FourierConvolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Algebraic polynomials from the sharp Jackson convolution

The actual even circle pullback has real Fourier coefficients. Its convolution with
the proved finite cosine kernel is therefore an algebraic Chebyshev polynomial.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev MeasureTheory Set Finset Real
open scoped ComplexConjugate

namespace NLAlib

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The real cosine pullback to the circle of period `2π`.
Source: operator rederivations `rt:jackson`; construction for `jackson-lipschitz`. -/
def realChebyshevCircleFunction (f : ℝ → ℝ) (t : AddCircle (2 * Real.pi)) : ℝ :=
  f ((fourier 1 t).re)

/-- Every cosine-circle argument lies in the closed unit interval.
Source: unit norm of Fourier characters; helper for `jackson-lipschitz`. -/
theorem re_fourier_one_mem_Icc (t : AddCircle (2 * Real.pi)) :
    (fourier 1 t).re ∈ Icc (-1 : ℝ) 1 := by
  have h : |(fourier 1 t).re| ≤ 1 := by
    simpa only [show ‖fourier 1 t‖ = (1 : ℝ) from Circle.norm_coe _] using
      Complex.abs_re_le_norm (fourier 1 t)
  exact abs_le.mp h

/-- The actual cosine pullback of a continuous interval function is continuous.
Source: cosine-circle substitution in `rt:jackson`; helper for `jackson-lipschitz`. -/
theorem continuous_realChebyshevCircleFunction {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) : Continuous (realChebyshevCircleFunction f) :=
  hf.comp_continuous (Complex.continuous_re.comp (fourier 1).continuous)
    re_fourier_one_mem_Icc

/-- The actual cosine pullback is even.
Source: conjugation of Fourier characters; helper for `jackson-lipschitz`. -/
theorem even_realChebyshevCircleFunction (f : ℝ → ℝ) (t : AddCircle (2 * Real.pi)) :
    realChebyshevCircleFunction f (-t) = realChebyshevCircleFunction f t := by
  have h : fourier 1 (-t) = conj (fourier 1 t) := by
    have hs := fourier_apply_sub 1 0 t
    simpa only [zero_sub, fourier_eval_zero, one_mul, fourier_neg] using hs
  unfold realChebyshevCircleFunction
  rw [h, Complex.conj_re]

/-- Evaluating the circle pullback at a real angle gives the usual cosine substitution.
Source: the Fourier character definition; helper for `jackson-lipschitz`. -/
theorem realChebyshevCircleFunction_coe (f : ℝ → ℝ) (t : ℝ) :
    realChebyshevCircleFunction f (t : AddCircle (2 * Real.pi)) = f (cos t) := by
  unfold realChebyshevCircleFunction
  rw [show (fourier 1 (t : AddCircle (2 * Real.pi))).re = cos t by
    simpa only [Nat.cast_one, one_mul] using re_fourier_nat_coe_eq_cos 1 t]

/-- Evaluating `T_k` on the real part of a unit character gives the real `k`th character.
Source: the Chebyshev cosine identity; helper for `jackson-lipschitz`. -/
theorem eval_T_re_fourier_one (k : ℕ) (t : AddCircle (2 * Real.pi)) :
    (T ℝ (k : ℤ)).eval ((fourier 1 t).re) = (fourier (k : ℤ) t).re := by
  induction t using QuotientAddGroup.induction_on with | H t =>
    rw [show (fourier 1 (t : AddCircle (2 * Real.pi))).re = cos t by
      simpa only [Nat.cast_one, one_mul] using re_fourier_nat_coe_eq_cos 1 t,
      re_fourier_nat_coe_eq_cos k t]
    simpa only [Nat.cast_one, one_mul, Int.cast_natCast] using T_real_cos t (k : ℤ)

/-- A polynomial cosine kernel convolved with an actual even continuous circle function
is an actual algebraic polynomial of the same degree. The coefficients are its genuine
Fourier coefficients rather than an assumed polynomial representation.
Source: finite cosine expansion and Fourier convolution in `rt:jackson`;
construction for atlas `jackson-lipschitz`. -/
theorem exists_polynomial_circle_convolution {K : ℝ[X]} {n : ℕ} (hK : K.degree ≤ n)
    {g : AddCircle (2 * Real.pi) → ℝ} (hg : Continuous g) (heven : ∀ t, g (-t) = g t) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ a : AddCircle (2 * Real.pi),
      (∫ t : AddCircle (2 * Real.pi), K.eval ((fourier 1 t).re) * g (a - t)
        ∂AddCircle.haarAddCircle) = p.eval ((fourier 1 a).re) := by
  obtain ⟨c, hc⟩ := exists_sum_smul_T_eq_of_degree_le hK
  let p : ℝ[X] := ∑ k ∈ range (n + 1),
    (c k * (fourierCoeff (fun t => (g t : ℂ)) (k : ℤ)).re) • T ℝ (k : ℤ)
  refine ⟨p, ?_, fun a => ?_⟩
  · refine (degree_sum_le _ _).trans (Finset.sup_le fun k hk => ?_)
    refine (degree_smul_le _ _).trans ?_
    rw [degree_T, Int.natAbs_natCast]
    exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk)
  · have hI : ∀ k ∈ range (n + 1), Integrable
        (fun t : AddCircle (2 * Real.pi) => c k * (fourier (k : ℤ) t).re * g (a - t))
        AddCircle.haarAddCircle := by
      intro k hk
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      exact (continuous_const.mul (Complex.continuous_re.comp (fourier (k : ℤ)).continuous)).mul
        (hg.comp (continuous_const.sub continuous_id))
    have hterm : ∀ t : AddCircle (2 * Real.pi),
        K.eval ((fourier 1 t).re) * g (a - t) =
          ∑ k ∈ range (n + 1), c k * (fourier (k : ℤ) t).re * g (a - t) := by
      intro t
      rw [← hc, eval_finsetSum, Finset.sum_mul]
      simp only [eval_smul, smul_eq_mul, eval_T_re_fourier_one]
    simp_rw [hterm]
    rw [MeasureTheory.integral_finsetSum _ hI]
    unfold p
    rw [eval_finsetSum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (fun t : AddCircle (2 * Real.pi) => c k * (fourier (k : ℤ) t).re * g (a - t)) =
        (fun t => c k * ((fourier (k : ℤ) t).re * g (a - t))) by funext t; ring]
    rw [MeasureTheory.integral_const_mul,
      integral_re_fourier_mul_comp_sub_eq_re_fourier_mul_coeff hg heven,
      eval_smul, smul_eq_mul, eval_T_re_fourier_one]
    ring

/-- Cosine substitution preserves the Lipschitz constant of a unit-interval function.
Source: the one-Lipschitz cosine function; helper for sharp `jackson-lipschitz`. -/
theorem lipschitzWith_comp_cos {f : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) : LipschitzWith L (fun t : ℝ => f (cos t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hf.dist_le_mul (cos x) ⟨neg_one_le_cos x, cos_le_one x⟩
    (cos y) ⟨neg_one_le_cos y, cos_le_one y⟩).trans
      (mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one, one_mul] using
        Real.lipschitzWith_cos.dist_le_mul x y) L.coe_nonneg)

/-- The fixed sharp periodic convolution for a cosine pullback is represented by an
actual algebraic polynomial with degree at most `n`.
Source: Arnold, numerical analysis, Section 1.2; operator rederivations `rt:jackson`;
construction for atlas `jackson-lipschitz`. -/
theorem exists_polynomial_jacksonPeriodicApprox {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (n : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ x : ℝ,
      jacksonPeriodicApprox n (fun t => f (cos t)) x = p.eval (cos x) := by
  obtain ⟨p, hp, heq⟩ := exists_polynomial_circle_convolution
    (degree_sawtoothErrorDerivativePolynomial_le n)
    (continuous_realChebyshevCircleFunction hf) (even_realChebyshevCircleFunction f)
  refine ⟨p, hp, fun x => ?_⟩
  have h := heq (x : AddCircle (2 * Real.pi))
  rw [integral_haarAddCircle_eq_inv_mul_intervalIntegral] at h
  have hterm : ∀ t : ℝ,
      (sawtoothErrorDerivativePolynomial n).eval ((fourier 1 (t : AddCircle (2 * Real.pi))).re) *
        realChebyshevCircleFunction f ((x : AddCircle (2 * Real.pi)) - (t : AddCircle (2 * Real.pi))) =
      (sawtoothErrorDerivativePolynomial n).eval (cos t) * f (cos (x - t)) := by
    intro t
    rw [← AddCircle.coe_sub, realChebyshevCircleFunction_coe]
    rw [show (fourier 1 (t : AddCircle (2 * Real.pi))).re = cos t by
      simpa only [Nat.cast_one, one_mul] using re_fourier_nat_coe_eq_cos 1 t]
  simp_rw [hterm] at h
  rw [show (fourier 1 (x : AddCircle (2 * Real.pi))).re = cos x by
    simpa only [Nat.cast_one, one_mul] using re_fourier_nat_coe_eq_cos 1 x] at h
  exact h

/-- The required sharp Jackson theorem on the unit interval: a degree-`n` algebraic
polynomial approximates every `L`-Lipschitz function with error at most `πL/(2(n+1))`.
Source: Arnold, numerical analysis, Section 1.2; operator rederivations `rt:jackson-theorem`.
Atlas `jackson-lipschitz` (unit-interval form). -/
theorem exists_degree_le_abs_sub_eval_le_jackson_unit {f : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) (n : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |f x - p.eval x| ≤ Real.pi * (L : ℝ) / (2 * (n + 1)) := by
  obtain ⟨p, hp, heq⟩ := exists_polynomial_jacksonPeriodicApprox hf.continuousOn n
  refine ⟨p, hp, fun x hx => ?_⟩
  have hper : Function.Periodic (fun t : ℝ => f (cos t)) (2 * Real.pi) := by
    intro t
    simp only [cos_add_two_pi]
  have h := abs_sub_jacksonPeriodicApprox_le (lipschitzWith_comp_cos hf) hper n (arccos x)
  rw [heq, cos_arccos hx.1 hx.2] at h
  exact h

end NLAlib
