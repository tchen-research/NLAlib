import NLAlib.Polynomial.FunctionApproximation.AnalyticFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import NLAlib.ForMathlib.Analysis.FourierConvolution
/-!
# Real Chebyshev coefficients

The weighted integral and cosine integral definitions agree with the existing Joukowski
contour coefficients whenever the complex function restricts to the continuous real function
on `[-1,1]`. Coefficient identification needs no analyticity assumption.
-/

noncomputable section

open MeasureTheory Polynomial Polynomial.Chebyshev Set
open scoped Real NLAlib.TwoPi

namespace NLAlib

/-- Real Chebyshev coefficient with zeroth normalization `1/π` and positive normalization
`2/π`, using the arcsine weight. Source: Trefethen, ATAP, Chapter 3. -/
def chebyshevCoeff (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (if k = 0 then 1 else 2) / Real.pi *
    ∫ x, f x * (T ℝ (k : ℤ)).eval x ∂measureT

/-- The arcsine-measure coefficient is the classical weighted integral on `[-1,1]`.
Source: Trefethen, ATAP, Chapter 3. -/
theorem chebyshevCoeff_eq_weighted_integral (f : ℝ → ℝ) (k : ℕ) :
    chebyshevCoeff f k = (if k = 0 then 1 else 2) / Real.pi *
      ∫ x in (-1 : ℝ)..1, (f x * (T ℝ (k : ℤ)).eval x) * Real.sqrt (1 - x ^ 2)⁻¹ := by
  rw [chebyshevCoeff, integral_measureT]

/-- The weighted coefficient is the usual cosine coefficient, including the zeroth
normalization. Source: the cosine substitution for the Chebyshev weight. -/
theorem chebyshevCoeff_eq_cosine_integral (f : ℝ → ℝ) (k : ℕ) :
    chebyshevCoeff f k = (if k = 0 then 1 else 2) / Real.pi *
      ∫ θ in 0..Real.pi, f (Real.cos θ) * Real.cos ((k : ℝ) * θ) := by
  rw [chebyshevCoeff, integral_measureT_eq_integral_cos]
  simp_rw [T_real_cos, Int.cast_natCast]

/-- Reflection of the cosine pullback halves its full-period integral. Source: the
symmetry `cos (2π - θ) = cos θ` and adjacent interval additivity. -/
theorem integral_chebyshev_cosine_full_period {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1)) (k : ℕ) :
    (∫ θ in 0..2 * Real.pi, f (Real.cos θ) * (T ℝ (k : ℤ)).eval (Real.cos θ)) =
      2 * ∫ θ in 0..Real.pi, f (Real.cos θ) * (T ℝ (k : ℤ)).eval (Real.cos θ) := by
  let g : ℝ → ℝ := fun θ => f (Real.cos θ) * (T ℝ (k : ℤ)).eval (Real.cos θ)
  have hfc : Continuous (fun θ => f (Real.cos θ)) :=
    hf.comp_continuous Real.continuous_cos (fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
  have hg : Continuous g := hfc.mul ((T ℝ (k : ℤ)).continuous.comp Real.continuous_cos)
  have hreflect := intervalIntegral.integral_comp_sub_left (f := g)
    (a := Real.pi) (b := 2 * Real.pi) (2 * Real.pi)
  have hsym : ∀ θ, g (2 * Real.pi - θ) = g θ := by
    intro θ
    simp only [g, Real.cos_two_pi_sub]
  simp_rw [hsym] at hreflect
  have heq : (∫ θ in Real.pi..2 * Real.pi, g θ) = ∫ θ in 0..Real.pi, g θ := by
    simpa only [sub_self, show 2 * Real.pi - Real.pi = Real.pi by ring] using hreflect
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 Real.pi) (hg.intervalIntegrable Real.pi (2 * Real.pi))
  change (∫ θ in 0..2 * Real.pi, g θ) = 2 * ∫ θ in 0..Real.pi, g θ
  rw [← hadd, heq]
  ring

/-- A continuous real restriction identifies the real contour coefficient with the
weighted real Chebyshev coefficient. No holomorphic extension is needed for this equality.
Source: Trefethen, ATAP, Chapters 3 and 8. -/
theorem chebyshevAnalyticCoeff_eq_chebyshevCoeff {F : ℂ → ℂ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1))
    (hF : ∀ x ∈ Icc (-1 : ℝ) 1, F x = (f x : ℂ)) (k : ℕ) :
    chebyshevAnalyticCoeff F k = chebyshevCoeff f k := by
  have hfc : Continuous (fun θ => f (Real.cos θ)) :=
    hf.comp_continuous Real.continuous_cos (fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
  have hcircle : ∀ θ : ℝ, chebyshevCircleFunction F (θ : AddCircle (2 * Real.pi)) =
      (f (Real.cos θ) : ℂ) := by
    intro θ
    rw [chebyshevCircleFunction_coe_eq_cos]
    exact hF _ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hI : IntervalIntegrable (fun θ : ℝ =>
      fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) * (f (Real.cos θ) : ℂ))
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact ((fourier (-(k : ℤ))).continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))).mul
      (Complex.continuous_ofReal.comp hfc)
  have hreal := Complex.reCLM.intervalIntegral_comp_comm hI
  change (∫ θ in 0..2 * Real.pi,
      (fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) * (f (Real.cos θ) : ℂ)).re) =
    (∫ θ in 0..2 * Real.pi,
      fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) * (f (Real.cos θ) : ℂ)).re at hreal
  have hterm : ∀ θ : ℝ,
      (fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) * (f (Real.cos θ) : ℂ)).re =
        f (Real.cos θ) * (T ℝ (k : ℤ)).eval (Real.cos θ) := by
    intro θ
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, fourier_neg, Complex.conj_re, re_fourier_nat_coe_eq_cos,
      T_real_cos, Int.cast_natCast]
    ring
  simp_rw [hterm] at hreal
  rw [chebyshevAnalyticCoeff, chebyshevComplexCoeff_eq_fourierCoeff,
    fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
  simp_rw [hcircle]
  have hnormal (z : ℂ) :
      ((if k = 0 then (1 : ℂ) else 2) * ((1 / (2 * Real.pi) : ℝ) • z)).re =
        (if k = 0 then (1 : ℝ) else 2) * (1 / (2 * Real.pi)) * z.re := by
    split_ifs <;> simp [Complex.mul_re, Complex.real_smul]
    ring
  rw [hnormal]
  simp only [smul_eq_mul]
  rw [← hreal, integral_chebyshev_cosine_full_period hf k, chebyshevCoeff,
    integral_measureT_eq_integral_cos]
  split_ifs <;> ring

/-- The complex contour coefficient itself is the real weighted coefficient when the
restriction is real and continuous. Source: even-real Fourier symmetry and the contour bridge. -/
theorem chebyshevComplexCoeff_eq_ofReal_chebyshevCoeff {F : ℂ → ℂ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1) 1))
    (hF : ∀ x ∈ Icc (-1 : ℝ) 1, F x = (f x : ℂ)) (k : ℕ) :
    chebyshevComplexCoeff F k = (chebyshevCoeff f k : ℂ) := by
  let g : AddCircle (2 * Real.pi) → ℝ := fun θ => (chebyshevCircleFunction F θ).re
  have hreal : chebyshevCircleFunction F = fun θ => (g θ : ℂ) := by
    funext θ
    induction θ using QuotientAddGroup.induction_on with
    | H θ =>
      change chebyshevCircleFunction F (θ : AddCircle (2 * Real.pi)) =
        ((chebyshevCircleFunction F (θ : AddCircle (2 * Real.pi))).re : ℂ)
      rw [chebyshevCircleFunction_coe_eq_cos, hF _ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩]
      simp
  have heven : ∀ θ, g (-θ) = g θ := by
    intro θ
    simp only [g, chebyshevCircleFunction_neg]
  have him := im_fourierCoeff_of_even_real g heven (k : ℤ)
  apply Complex.ext
  · simpa only [Complex.ofReal_re, chebyshevAnalyticCoeff] using
      chebyshevAnalyticCoeff_eq_chebyshevCoeff hf hF k
  · rw [chebyshevComplexCoeff_eq_fourierCoeff, hreal]
    split_ifs <;> simp [Complex.mul_im, him]

end NLAlib
