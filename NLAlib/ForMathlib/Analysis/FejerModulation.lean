import NLAlib.ForMathlib.Analysis.FejerKernel
import NLAlib.ForMathlib.Analysis.FourierConvolution

/-! # A finite high-frequency Fejér certificate

Modulating a doubled Fejér kernel by frequency `4K` produces only frequencies
from `2K` through `6K`. Its absolute value is bounded by the positive doubled
Fejér kernel, whose normalized Haar integral is one.
-/

noncomputable section
open Complex Finset MeasureTheory
open scoped Real ComplexConjugate NLAlib.TwoPi

namespace NLAlib

/-- A natural cosine character at the doubled argument has doubled frequency. -/
theorem re_fourier_two_nsmul (k : ℕ) (t : AddCircle (2 * Real.pi)) :
    (fourier (k : ℤ) (2 • t)).re = (fourier ((2 * k : ℕ) : ℤ) t).re := by
  rw [two_nsmul, fourier_apply_add, ← fourier_add]
  rw [show (k : ℤ) + (k : ℤ) = ((2 * k : ℕ) : ℤ) by omega]

/-- Finite cosine product-to-sum for two natural Fourier frequencies. -/
theorem re_fourier_mul_re_fourier_nat (k l : ℕ) (hlk : l ≤ k)
    (t : AddCircle (2 * Real.pi)) :
    2 * ((fourier (k : ℤ) t).re * (fourier (l : ℤ) t).re) =
      (fourier ((k + l : ℕ) : ℤ) t).re + (fourier ((k - l : ℕ) : ℤ) t).re := by
  rw [Nat.cast_add, Nat.cast_sub hlk, sub_eq_add_neg, fourier_add, fourier_add, fourier_neg]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The actual high-frequency dual kernel used for absolute-value approximation. -/
def modulatedFejerCircleKernel (K : ℕ) (t : AddCircle (2 * Real.pi)) : ℝ :=
  (fourier ((4 * K : ℕ) : ℤ) t).re * fejerCircleKernel K (2 • t)

/-- The modulated positive Fejér kernel has a finite band of cosine frequencies.
The averaged-Dirichlet representation equals the usual triangular Fourier weights. -/
theorem modulatedFejerCircleKernel_eq_sum (K : ℕ) (t : AddCircle (2 * Real.pi)) :
    modulatedFejerCircleKernel K t = (K + 1 : ℝ)⁻¹ * ∑ m ∈ range (K + 1),
      ((fourier ((4 * K : ℕ) : ℤ) t).re + ∑ j ∈ range m,
        ((fourier ((4 * K + 2 * (j + 1) : ℕ) : ℤ) t).re +
          (fourier ((4 * K - 2 * (j + 1) : ℕ) : ℤ) t).re)) := by
  rw [modulatedFejerCircleKernel, fejerCircleKernel_eq_avg_dirichlet, ← mul_assoc,
    mul_comm _ ((K + 1 : ℝ)⁻¹), mul_assoc, mul_sum]
  congr 1
  apply sum_congr rfl
  intro m hm
  simp only [dirichletCircleKernel, re_fourier_two_nsmul, mul_add, mul_one,
    mul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hfreq : 2 * (j + 1) ≤ 4 * K := by have := mem_range.mp hm; have := mem_range.mp hj; omega
  have h := re_fourier_mul_re_fourier_nat (4 * K) (2 * (j + 1)) hfreq t
  norm_num only [Nat.mul_add, Nat.mul_one] at h
  linarith

/-- Positive natural cosine frequencies have normalized Haar mean zero. -/
theorem integral_re_fourier_nat_eq_zero {k : ℕ} (hk : 0 < k) :
    (∫ t : AddCircle (2 * Real.pi), (fourier (k : ℤ) t).re ∂AddCircle.haarAddCircle) = 0 := by
  simpa only [Nat.sub_add_cancel (Nat.succ_le_of_lt hk)] using integral_re_fourier_nat_succ_eq_zero (k - 1)

/-- Doubling the argument of the positive Fejér kernel preserves its normalized
mean. This uses the finite Fourier expansion, so no measure-map assumption is needed. -/
theorem integral_fejerCircleKernel_two_nsmul_eq_one (K : ℕ) :
    (∫ t : AddCircle (2 * Real.pi), fejerCircleKernel K (2 • t) ∂AddCircle.haarAddCircle) = 1 := by
  have hdir (m : ℕ) : (∫ t : AddCircle (2 * Real.pi),
      dirichletCircleKernel m (2 • t) ∂AddCircle.haarAddCircle) = 1 := by
    simp_rw [dirichletCircleKernel, re_fourier_two_nsmul]
    rw [integral_add (integrable_const _) (by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      fun_prop), integral_const_mul, integral_finsetSum _ (by
        intro k hk
        apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
        fun_prop)]
    have hz (k : ℕ) : (∫ t : AddCircle (2 * Real.pi),
        (fourier ((2 * (k + 1) : ℕ) : ℤ) t).re ∂AddCircle.haarAddCircle) = 0 :=
      integral_re_fourier_nat_eq_zero (by omega)
    simp only [hz]
    simp
  simp_rw [fejerCircleKernel_eq_avg_dirichlet]
  rw [integral_const_mul, integral_finsetSum _ (by
    intro m hm
    exact ((continuous_dirichletCircleKernel m).comp (continuous_id.nsmul 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [hdir, sum_const, card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  exact inv_mul_cancel₀ (by positivity)

/-- The finite high-frequency kernel has continuous circle values. -/
theorem continuous_modulatedFejerCircleKernel (K : ℕ) : Continuous (modulatedFejerCircleKernel K) := by
  exact (Complex.continuous_re.comp (fourier ((4 * K : ℕ) : ℤ)).continuous).mul
    ((continuous_fejerCircleKernel K).comp (continuous_id.nsmul 2))

/-- The positive Fejér majorant bounds the absolute value of the actual dual kernel. -/
theorem abs_modulatedFejerCircleKernel_le (K : ℕ) (t : AddCircle (2 * Real.pi)) :
    |modulatedFejerCircleKernel K t| ≤ fejerCircleKernel K (2 • t) := by
  rw [modulatedFejerCircleKernel, abs_mul, abs_of_nonneg (fejerCircleKernel_nonneg _ _)]
  have hcos : |(fourier ((4 * K : ℕ) : ℤ) t).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe _)
  exact (mul_le_mul_of_nonneg_right hcos (fejerCircleKernel_nonneg _ _)).trans_eq (one_mul _)

end NLAlib
