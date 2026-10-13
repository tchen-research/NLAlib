import NLAlib.ForMathlib.Analysis.FourierCircle
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Positive Fejér kernels on the circle

The squared norm of a finite character sum is the sum of the finite Dirichlet
kernels. Its normalized form is nonnegative and has Haar integral one.
-/

noncomputable section

open Complex Finset MeasureTheory
open scoped Real ComplexConjugate

namespace NLAlib

open scoped NLAlib.TwoPi

/-- The real Dirichlet kernel with frequencies from `-n` through `n`.
Source: finite Fourier sums; helper for `fejer-chebyshev-means`. -/
def dirichletCircleKernel (n : ℕ) (t : AddCircle (2 * Real.pi)) : ℝ :=
  1 + 2 * ∑ k ∈ range n, (fourier ((k + 1 : ℕ) : ℤ) t).re

/-- The normalized nonnegative Fejér kernel is the squared finite character sum.
Source: Fejér's finite kernel identity, ATAP Exercise 6.6. -/
def fejerCircleKernel (n : ℕ) (t : AddCircle (2 * Real.pi)) : ℝ :=
  (n + 1 : ℝ)⁻¹ * Complex.normSq (∑ j ∈ range (n + 1), fourier (j : ℤ) t)

/-- The cross term in extending a character sum is the next finite cosine sum.
Source: finite Fourier characters; helper for `fejer-chebyshev-means`. -/
theorem re_sum_fourier_mul_conj_eq_sum (n : ℕ) (t : AddCircle (2 * Real.pi)) :
    ((∑ j ∈ range n, fourier (j : ℤ) t) * conj (fourier (n : ℤ) t)).re =
      ∑ j ∈ range n, (fourier ((j + 1 : ℕ) : ℤ) t).re := by
  rw [sum_mul, Complex.re_sum]
  have hterm : ∀ j ∈ range n,
      (fourier (j : ℤ) t * conj (fourier (n : ℤ) t)).re =
        (fourier (((n - 1 - j) + 1 : ℕ) : ℤ) t).re := by
    intro j hj
    have hjn : j < n := mem_range.mp hj
    rw [← fourier_neg, ← fourier_add]
    have hidx : (j : ℤ) + -(n : ℤ) = -(((n - 1 - j) + 1 : ℕ) : ℤ) := by
      omega
    rw [hidx, fourier_neg, Complex.conj_re]
  rw [sum_congr rfl hterm]
  exact sum_range_reflect (fun j => (fourier ((j + 1 : ℕ) : ℤ) t).re) n

/-- A squared finite Fourier sum equals the sum of successive Dirichlet kernels.
Source: Fejér's finite kernel identity, ATAP Exercise 6.6;
operator rederivations `polyseries:fejerkernel`. -/
theorem normSq_sum_fourier_eq_sum_dirichletCircleKernel (n : ℕ)
    (t : AddCircle (2 * Real.pi)) :
    Complex.normSq (∑ j ∈ range n, fourier (j : ℤ) t) =
      ∑ m ∈ range n, dirichletCircleKernel m t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Complex.normSq_add, ih, sum_range_succ,
      re_sum_fourier_mul_conj_eq_sum]
    have hn : Complex.normSq (fourier (n : ℤ) t) = 1 := by
      rw [Complex.normSq_eq_norm_sq, show ‖fourier (n : ℤ) t‖ = (1 : ℝ) from Circle.norm_coe _]
      norm_num
    rw [hn]
    simp only [dirichletCircleKernel]
    ring

/-- The positive Fejér kernel is the average of the finite Dirichlet kernels.
Source: Fejér's finite kernel identity, ATAP Exercise 6.6. -/
theorem fejerCircleKernel_eq_avg_dirichlet (n : ℕ) (t : AddCircle (2 * Real.pi)) :
    fejerCircleKernel n t = (n + 1 : ℝ)⁻¹ * ∑ m ∈ range (n + 1), dirichletCircleKernel m t := by
  rw [fejerCircleKernel, normSq_sum_fourier_eq_sum_dirichletCircleKernel]

/-- The Fejér kernel is nonnegative at every circle argument.
Source: Fejér's squared-norm formula, ATAP Exercise 6.6. -/
theorem fejerCircleKernel_nonneg (n : ℕ) (t : AddCircle (2 * Real.pi)) :
    0 ≤ fejerCircleKernel n t := by
  unfold fejerCircleKernel
  exact mul_nonneg (inv_nonneg.mpr (by positivity)) (Complex.normSq_nonneg _)

/-- Every finite Dirichlet kernel is continuous on the circle.
Source: finite Fourier characters; helper for `fejer-chebyshev-means`. -/
theorem continuous_dirichletCircleKernel (n : ℕ) : Continuous (dirichletCircleKernel n) := by
  unfold dirichletCircleKernel
  fun_prop

/-- Every Fejér kernel is continuous on the circle.
Source: finite Fourier characters; helper for `fejer-chebyshev-means`. -/
theorem continuous_fejerCircleKernel (n : ℕ) : Continuous (fejerCircleKernel n) := by
  have heq : fejerCircleKernel n = fun t =>
      (n + 1 : ℝ)⁻¹ * ∑ m ∈ range (n + 1), dirichletCircleKernel m t :=
    funext (fejerCircleKernel_eq_avg_dirichlet n)
  rw [heq]
  exact continuous_const.mul (continuous_finsetSum _ (fun m hm => continuous_dirichletCircleKernel m))

/-- A positive-frequency cosine character has Haar integral zero.
Source: Mathlib Fourier orthogonality; helper for `fejer-chebyshev-means`. -/
theorem integral_re_fourier_nat_succ_eq_zero (k : ℕ) :
    (∫ t : AddCircle (2 * Real.pi), (fourier ((k + 1 : ℕ) : ℤ) t).re
      ∂AddCircle.haarAddCircle) = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 2 * Real.pi) 0) (-((k + 1 : ℕ) : ℤ))
  have hI : Integrable (fun t : AddCircle (2 * Real.pi) => fourier ((k + 1 : ℕ) : ℤ) t)
      AddCircle.haarAddCircle := (fourier ((k + 1 : ℕ) : ℤ)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hR := Complex.reCLM.integral_comp_comm hI
  change (∫ t : AddCircle (2 * Real.pi), (fourier ((k + 1 : ℕ) : ℤ) t).re
    ∂AddCircle.haarAddCircle) = (∫ t : AddCircle (2 * Real.pi),
      fourier ((k + 1 : ℕ) : ℤ) t ∂AddCircle.haarAddCircle).re at hR
  rw [hR]
  have hzero : (∫ t : AddCircle (2 * Real.pi),
      fourier ((k + 1 : ℕ) : ℤ) t ∂AddCircle.haarAddCircle) = 0 := by
    have hne : -((k + 1 : ℕ) : ℤ) ≠ 0 := by omega
    simpa only [fourierCoeff, neg_neg, fourier_zero, ContinuousMap.coe_one,
      Pi.one_apply, smul_eq_mul, mul_one, Pi.single_apply, if_neg hne,
      if_neg (Ne.symm hne)] using h
  rw [hzero]
  rfl

/-- Each Dirichlet kernel has normalized Haar integral one.
Source: Fourier orthogonality; helper for `fejer-chebyshev-means`. -/
theorem integral_dirichletCircleKernel_eq_one (n : ℕ) :
    (∫ t : AddCircle (2 * Real.pi), dirichletCircleKernel n t ∂AddCircle.haarAddCircle) = 1 := by
  unfold dirichletCircleKernel
  rw [integral_add (integrable_const _) (by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      fun_prop), integral_const_mul]
  rw [integral_finsetSum (f := fun k t => (fourier ((k + 1 : ℕ) : ℤ) t).re) _ (fun k hk =>
      (Complex.continuous_re.comp (fourier ((k + 1 : ℕ) : ℤ)).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
  simp_rw [integral_re_fourier_nat_succ_eq_zero]
  simp

/-- The Fejér kernel has normalized Haar integral one.
Source: Fourier orthogonality and finite Fejér identity, ATAP Exercise 6.6. -/
theorem integral_fejerCircleKernel_eq_one (n : ℕ) :
    (∫ t : AddCircle (2 * Real.pi), fejerCircleKernel n t ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [fejerCircleKernel_eq_avg_dirichlet]
  rw [integral_const_mul, integral_finsetSum _ (fun m hm =>
    (continuous_dirichletCircleKernel m).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [integral_dirichletCircleKernel_eq_one, sum_const, card_range, nsmul_eq_mul,
    mul_one, Nat.cast_add, Nat.cast_one]
  exact inv_mul_cancel₀ (by positivity)

end NLAlib
