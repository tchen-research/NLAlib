import NLAlib.Polynomial.FunctionApproximation.JacksonDamping
import NLAlib.ForMathlib.Analysis.FourierAutocorrelation
import NLAlib.ForMathlib.Analysis.FejerKernel
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The explicit positive Chebyshev Jackson kernel

The sine-vector squared Fourier sum gives a genuine nonnegative kernel.
Symmetrizing its circle translates gives precisely the finite Chebyshev
kernel with the explicit Jackson damping coefficients.
Source: Musco--Musco--Shah--Urschel--West, arXiv:2605.31430v2, Section 2.2.
Atlas: `tensor-chebyshev-kernel-measure` (partial).
-/

noncomputable section

open Real Finset MeasureTheory Polynomial.Chebyshev
open scoped ComplexConjugate

namespace NLAlib

open scoped NLAlib.TwoPi

/-- The actual finite normalized Chebyshev Jackson kernel. -/
def chebyshevJacksonKernel (M : ℕ) (x r : ℝ) : ℝ :=
  ∑ j ∈ range (M + 1), chebyshevJacksonDamping M j * normalizedChebyshev j x *
    normalizedChebyshev j r

/-- Its positive circle kernel is the normalized squared sine-weighted character sum. -/
def chebyshevJacksonCircleKernel (M : ℕ) (t : AddCircle (2 * π)) : ℝ :=
  (2 / (M + 2 : ℝ)) * Complex.normSq
    (∑ l ∈ range (M + 1), (chebyshevJacksonSineWeight M l : ℂ) * fourier (l : ℤ) t)

/-- The circle kernel is nonnegative by its actual squared-norm construction. -/
theorem chebyshevJacksonCircleKernel_nonneg (M : ℕ) (t : AddCircle (2 * π)) :
    0 ≤ chebyshevJacksonCircleKernel M t :=
  mul_nonneg (by positivity) (Complex.normSq_nonneg _)

/-- Autocorrelation gives the exact finite cosine expansion of the circle kernel. -/
theorem chebyshevJacksonCircleKernel_eq_sum (M : ℕ) (t : AddCircle (2 * π)) :
    chebyshevJacksonCircleKernel M t = 1 + 2 * ∑ j ∈ range M,
      chebyshevJacksonDamping M (j + 1) * (fourier ((j + 1 : ℕ) : ℤ) t).re := by
  rw [chebyshevJacksonCircleKernel, normSq_sum_real_mul_fourier_eq_autocorrelation,
    sum_chebyshevJacksonSineWeight_sq, sum_range_succ]
  simp only [Nat.sub_self, sum_range_zero, zero_mul, add_zero]
  have hnorm : 2 / (M + 2 : ℝ) * ((M + 2 : ℝ) / 2) = 1 := by
    field_simp [show (M + 2 : ℝ) ≠ 0 by positivity]
  rw [mul_add, hnorm]
  congr 1
  rw [← mul_assoc, mul_comm (2 / (M + 2 : ℝ)) 2, mul_assoc, mul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [chebyshevJacksonDamping_eq_autocorrelation M (j + 1) (by
    have := mem_range.mp hj
    omega)]
  ring_nf

/-- Evaluating the circle kernel at a real angle gives its ordinary cosine expansion. -/
theorem chebyshevJacksonCircleKernel_coe_eq_sum (M : ℕ) (t : ℝ) :
    chebyshevJacksonCircleKernel M (t : AddCircle (2 * π)) =
      1 + 2 * ∑ j ∈ range M, chebyshevJacksonDamping M (j + 1) * cos (((j + 1 : ℕ) : ℝ) * t) := by
  rw [chebyshevJacksonCircleKernel_eq_sum]
  simp_rw [re_fourier_nat_coe_eq_cos]

/-- The normalized polynomial kernel has the usual finite cosine-product expansion. -/
theorem chebyshevJacksonKernel_cos_eq_sum (M : ℕ) (a b : ℝ) :
    chebyshevJacksonKernel M (cos a) (cos b) =
      1 / π + (2 / π) * ∑ j ∈ range M,
        chebyshevJacksonDamping M (j + 1) * cos (((j + 1 : ℕ) : ℝ) * a) *
          cos (((j + 1 : ℕ) : ℝ) * b) := by
  have hterm (j : ℕ) :
      chebyshevJacksonDamping M j * normalizedChebyshev j (cos a) * normalizedChebyshev j (cos b) =
        ((if j = 0 then 1 else 2) / π) * chebyshevJacksonDamping M j *
          cos ((j : ℝ) * a) * cos ((j : ℝ) * b) := by
    rw [normalizedChebyshev_cos, normalizedChebyshev_cos]
    have h := normalizedChebyshevWeight_sq j
    calc
      _ = normalizedChebyshevWeight j ^ 2 * chebyshevJacksonDamping M j *
          cos ((j : ℝ) * a) * cos ((j : ℝ) * b) := by ring
      _ = _ := by rw [h]
  simp_rw [chebyshevJacksonKernel, hterm]
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, cos_zero, chebyshevJacksonDamping_zero,
    if_true, mul_one, Nat.add_one_ne_zero, if_false]
  rw [mul_sum]
  simp only [mul_assoc]
  rw [add_comm]

/-- The Chebyshev kernel is the sum of two translates of the positive circle
kernel. This is an equality of the actual finite kernels. -/
theorem chebyshevJacksonKernel_cos_eq_circle (M : ℕ) (a b : ℝ) :
    chebyshevJacksonKernel M (cos a) (cos b) =
      (chebyshevJacksonCircleKernel M ((a - b : ℝ) : AddCircle (2 * π)) +
        chebyshevJacksonCircleKernel M ((a + b : ℝ) : AddCircle (2 * π))) / (2 * π) := by
  rw [chebyshevJacksonKernel_cos_eq_sum, chebyshevJacksonCircleKernel_coe_eq_sum,
    chebyshevJacksonCircleKernel_coe_eq_sum]
  have h (j : ℕ) :
      cos (((j + 1 : ℕ) : ℝ) * (a - b)) + cos (((j + 1 : ℕ) : ℝ) * (a + b)) =
        2 * (cos (((j + 1 : ℕ) : ℝ) * a) * cos (((j + 1 : ℕ) : ℝ) * b)) := by
    rw [mul_sub, mul_add, cos_sub, cos_add]
    ring
  have hs : (∑ j ∈ range M, chebyshevJacksonDamping M (j + 1) *
      cos (((j + 1 : ℕ) : ℝ) * (a - b))) +
      (∑ j ∈ range M, chebyshevJacksonDamping M (j + 1) * cos (((j + 1 : ℕ) : ℝ) * (a + b))) =
        2 * ∑ j ∈ range M, chebyshevJacksonDamping M (j + 1) *
          cos (((j + 1 : ℕ) : ℝ) * a) * cos (((j + 1 : ℕ) : ℝ) * b) := by
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro j _
    rw [← mul_add, h]
    ring
  field_simp
  nlinarith [hs]

/-- The explicit finite Jackson kernel is nonnegative on the entire closed square. -/
theorem chebyshevJacksonKernel_nonneg (M : ℕ) {x r : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hr : r ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ chebyshevJacksonKernel M x r := by
  rw [← cos_arccos hx.1 hx.2, ← cos_arccos hr.1 hr.2, chebyshevJacksonKernel_cos_eq_circle]
  exact div_nonneg (add_nonneg (chebyshevJacksonCircleKernel_nonneg M _)
    (chebyshevJacksonCircleKernel_nonneg M _)) (by positivity)

/-- The explicit Jackson kernel is symmetric. -/
theorem chebyshevJacksonKernel_symm (M : ℕ) (x r : ℝ) :
    chebyshevJacksonKernel M x r = chebyshevJacksonKernel M r x := by
  apply sum_congr rfl
  intro j _
  ring

/-- Every normalized Chebyshev basis function is continuous on the real line. -/
@[fun_prop] theorem continuous_normalizedChebyshev (j : ℕ) : Continuous (normalizedChebyshev j) :=
  continuous_const.mul (T ℝ (j : ℤ)).continuous

/-- The normalized Chebyshev basis is orthonormal for the actual arcsine measure. -/
theorem integral_normalizedChebyshev_mul (j k : ℕ) :
    (∫ x, normalizedChebyshev j x * normalizedChebyshev k x ∂measureT) =
      if j = k then 1 else 0 := by
  rw [integral_measureT_eq_integral_cos, intervalIntegral.integral_of_le pi_pos.le]
  exact integral_normalizedChebyshev_cos_mul j k

/-- The finite Jackson kernel is continuous in its integrated variable. -/
@[fun_prop] theorem continuous_chebyshevJacksonKernel (M : ℕ) (r : ℝ) :
    Continuous (fun x => chebyshevJacksonKernel M x r) := by
  unfold chebyshevJacksonKernel
  exact continuous_finsetSum _ (fun j _ =>
    (continuous_const.mul (continuous_normalizedChebyshev j)).mul continuous_const)

/-- The kernel acts diagonally on the normalized basis, including the first
vanishing frequency just beyond its degree. -/
theorem integral_chebyshevJacksonKernel_mul_normalizedChebyshev
    (M k : ℕ) (hk : k ≤ M + 1) (r : ℝ) :
    (∫ x, chebyshevJacksonKernel M x r * normalizedChebyshev k x ∂measureT) =
      chebyshevJacksonDamping M k * normalizedChebyshev k r := by
  have hterm (j : ℕ) (x : ℝ) :
      chebyshevJacksonDamping M j * normalizedChebyshev j x *
        normalizedChebyshev j r * normalizedChebyshev k x =
      (chebyshevJacksonDamping M j * normalizedChebyshev j r) *
        (normalizedChebyshev j x * normalizedChebyshev k x) := by
    ring
  simp_rw [chebyshevJacksonKernel, sum_mul, hterm]
  rw [integral_finsetSum _ (fun j _ => integrable_measureT (by
    exact ((continuous_const.mul ((continuous_normalizedChebyshev j).mul
      (continuous_normalizedChebyshev k))).continuousOn)))]
  simp_rw [integral_const_mul, integral_normalizedChebyshev_mul]
  by_cases hkM : k ≤ M
  · rw [sum_eq_single k]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hnot
      exact False.elim (hnot (mem_range.mpr (by omega)))
  · have heq : k = M + 1 := by omega
    subst k
    rw [chebyshevJacksonDamping_succ, zero_mul]
    apply sum_eq_zero
    intro j hj
    have hne : j ≠ M + 1 := by have := mem_range.mp hj; omega
    simp [hne]

/-- The explicit positive Jackson kernel has total mass exactly one. -/
theorem integral_chebyshevJacksonKernel (M : ℕ) (r : ℝ) :
    (∫ x, chebyshevJacksonKernel M x r ∂measureT) = 1 := by
  have h := integral_chebyshevJacksonKernel_mul_normalizedChebyshev M 0 (by omega) r
  simp only [normalizedChebyshev_zero, chebyshevJacksonDamping_zero, one_mul] at h
  rw [integral_mul_const] at h
  have hp : sqrt π ≠ 0 := ne_of_gt (sqrt_pos.2 pi_pos)
  field_simp at h
  exact h

/-- The normalization of every Chebyshev mode is strictly positive. -/
theorem normalizedChebyshevWeight_pos (k : ℕ) : 0 < normalizedChebyshevWeight k := by
  unfold normalizedChebyshevWeight
  apply sqrt_pos.2
  split_ifs <;> positivity

/-- The kernel acts diagonally also in the ordinary, unnormalized Chebyshev basis. -/
theorem integral_chebyshevJacksonKernel_mul_T (M k : ℕ) (hk : k ≤ M + 1) (r : ℝ) :
    (∫ x, chebyshevJacksonKernel M x r * (T ℝ (k : ℤ)).eval x ∂measureT) =
      chebyshevJacksonDamping M k * (T ℝ (k : ℤ)).eval r := by
  have h := integral_chebyshevJacksonKernel_mul_normalizedChebyshev M k hk r
  simp only [normalizedChebyshev] at h
  have hfun (x : ℝ) : chebyshevJacksonKernel M x r *
      (normalizedChebyshevWeight k * (T ℝ (k : ℤ)).eval x) =
      normalizedChebyshevWeight k * (chebyshevJacksonKernel M x r * (T ℝ (k : ℤ)).eval x) := by ring
  simp_rw [hfun] at h
  rw [integral_const_mul] at h
  apply mul_left_cancel₀ (ne_of_gt (normalizedChebyshevWeight_pos k))
  exact h.trans (by ring)

/-- The first moment of the explicit Jackson kernel is its first damping coefficient. -/
theorem integral_chebyshevJacksonKernel_mul_id (M : ℕ) (r : ℝ) :
    (∫ x, chebyshevJacksonKernel M x r * x ∂measureT) =
      chebyshevJacksonDamping M 1 * r := by
  simpa using integral_chebyshevJacksonKernel_mul_T M 1 (by omega) r

/-- The second moment of the explicit Jackson kernel, valid also at cutoff one. -/
theorem integral_chebyshevJacksonKernel_mul_sq {M : ℕ} (hM : 1 ≤ M) (r : ℝ) :
    (∫ x, chebyshevJacksonKernel M x r * x ^ 2 ∂measureT) =
      (1 + chebyshevJacksonDamping M 2 * (2 * r ^ 2 - 1)) / 2 := by
  have h := integral_chebyshevJacksonKernel_mul_T M 2 (by omega) r
  simp only [Nat.cast_ofNat, T_two, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at h
  have hfun (x : ℝ) : chebyshevJacksonKernel M x r * (2 * x ^ 2 - 1) =
      2 * (chebyshevJacksonKernel M x r * x ^ 2) - chebyshevJacksonKernel M x r := by ring
  simp_rw [hfun] at h
  rw [integral_sub (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop)),
    integral_const_mul, integral_chebyshevJacksonKernel] at h
  linarith

/-- The exact centered second moment of the finite Jackson kernel. -/
theorem integral_chebyshevJacksonKernel_mul_sub_sq {M : ℕ} (hM : 1 ≤ M) (r : ℝ) :
    (∫ x, chebyshevJacksonKernel M x r * (x - r) ^ 2 ∂measureT) =
      (1 - chebyshevJacksonDamping M 2) / 2 +
        r ^ 2 * (chebyshevJacksonDamping M 2 - 2 * chebyshevJacksonDamping M 1 + 1) := by
  have hfun (x : ℝ) : chebyshevJacksonKernel M x r * (x - r) ^ 2 =
      chebyshevJacksonKernel M x r * x ^ 2 -
        (2 * r) * (chebyshevJacksonKernel M x r * x) + r ^ 2 * chebyshevJacksonKernel M x r := by ring
  simp_rw [hfun]
  rw [integral_add (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop)),
    integral_sub (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop)),
    integral_const_mul, integral_const_mul, integral_chebyshevJacksonKernel,
    integral_chebyshevJacksonKernel_mul_sq hM, integral_chebyshevJacksonKernel_mul_id]
  ring

/-- The quadratic displacement of the positive Jackson kernel is at most the
square of the sine of its defining angle. -/
theorem integral_chebyshevJacksonKernel_mul_sub_sq_le {M : ℕ} (hM : 1 ≤ M) (r : ℝ) :
    (∫ x, chebyshevJacksonKernel M x r * (x - r) ^ 2 ∂measureT) ≤
      sin (chebyshevJacksonAngle M) ^ 2 := by
  let θ := chebyshevJacksonAngle M
  have hc : (1 : ℝ) / 2 ≤ cos θ := by
    rw [← cos_pi_div_three]
    exact cos_le_cos_of_nonneg_of_le_pi (chebyshevJacksonAngle_pos M).le
      (by linarith [pi_pos]) (chebyshevJacksonAngle_le_pi_div_three hM)
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hcM : 1 ≤ ((M : ℝ) + 1) * cos θ := by
    have h := mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ M + 1)
      (by linarith : 0 ≤ cos θ)
    linarith
  have hcoef : chebyshevJacksonDamping M 2 - 2 * chebyshevJacksonDamping M 1 + 1 =
      2 * (cos θ - 1) * (((M : ℝ) + 1) * cos θ - 1) / (M + 2) := by
    rw [chebyshevJacksonDamping_two, chebyshevJacksonDamping_one, cos_two_mul]
    dsimp [θ]
    field_simp
    ring
  have hcoefneg : chebyshevJacksonDamping M 2 - 2 * chebyshevJacksonDamping M 1 + 1 ≤ 0 := by
    rw [hcoef]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [cos_le_one θ]) (by linarith)) (by positivity)
  have hconstant : (1 - chebyshevJacksonDamping M 2) / 2 =
      (((M : ℝ) + 1) / (M + 2)) * sin θ ^ 2 := by
    rw [chebyshevJacksonDamping_two, cos_two_mul, cos_sq']
    dsimp [θ]
    field_simp
    ring
  have hratio : ((M : ℝ) + 1) / (M + 2) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  rw [integral_chebyshevJacksonKernel_mul_sub_sq hM]
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) hcoefneg
  have hconst := mul_le_mul_of_nonneg_right hratio (sq_nonneg (sin θ))
  rw [one_mul] at hconst
  rw [hconstant]
  linarith

/-- The arcsine measure is supported on the closed approximation interval. -/
theorem ae_mem_Icc_measureT : ∀ᵐ x ∂measureT, x ∈ Set.Icc (-1 : ℝ) 1 := by
  have h : ∀ᵐ x ∂measureT, x ∈ Set.Ioc (-1 : ℝ) 1 := by
    unfold measureT
    exact ae_restrict_mem measurableSet_Ioc
  exact h.mono fun _ hx => ⟨hx.1.le, hx.2⟩

/-- The first absolute displacement is bounded by the Jackson angle's sine.
This follows from the exact second moment and positivity, without any boundary limits. -/
theorem integral_chebyshevJacksonKernel_mul_abs_sub_le_sin {M : ℕ} (hM : 1 ≤ M)
    {r : ℝ} (hr : r ∈ Set.Icc (-1 : ℝ) 1) :
    (∫ x, chebyshevJacksonKernel M x r * |x - r| ∂measureT) ≤
      sin (chebyshevJacksonAngle M) := by
  let S := sin (chebyshevJacksonAngle M)
  have hS : 0 < S := sin_chebyshevJacksonAngle_pos M
  have hi : ∀ᵐ x ∂measureT,
      2 * S * (chebyshevJacksonKernel M x r * |x - r|) ≤
      chebyshevJacksonKernel M x r * (x - r) ^ 2 + S ^ 2 * chebyshevJacksonKernel M x r := by
    filter_upwards [ae_mem_Icc_measureT] with x hx
    have hp : 2 * S * |x - r| ≤ (x - r) ^ 2 + S ^ 2 := by
      nlinarith [sq_nonneg (|x - r| - S), sq_abs (x - r)]
    have h := mul_le_mul_of_nonneg_left hp (chebyshevJacksonKernel_nonneg M hx hr)
    nlinarith
  have h := integral_mono_ae (integrable_measureT (by fun_prop))
    (integrable_measureT (by fun_prop)) hi
  rw [integral_const_mul, integral_add (integrable_measureT (by fun_prop))
    (integrable_measureT (by fun_prop)), integral_const_mul, integral_chebyshevJacksonKernel] at h
  have hsq := integral_chebyshevJacksonKernel_mul_sub_sq_le hM r
  change _ ≤ S ^ 2 at hsq
  change _ ≤ S
  nlinarith

/-- The positive kernel satisfies the advertised explicit `6/M` displacement bound. -/
theorem integral_chebyshevJacksonKernel_mul_abs_sub_le {M : ℕ} (hM : 1 ≤ M)
    {r : ℝ} (hr : r ∈ Set.Icc (-1 : ℝ) 1) :
    (∫ x, chebyshevJacksonKernel M x r * |x - r| ∂measureT) ≤ 6 / M := by
  refine (integral_chebyshevJacksonKernel_mul_abs_sub_le_sin hM hr).trans
    ((sin_le (chebyshevJacksonAngle_pos M).le).trans ?_)
  unfold chebyshevJacksonAngle
  have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  apply (div_le_div_iff₀ (by positivity) hMp).2
  nlinarith [pi_lt_four]

/-- Every retained damping coefficient lies below one; positivity and normalization
of the actual kernel prove this bound, including its first zero frequency. -/
theorem chebyshevJacksonDamping_le_one {M j : ℕ} (hj : j ≤ M + 1) :
    chebyshevJacksonDamping M j ≤ 1 := by
  have h : ∀ᵐ x ∂measureT, chebyshevJacksonKernel M x 1 * (T ℝ (j : ℤ)).eval x ≤
      chebyshevJacksonKernel M x 1 := by
    filter_upwards [ae_mem_Icc_measureT] with x hx
    have hT := (abs_le.mp (abs_eval_T_real_le_one (j : ℤ) (abs_le.mpr hx))).2
    exact (mul_le_mul_of_nonneg_left hT (chebyshevJacksonKernel_nonneg M hx (by norm_num))).trans_eq
      (mul_one _)
  have hi := integral_mono_ae (integrable_measureT (by fun_prop))
    (integrable_measureT (by fun_prop)) h
  simpa only [integral_chebyshevJacksonKernel_mul_T M j hj 1, T_eval_one,
    mul_one, integral_chebyshevJacksonKernel] using hi

/-- The explicit Jackson multipliers are genuine coefficient contractions. -/
theorem chebyshevJacksonDamping_mem_Icc {M j : ℕ} (hj : j ≤ M + 1) :
    chebyshevJacksonDamping M j ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨chebyshevJacksonDamping_nonneg hj, chebyshevJacksonDamping_le_one hj⟩

end NLAlib
