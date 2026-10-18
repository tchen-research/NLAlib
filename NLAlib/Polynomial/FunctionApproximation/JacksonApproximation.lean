import NLAlib.Polynomial.FunctionApproximation.JacksonKernel

/-!
# Coefficient-controlled positive Jackson approximation

The actual finite polynomial has the explicit Jackson multipliers in `[0,1]`.
Its integral against the positive kernel proves uniform Lipschitz approximation.
Source: Musco--Musco--Shah--Urschel--West, arXiv:2605.31430v2, Lemma 2.3.
Atlas: `tensor-chebyshev-kernel-measure`, `chebyshev-moment-wasserstein` (partial).
-/

noncomputable section

open Real Finset MeasureTheory Polynomial Polynomial.Chebyshev Set

namespace NLAlib

/-- The actual degree-`M` Jackson polynomial with damped Chebyshev coefficients. -/
def chebyshevJacksonApprox (f : ℝ → ℝ) (M : ℕ) : ℝ[X] :=
  ∑ j ∈ range (M + 1), C (chebyshevJacksonDamping M j * chebyshevCoeff f j) * T ℝ (j : ℤ)

/-- Its degree is at most the cutoff. -/
theorem degree_chebyshevJacksonApprox_le (f : ℝ → ℝ) (M : ℕ) :
    (chebyshevJacksonApprox f M).degree ≤ M := by
  refine (degree_sum_le _ _).trans (Finset.sup_le fun j hj => ?_)
  refine (degree_mul_le _ _).trans ?_
  have hT : (T ℝ (j : ℤ)).degree ≤ M := by
    rw [degree_T]
    exact_mod_cast (by have := mem_range.mp hj; omega : j ≤ M)
  exact (add_le_add degree_C_le hT).trans_eq (zero_add _)

/-- The finite Jackson polynomial is integration against the actual positive kernel. -/
theorem eval_chebyshevJacksonApprox_eq_integral {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (M : ℕ) (r : ℝ) :
    (chebyshevJacksonApprox f M).eval r =
      ∫ x, chebyshevJacksonKernel M x r * f x ∂measureT := by
  have hterm (j : ℕ) (x : ℝ) :
      chebyshevJacksonDamping M j * normalizedChebyshev j x * normalizedChebyshev j r * f x =
      (chebyshevJacksonDamping M j * normalizedChebyshevWeight j ^ 2 * (T ℝ (j : ℤ)).eval r) *
        (f x * (T ℝ (j : ℤ)).eval x) := by
    unfold normalizedChebyshev
    ring
  simp only [chebyshevJacksonApprox, eval_finsetSum, eval_mul, eval_C]
  simp_rw [chebyshevJacksonKernel, sum_mul, hterm]
  rw [integral_finsetSum (f := fun j x =>
    (chebyshevJacksonDamping M j * normalizedChebyshevWeight j ^ 2 * (T ℝ (j : ℤ)).eval r) *
      (f x * (T ℝ (j : ℤ)).eval x)) _ (fun j _ =>
        (integrable_measureT (hf.mul (T ℝ (j : ℤ)).continuous.continuousOn)).const_mul _)]
  simp_rw [integral_const_mul, normalizedChebyshevWeight_sq]
  apply sum_congr rfl
  intro j _
  unfold chebyshevCoeff
  ring

/-- Positivity of the finite polynomial follows from positivity of its kernel. -/
theorem eval_chebyshevJacksonApprox_nonneg {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ f x)
    (M : ℕ) {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    0 ≤ (chebyshevJacksonApprox f M).eval r := by
  rw [eval_chebyshevJacksonApprox_eq_integral hf]
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_Icc_measureT] with x hx
  exact mul_nonneg (chebyshevJacksonKernel_nonneg M hx hr) (hpos x hx)

/-- Positive Jackson approximation contracts every uniform bound on the closed interval. -/
theorem abs_eval_chebyshevJacksonApprox_le {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {B : ℝ}
    (hB : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ B) (M : ℕ)
    {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    |(chebyshevJacksonApprox f M).eval r| ≤ B := by
  rw [eval_chebyshevJacksonApprox_eq_integral hf, ← Real.norm_eq_abs]
  have hi : Integrable (fun x => B * chebyshevJacksonKernel M x r) measureT :=
    integrable_measureT (by fun_prop)
  refine (norm_integral_le_of_norm_le hi ?_).trans_eq ?_
  · filter_upwards [ae_mem_Icc_measureT] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (chebyshevJacksonKernel_nonneg M hx hr)]
    exact (mul_le_mul_of_nonneg_left (hB x hx) (chebyshevJacksonKernel_nonneg M hx hr)).trans_eq
      (mul_comm _ _)
  · rw [integral_const_mul, integral_chebyshevJacksonKernel, mul_one]

/-- Uniform Jackson approximation with the explicit coefficient multipliers:
the hypothesis is Lipschitz continuity only on the approximation interval. -/
theorem abs_eval_chebyshevJacksonApprox_sub_le {f : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1)) {M : ℕ} (hM : 1 ≤ M)
    {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    |(chebyshevJacksonApprox f M).eval r - f r| ≤ 6 * (L : ℝ) / M := by
  have hiK : Integrable (fun x => chebyshevJacksonKernel M x r) measureT :=
    integrable_measureT (by fun_prop)
  have hif : Integrable (fun x => chebyshevJacksonKernel M x r * f x) measureT :=
    integrable_measureT ((continuous_chebyshevJacksonKernel M r).continuousOn.mul hf.continuousOn)
  have heq : (chebyshevJacksonApprox f M).eval r - f r =
      ∫ x, chebyshevJacksonKernel M x r * (f x - f r) ∂measureT := by
    rw [eval_chebyshevJacksonApprox_eq_integral hf.continuousOn]
    simp_rw [mul_sub]
    rw [integral_sub hif (hiK.mul_const _), integral_mul_const, integral_chebyshevJacksonKernel,
      one_mul]
  rw [heq, ← Real.norm_eq_abs]
  have hdom : Integrable (fun x => (L : ℝ) * (chebyshevJacksonKernel M x r * |x - r|)) measureT :=
    integrable_measureT (by fun_prop)
  have hbound := norm_integral_le_of_norm_le hdom (show ∀ᵐ x ∂measureT,
      ‖chebyshevJacksonKernel M x r * (f x - f r)‖ ≤
        (L : ℝ) * (chebyshevJacksonKernel M x r * |x - r|) from by
    filter_upwards [ae_mem_Icc_measureT] with x hx
    have hLip := hf.dist_le_mul x hx r hr
    simp only [Real.dist_eq] at hLip
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (chebyshevJacksonKernel_nonneg M hx hr)]
    exact (mul_le_mul_of_nonneg_left hLip (chebyshevJacksonKernel_nonneg M hx hr)).trans_eq
      (by ring))
  rw [integral_const_mul] at hbound
  exact hbound.trans ((mul_le_mul_of_nonneg_left
    (integral_chebyshevJacksonKernel_mul_abs_sub_le hM hr) L.coe_nonneg).trans_eq (by ring))

end NLAlib
