import NLAlib.Polynomial.Quadrature.FoldedMomentBounds
import NLAlib.Polynomial.BestApproximation.LobattoCardinals

/-!
# Actual Clenshaw–Curtis weights

Integrating the endpoint-half discrete cosine expansion of the genuine Lagrange
cardinals gives the weights. A finite moment telescope proves strict positivity.
-/

noncomputable section
open Polynomial Polynomial.Chebyshev Real Finset MeasureTheory Set
namespace NLAlib

/-- Clenshaw–Curtis is the finite weighted sum with its actual cardinal integrals.
Source: integrating Lagrange's formula; ATAP, Chapter 19. -/
theorem clenshawCurtisRule_eq_sum_weights (n : ℕ) (f : ℝ → ℝ) :
    clenshawCurtisRule n f = ∑ j ∈ range (n + 1), clenshawCurtisWeight n j * f (node n j) := by
  simp only [clenshawCurtisRule, Lagrange.interpolate_apply, eval_finsetSum, eval_mul,
    eval_C, Function.comp_apply]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul, clenshawCurtisWeight, mul_comm]
  · intro j _
    exact (continuous_const.mul (Lagrange.basis (range (n + 1)) (node n) j).continuous).intervalIntegrable _ _

/-- Integrating the finite endpoint-half cosine cardinal gives an explicit
formula for every actual Clenshaw–Curtis weight.
Source: finite DCT cardinal formula; focused rederivations `thm:lobatto`. -/
theorem clenshawCurtisWeight_eq_cosine_sum {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    clenshawCurtisWeight n j = (lobattoEndpointWeight n j / n) *
      (2 + ∑ k ∈ range (n - 1),
        (2 * cos ((k + 1 : ℕ) * (j * π / n))) * chebyshevMoment (k + 1) +
        cos ((n : ℝ) * (j * π / n)) * chebyshevMoment n) := by
  rw [clenshawCurtisWeight, ← lobattoCardinal_eq_basis hn hj]
  simp only [lobattoCardinal, eval_smul, eval_add, eval_one, eval_finsetSum, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (by
      exact (show Continuous (fun x : ℝ => 1 + ∑ k ∈ range (n - 1),
        (2 * cos ((k + 1 : ℕ) * (j * π / n))) * (T ℝ (k + 1 : ℕ)).eval x) by fun_prop).intervalIntegrable _ _)
      (by exact (continuous_const.mul (T ℝ n).continuous).intervalIntegrable _ _),
    intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _) (by
      exact (show Continuous (fun x : ℝ => ∑ k ∈ range (n - 1),
        (2 * cos ((k + 1 : ℕ) * (j * π / n))) * (T ℝ (k + 1 : ℕ)).eval x) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (f := fun k x =>
      (2 * cos ((k + 1 : ℕ) * (j * π / n))) * (T ℝ (k + 1 : ℕ)).eval x) (fun k _ =>
      (continuous_const.mul (T ℝ (k + 1 : ℕ)).continuous).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  simp_rw [intervalIntegral.integral_const_mul, integral_eval_T]
  simp only [chebyshevMoment]
  norm_num

/-- Odd Lebesgue Chebyshev moments vanish.
Source: ATAP, Theorem 19.2; helper for positivity of actual quadrature weights. -/
@[simp] theorem chebyshevMoment_two_mul_add_one (j : ℕ) :
    chebyshevMoment (2 * j + 1) = 0 := by
  unfold chebyshevMoment
  rw [if_neg (by simp : ¬ Even (2 * j + 1))]

/-- Pairing odd and even moments reduces any even-length natural sum to the
positive-even telescope.
Source: finite pairing; helper for actual Clenshaw–Curtis positivity. -/
theorem sum_abs_chebyshevMoment_succ_two_mul (m : ℕ) :
    (∑ k ∈ range (2 * m), |chebyshevMoment (k + 1)|) =
      ∑ j ∈ range m, |chebyshevMoment (2 * (j + 1))| := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, sum_range_succ, sum_range_succ,
      sum_range_succ, ih, chebyshevMoment_two_mul_add_one]
    simp only [abs_zero, add_zero]
    congr 2

/-- A finite natural sum of positive-degree absolute Chebyshev moments is
strictly below one, with an explicit telescoping margin.
Source: the even-moment telescope; focused quadrature reroutes. -/
theorem sum_abs_chebyshevMoment_succ_le (n : ℕ) :
    (∑ k ∈ range n, |chebyshevMoment (k + 1)|) ≤ 1 - 1 / (2 * (n : ℝ) + 1) := by
  calc
    _ ≤ ∑ k ∈ range (2 * n), |chebyshevMoment (k + 1)| :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => abs_nonneg _)
    _ = _ := by rw [sum_abs_chebyshevMoment_succ_two_mul, sum_abs_chebyshevMoment_two_mul_succ]

/-- A cosine coefficient times any real moment is bounded below by minus
the absolute moment.
Source: `|cos| ≤ 1`; helper for actual Clenshaw–Curtis positivity. -/
theorem neg_abs_le_cos_mul (t u : ℝ) : -|u| ≤ cos t * u := by
  have h : |cos t * u| ≤ |u| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (abs_cos_le_one t) (abs_nonneg u)
  linarith [neg_abs_le (cos t * u)]

/-- Every actual Clenshaw–Curtis weight is strictly positive on its endpoint grid.
Source: integrated endpoint-half DCT cardinals and the finite moment telescope;
focused rederivations `thm:lobatto`. -/
theorem clenshawCurtisWeight_pos {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    0 < clenshawCurtisWeight n j := by
  rw [clenshawCurtisWeight_eq_cosine_sum hn hj]
  apply mul_pos
  · apply div_pos _ (by exact_mod_cast hn)
    unfold lobattoEndpointWeight
    split_ifs <;> norm_num
  · have hsum : -2 * (∑ k ∈ range (n - 1), |chebyshevMoment (k + 1)|) ≤
        ∑ k ∈ range (n - 1),
          (2 * cos ((k + 1 : ℕ) * (j * π / n))) * chebyshevMoment (k + 1) := by
      rw [mul_sum]
      apply sum_le_sum
      intro k _
      nlinarith [neg_abs_le_cos_mul ((k + 1 : ℕ) * (j * π / n)) (chebyshevMoment (k + 1))]
    have hend := neg_abs_le_cos_mul ((n : ℝ) * (j * π / n)) (chebyshevMoment n)
    have hfull : (∑ k ∈ range n, |chebyshevMoment (k + 1)|) =
        (∑ k ∈ range (n - 1), |chebyshevMoment (k + 1)|) + |chebyshevMoment n| := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ n by omega), sum_range_succ]
      simp only [Nat.sub_add_cancel (show 1 ≤ n by omega)]
    have hbound := sum_abs_chebyshevMoment_succ_le n
    rw [hfull] at hbound
    have hmargin : 0 < 1 / (2 * (n : ℝ) + 1) := by positivity
    nlinarith [abs_nonneg (chebyshevMoment n)]

/-- The actual quadrature weights sum to the interval length two.
Source: Lagrange partition of unity; ATAP, Chapter 19. -/
theorem sum_clenshawCurtisWeight (n : ℕ) :
    (∑ j ∈ range (n + 1), clenshawCurtisWeight n j) = 2 := by
  simp only [clenshawCurtisWeight]
  rw [← intervalIntegral.integral_finsetSum (f := fun j x =>
    (Lagrange.basis (range (n + 1)) (node n) j).eval x) (fun j _ =>
      (Lagrange.basis (range (n + 1)) (node n) j).continuous.intervalIntegrable _ _)]
  have hp := Lagrange.sum_basis (chebyshev_node_injOn n)
    (show (range (n + 1)).Nonempty from ⟨0, by simp⟩)
  simp_rw [← eval_finsetSum, hp, eval_one]
  norm_num

/-- The one-node convention has its single quadrature weight equal to two.
Source: the constant cardinal polynomial; ATAP, Chapter 19. -/
@[simp] theorem clenshawCurtisWeight_zero_zero : clenshawCurtisWeight 0 0 = 2 := by
  norm_num [clenshawCurtisWeight, range_one, Lagrange.basis_singleton]

/-- Every actual grid weight is nonnegative, including the one-node convention.
Source: the integrated DCT cardinals; ATAP, Chapter 19. -/
theorem clenshawCurtisWeight_nonneg (n j : ℕ) (hj : j ≤ n) :
    0 ≤ clenshawCurtisWeight n j := by
  by_cases hn : n = 0
  · subst n
    have hj0 : j = 0 := by omega
    subst j
    rw [clenshawCurtisWeight_zero_zero]
    norm_num
  · exact (clenshawCurtisWeight_pos (Nat.pos_of_ne_zero hn) hj).le

/-- Positivity and mass two make the actual Clenshaw–Curtis rule contract
every unit-interval uniform bound by the interval length.
Source: positive quadrature weights; ATAP, Chapter 19. -/
theorem abs_clenshawCurtisLinearMap_le (n : ℕ) (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    |clenshawCurtisLinearMap n f| ≤ 2 * ‖f‖ := by
  change |∑ j ∈ range (n + 1), clenshawCurtisWeight n j * f ⟨node n j, node_mem_Icc⟩| ≤ _
  calc
    _ ≤ ∑ j ∈ range (n + 1), |clenshawCurtisWeight n j * f ⟨node n j, node_mem_Icc⟩| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (n + 1), clenshawCurtisWeight n j * ‖f‖ := by
      apply sum_le_sum
      intro j hj
      have hw := clenshawCurtisWeight_nonneg n j (Nat.le_of_lt_succ (mem_range.mp hj))
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm ⟨node n j, node_mem_Icc⟩) hw
    _ = 2 * ‖f‖ := by rw [← sum_mul, sum_clenshawCurtisWeight]

end NLAlib
