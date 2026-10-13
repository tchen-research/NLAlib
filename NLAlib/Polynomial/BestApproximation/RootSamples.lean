import NLAlib.Polynomial.Chebyshev.Markov
import NLAlib.Polynomial.BestApproximation.Basic

/-! # Finite Chebyshev-root interpolation samples

Differentiating the actual Chebyshev nodal polynomial gives the cardinal
sample formula at each Chebyshev extremum.
-/
noncomputable section
open Real Set Polynomial Polynomial.Chebyshev Finset
namespace NLAlib

/-- The Chebyshev root angles lie strictly between zero and pi.
Source: Trefethen, ATAP, Chapter 2, the explicit root grid. -/
theorem chebyshev_root_angle_mem_Ioo {N : ℕ} (j : Fin N) :
    ((j : ℝ) + 1 / 2) * π / N ∈ Ioo 0 π := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hj : (j : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  constructor
  · positivity
  · rw [div_lt_iff₀ hN]
    nlinarith [pi_pos]

/-- The actual Chebyshev zero uses the half-index root angle.
Source: the equivalent forms of the standard Chebyshev root formula. -/
theorem chebyshevZero_eq_cos_half_index {N : ℕ} (j : Fin N) :
    chebyshevZero N j = cos (((j : ℝ) + 1 / 2) * π / N) := by
  unfold chebyshevZero
  congr 1
  ring

/-- The derivative modulus at a Chebyshev zero times its root-angle sine is `N`.
Source: the differentiated Chebyshev cosine identity; shared Markov helper. -/
theorem abs_eval_derivative_T_zero_mul_sin {N : ℕ} (j : Fin N) :
    |(derivative (T ℝ N)).eval (chebyshevZero N j)| *
      sin (((j : ℝ) + 1 / 2) * π / N) = N := by
  have hθ := chebyshev_root_angle_mem_Ioo j
  have hsqrt : sin (((j : ℝ) + 1 / 2) * π / N) = √(1 - chebyshevZero N j ^ 2) := by
    rw [chebyshevZero_eq_cos_half_index]
    exact sin_eq_sqrt_one_sub_cos_sq hθ.1.le hθ.2.le
  rw [hsqrt]
  exact Markov.abs_eval_derivative_T_zero_mul_sqrt j

/-- A Chebyshev-root cardinal polynomial at an extremum has the exact sine-over-
distance modulus. Source: focused reroutes, equation `polyretry:sample`. -/
theorem abs_eval_basis_chebyshevZero_cos_nat_mul_pi_div {N : ℕ} (hN : 0 < N)
    (k : ℕ) (j : Fin N) :
    |(Lagrange.basis univ (chebyshevZero N) j).eval (cos ((k : ℝ) * π / N))| =
      sin (((j : ℝ) + 1 / 2) * π / N) /
        ((N : ℝ) * |cos ((k : ℝ) * π / N) - chebyshevZero N j|) := by
  let y := cos ((k : ℝ) * π / N)
  let c : ℝ := 1 / 2 ^ (N - 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hT : |(T ℝ N).eval y| = 1 := by
    rw [eval_T_real_cos_int_mul_pi_div (Nat.ne_of_gt hN), Int.cast_negOnePow_natCast, abs_neg_one_pow]
  have hy : y ≠ chebyshevZero N j := by
    intro h
    rw [h, eval_T_real_chebyshevZero] at hT
    norm_num at hT
  have hd := abs_eval_derivative_T_zero_mul_sin j
  have hθ := chebyshev_root_angle_mem_Ioo j
  have hs : 0 < sin (((j : ℝ) + 1 / 2) * π / N) := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hd0 : |(derivative (T ℝ N)).eval (chebyshevZero N j)| ≠ 0 := by
    intro h
    rw [h, zero_mul] at hd
    exact hNR.ne' hd.symm
  have hdiff : |y - chebyshevZero N j| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hy)
  rw [Lagrange.eval_basis_not_at_node (mem_univ j) hy,
    Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ j), nodal_chebyshevZero,
    derivative_C_mul, eval_mul, eval_C, eval_mul, eval_C, abs_mul, abs_mul, abs_mul, abs_inv, abs_inv,
    abs_mul, abs_of_pos hc, hT, mul_one]
  change c * ((c * |(derivative (T ℝ N)).eval (chebyshevZero N j)|)⁻¹ * |y - chebyshevZero N j|⁻¹) = _
  have hf (d s t : ℝ) (hd0 : d ≠ 0) (ht0 : t ≠ 0) (hds : d * s = N) :
      c * ((c * d)⁻¹ * t⁻¹) = s / ((N : ℝ) * t) := by
    field_simp [hc.ne', hd0, ht0, hNR.ne']
    exact hds.symm
  exact hf _ _ _ hd0 hdiff hd

/-- The actual Chebyshev-root Lebesgue function at an extremum is its finite sine-
distance sum. Source: focused reroutes, equation `polyretry:sample`. -/
theorem lebesgueFunction_chebyshevZero_cos_nat_mul_pi_div {N : ℕ} (hN : 0 < N) (k : ℕ) :
    lebesgueFunction (chebyshevZero N) (cos ((k : ℝ) * π / N)) =
      (1 / (N : ℝ)) * ∑ j : Fin N, sin (((j : ℝ) + 1 / 2) * π / N) /
        |cos ((k : ℝ) * π / N) - cos (((j : ℝ) + 1 / 2) * π / N)| := by
  unfold lebesgueFunction
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [abs_eval_basis_chebyshevZero_cos_nat_mul_pi_div hN k j, chebyshevZero_eq_cos_half_index]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end NLAlib
