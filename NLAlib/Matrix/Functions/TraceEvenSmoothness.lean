import NLAlib.Matrix.Functions.TracePowerDerivatives
import NLAlib.ForMathlib.Analysis.SecondDerivativeBound

/-! # Two-point smoothness of even Hermitian trace moments

Apply the even-moment Hessian estimate to a block diagonal line carrying
both signs. Its first derivative at zero vanishes exactly.
Source: Tropp 2022, Theorem 8.2 and Section 8.5.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem re_trace_block_diag (A B : Matrix ι ι ℂ) :
    (Matrix.fromBlocks A 0 0 B).trace.re = A.trace.re + B.trace.re := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- The sharp two-point estimate for every positive even Hermitian trace
moment, with no positivity or invertibility hypothesis on either matrix.
atlas: schatten-even-moment-smoothness (partial) -/
theorem re_trace_even_moment_smoothness (A H : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hH : H.IsHermitian) {p : ℕ}
    (hp : Even p) (hp2 : 2 ≤ p) :
    ((((A + H) ^ p).trace.re + ((A - H) ^ p).trace.re) / 2) ^ (2 / (p : ℝ)) ≤
      (A ^ p).trace.re ^ (2 / (p : ℝ)) +
        ((p : ℝ) - 1) * (H ^ p).trace.re ^ (2 / (p : ℝ)) := by
  let B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := Matrix.fromBlocks A 0 0 A
  let D : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := Matrix.fromBlocks H 0 0 (-H)
  have hB : B.IsHermitian := hA.fromBlocks (by simp) hA
  have hD : D.IsHermitian := hH.fromBlocks (by simp) hH.neg
  have hzero : reTracePowerFirst p B D 0 = 0 := by
    simp only [reTracePowerFirst, zero_smul, add_zero, B, D,
      Matrix.fromBlocks_diagonal_pow, Matrix.fromBlocks_multiply, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, neg_mul, neg_zero]
    rw [re_trace_block_diag]
    simp
  have h := rpow_le_of_moment_second_derivative_le
    (f := reTracePowerAlong p B D) (f' := reTracePowerFirst p B D)
    (f'' := reTracePowerSecond p B D)
    (p := (p : ℝ)) (K := (D ^ p).trace.re ^ (2 / (p : ℝ)))
    (by exact_mod_cast hp2)
    (Real.rpow_nonneg (re_trace_pow_nonneg_of_even D hD hp) _)
    (fun t => re_trace_pow_nonneg_of_even (B + t • D)
      (hB.add (hD.smul (IsSelfAdjoint.all t))) hp)
    (hasDerivAt_reTracePowerAlong p B D) (hasDerivAt_reTracePowerFirst p B D)
    hzero (reTracePowerSecond_le_even_moments p hp hp2 B D hB hD)
  have hBpow : (B ^ p).trace.re = 2 * (A ^ p).trace.re := by
    dsimp [B]
    rw [Matrix.fromBlocks_diagonal_pow, re_trace_block_diag]
    ring
  have hDpow : (D ^ p).trace.re = 2 * (H ^ p).trace.re := by
    dsimp [D]
    rw [Matrix.fromBlocks_diagonal_pow, re_trace_block_diag, hp.neg_pow]
    ring
  have hline : B + D = Matrix.fromBlocks (A + H) 0 0 (A - H) := by
    ext (i | i) (j | j) <;> simp [B, D, sub_eq_add_neg]
  have h1 : reTracePowerAlong p B D 1 =
      ((A + H) ^ p).trace.re + ((A - H) ^ p).trace.re := by
    simp only [reTracePowerAlong, one_smul, hline, Matrix.fromBlocks_diagonal_pow,
      re_trace_block_diag]
  have h0 : reTracePowerAlong p B D 0 = 2 * (A ^ p).trace.re := by
    simpa only [reTracePowerAlong, zero_smul, add_zero] using hBpow
  rw [h1, h0, hDpow] at h
  have ha := re_trace_pow_nonneg_of_even A hA hp
  have hh := re_trace_pow_nonneg_of_even H hH hp
  have hplus := re_trace_pow_nonneg_of_even (A + H) (hA.add hH) hp
  have hminus := re_trace_pow_nonneg_of_even (A - H) (hA.sub hH) hp
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hh] at h
  rw [Real.div_rpow (add_nonneg hplus hminus) (by norm_num : (0 : ℝ) ≤ 2)]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  nlinarith

end NLAlib
