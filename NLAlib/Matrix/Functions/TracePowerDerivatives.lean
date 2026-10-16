import NLAlib.Matrix.Functions.PolynomialSeries
import NLAlib.Matrix.Functions.TraceEvenHolder
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Complex Hermitian trace-power derivatives

Exact first and second derivatives along real affine lines, followed by the
even-moment Hessian estimate of Tropp 2022, Section 8.5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real part of a complex trace power along an affine matrix line. -/
def reTracePowerAlong (p : ℕ) (A H : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  ((A + t • H) ^ p).trace.re

/-- The explicit first derivative of an affine trace power. -/
def reTracePowerFirst (p : ℕ) (A H : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  (p : ℝ) * (H * (A + t • H) ^ (p - 1)).trace.re

/-- The explicit second derivative of an affine trace power. -/
def reTracePowerSecond (p : ℕ) (A H : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  (p : ℝ) * ∑ i ∈ Finset.range (p - 1),
    (H * (A + t • H) ^ ((p - 1).pred - i) * H * (A + t • H) ^ i).trace.re

private theorem re_trace_derivative_sum (C H : Matrix ι ι ℂ) (p : ℕ) :
    (∑ i ∈ Finset.range p, C ^ (p.pred - i) * H * C ^ i).trace.re =
      (p : ℝ) * (H * C ^ (p - 1)).trace.re := by
  rw [Matrix.trace_sum, Complex.re_sum]
  have hterm (i : ℕ) (hi : i ∈ Finset.range p) :
      (C ^ (p.pred - i) * H * C ^ i).trace = (H * C ^ (p - 1)).trace := by
    rw [Matrix.trace_mul_comm (C ^ (p.pred - i) * H),
      ← Matrix.mul_assoc, Matrix.trace_mul_comm (C ^ i * C ^ (p.pred - i)) H,
      ← pow_add]
    simp only [Nat.pred_eq_sub_one]
    rw [show i + (p - 1 - i) = p - 1 by have := Finset.mem_range.mp hi; omega]
  calc
    _ = ∑ _i ∈ Finset.range p, (H * C ^ (p - 1)).trace.re := by
      exact Finset.sum_congr rfl fun i hi => congrArg Complex.re (hterm i hi)
    _ = _ := by simp

/-- Exact first derivative, for arbitrary complex matrices.
atlas: schatten-even-moment-smoothness (partial) -/
theorem hasDerivAt_reTracePowerAlong (p : ℕ) (A H : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (reTracePowerAlong p A H) (reTracePowerFirst p A H t) t := by
  have haff : HasDerivAt (fun r : ℝ => A + r • H) H t := by
    simpa using ((hasDerivAt_id t).smul_const H).const_add A
  have htrace := (hasDerivAt_const t
    (reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ)).clm_apply (haff.fun_pow' p)
  convert! htrace using 1
  · simp only [_root_.zero_apply, zero_add, reTraceCLM_apply,
      re_trace_derivative_sum, reTracePowerFirst]

/-- Exact second derivative, for arbitrary complex matrices.
atlas: schatten-even-moment-smoothness (partial) -/
theorem hasDerivAt_reTracePowerFirst (p : ℕ) (A H : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (reTracePowerFirst p A H) (reTracePowerSecond p A H t) t := by
  have haff : HasDerivAt (fun r : ℝ => A + r • H) H t := by
    simpa using ((hasDerivAt_id t).smul_const H).const_add A
  have hmul := (hasDerivAt_const t H).mul (haff.fun_pow' (p - 1))
  have htrace := (hasDerivAt_const t
    (reTraceCLM : Matrix ι ι ℂ →L[ℝ] ℝ)).clm_apply hmul
  have hscaled := htrace.const_mul (p : ℝ)
  convert! hscaled using 1
  · simp only [_root_.zero_apply, zero_mul, zero_add, reTraceCLM_apply,
      Finset.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.mul_assoc,
      reTracePowerSecond]

/-- The trace Hessian is bounded by the even endpoint trace moment.
atlas: schatten-even-moment-smoothness (partial) -/
theorem reTracePowerSecond_le_trace_sq_mul (p : ℕ) (hp : Even p) (hp2 : 2 ≤ p)
    (A H : Matrix ι ι ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) (t : ℝ) :
    reTracePowerSecond p A H t ≤
      (p : ℝ) * ((p : ℝ) - 1) * (H ^ 2 * (A + t • H) ^ (p - 2)).trace.re := by
  have hB : (A + t • H).IsHermitian := hA.add (hH.smul (IsSelfAdjoint.all t))
  have hm : Even (p - 2) := by
    obtain ⟨k, hk⟩ := hp
    exact ⟨k - 1, by omega⟩
  have hsum := Finset.sum_le_sum fun i (hi : i ∈ Finset.range (p - 1)) => by
    have hi' : i ≤ p - 2 := by have := Finset.mem_range.mp hi; omega
    have hpred : (p - 1).pred = p - 2 := by simp only [Nat.pred_eq_sub_one]; omega
    have h := re_trace_mul_pow_mul_le_trace_sq_mul_pow H (A + t • H) hH hB
      hm (show (p - 1).pred - i ≤ p - 2 by rw [hpred]; omega)
    have he : p - 2 - ((p - 1).pred - i) = i := by rw [hpred]; omega
    rw [he] at h
    exact h
  have h := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  simpa only [reTracePowerSecond, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one, mul_assoc] using h

/-- The source even-moment Hessian estimate with sharp coefficient `p(p−1)`.
atlas: schatten-even-moment-smoothness (partial) -/
theorem reTracePowerSecond_le_even_moments (p : ℕ) (hp : Even p) (hp2 : 2 ≤ p)
    (A H : Matrix ι ι ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) (t : ℝ) :
    reTracePowerSecond p A H t ≤
      (p : ℝ) * ((p : ℝ) - 1) * reTracePowerAlong p A H t ^ (1 - 2 / (p : ℝ)) *
        (H ^ p).trace.re ^ (2 / (p : ℝ)) := by
  have hB : (A + t • H).IsHermitian := hA.add (hH.smul (IsSelfAdjoint.all t))
  have h := re_trace_sq_mul_pow_le_even_moments H (A + t • H) hH hB hp hp2
  have hc : 0 ≤ (p : ℝ) * ((p : ℝ) - 1) := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    exact mul_nonneg (by positivity) (by linarith)
  exact (reTracePowerSecond_le_trace_sq_mul p hp hp2 A H hA hH t).trans
    (by simpa only [reTracePowerAlong, mul_assoc] using mul_le_mul_of_nonneg_left h hc)

end NLAlib
