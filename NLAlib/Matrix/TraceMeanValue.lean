import NLAlib.Matrix.TraceYoung

/-!
# Polynomial trace mean-value inequality

The overlap of two separate Hermitian eigenbases reduces the trace inequality
to an odd-power scalar inequality. This is the deterministic input to the
individual sign-flip proof for integer noncommutative Khintchine moments.
Source: operator manuscript `lem:meanvalue`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
open Matrix
namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic trace of a Hermitian difference expands into three
polynomial traces. Source: cyclicity in manuscript `lem:meanvalue`;
supports `noncommutative-khintchine`. -/
theorem re_trace_sub_sq_mul_pow (H K : Matrix ι ι ℂ) (m : ℕ) :
    ((H - K) ^ 2 * H ^ m).trace.re =
      (H ^ (m + 2)).trace.re + (H ^ m * K ^ 2).trace.re -
        2 * (H ^ (m + 1) * K).trace.re := by
  have hpow : H * H * H ^ m = H ^ (m + 2) := by
    rw [← pow_two, ← pow_add]
    congr 1
    omega
  have hcross : (H * K * H ^ m).trace = (H ^ (m + 1) * K).trace := by
    rw [Matrix.trace_mul_cycle, ← pow_succ]
  have hcross' : (K * H * H ^ m).trace = (H ^ (m + 1) * K).trace := by
    rw [Matrix.mul_assoc, ← pow_succ', Matrix.trace_mul_comm]
  have hkk : (K * K * H ^ m).trace = (H ^ m * K ^ 2).trace := by
    rw [← pow_two, Matrix.trace_mul_comm]
  rw [pow_two]
  simp only [sub_mul, mul_sub, Matrix.trace_sub, hpow, hcross, hcross', hkk]
  simp only [Complex.sub_re]
  ring

/-- **Polynomial trace mean-value inequality.** At every odd power `m+1`,
where `m` is even, the Hermitian difference is bounded by the average of
the two endpoint quadratic traces. Source: manuscript `lem:meanvalue`;
supports `noncommutative-khintchine`. The matrices may fail to commute. -/
theorem re_trace_sub_mul_sub_pow_le
    (H K : Matrix ι ι ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    {m : ℕ} (hm : Even m) :
    ((H - K) * (H ^ (m + 1) - K ^ (m + 1))).trace.re ≤
      ((m + 1 : ℕ) : ℝ) / 2 *
        ((H - K) ^ 2 * (H ^ m + K ^ m)).trace.re := by
  let W : Matrix.unitaryGroup ι ℂ := star hH.eigenvectorUnitary * hK.eigenvectorUnitary
  let w (i j : ι) := ‖(W : Matrix ι ι ℂ) i j‖ ^ 2
  let a := hH.eigenvalues
  let b := hK.eigenvalues
  have hrow (i) : ∑ j, w i j = 1 := sum_norm_sq_unitary_row W i
  have hcol (j) : ∑ i, w i j = 1 := sum_norm_sq_unitary_col W j
  have hleft (r : ℕ) : (H ^ r).trace.re = ∑ i, ∑ j, w i j * a i ^ r := by
    rw [re_trace_pow_eq_sum_eigenvalues_pow H hH]
    simp only [← Finset.sum_mul, hrow, one_mul, a]
  have hright (r : ℕ) : (K ^ r).trace.re = ∑ i, ∑ j, w i j * b j ^ r := by
    rw [re_trace_pow_eq_sum_eigenvalues_pow K hK, Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, one_mul, b]
  have hprod (r s : ℕ) : (H ^ r * K ^ s).trace.re =
      ∑ i, ∑ j, w i j * a i ^ r * b j ^ s :=
    re_trace_pow_mul_pow_eq_sum_overlap H K hH hK r s
  have hprodH (r : ℕ) : (H ^ r * K).trace.re =
      ∑ i, ∑ j, w i j * a i ^ r * b j := by
    simpa only [pow_one] using hprod r 1
  have hprodK (r : ℕ) : (K ^ r * H).trace.re =
      ∑ i, ∑ j, w i j * a i * b j ^ r := by
    rw [Matrix.trace_mul_comm]
    simpa only [pow_one] using hprod 1 r
  have hL : ((H - K) * (H ^ (m + 1) - K ^ (m + 1))).trace.re =
      ∑ i, ∑ j, w i j * ((a i - b j) * (a i ^ (m + 1) - b j ^ (m + 1))) := by
    have hh : (H * H ^ (m + 1)).trace = (H ^ (m + 2)).trace := by rw [← pow_succ']
    have hk : (K * K ^ (m + 1)).trace = (K ^ (m + 2)).trace := by rw [← pow_succ']
    have hhk : (H * K ^ (m + 1)).trace.re =
        ∑ i, ∑ j, w i j * a i * b j ^ (m + 1) := by
      simpa only [pow_one] using hprod 1 (m + 1)
    have hkh : (K * H ^ (m + 1)).trace.re =
        ∑ i, ∑ j, w i j * a i ^ (m + 1) * b j := by
      rw [Matrix.trace_mul_comm]
      exact hprodH (m + 1)
    rw [sub_mul, mul_sub, mul_sub, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, hh, hk]
    simp only [Complex.sub_re]
    rw [hleft, hright, hhk, hkh]
    have he (x y : ℝ) : (x - y) * (x ^ (m + 1) - y ^ (m + 1)) =
        x ^ (m + 2) - x * y ^ (m + 1) - x ^ (m + 1) * y + y ^ (m + 2) := by
      rw [pow_succ x (m + 1), pow_succ y (m + 1)]
      ring
    simp_rw [he, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_assoc]
    ring
  have hR : ((H - K) ^ 2 * (H ^ m + K ^ m)).trace.re =
      ∑ i, ∑ j, w i j * ((a i - b j) ^ 2 * (a i ^ m + b j ^ m)) := by
    have heq : (H - K) ^ 2 = (K - H) ^ 2 := by
      rw [show H - K = -(K - H) by abel, neg_sq]
    rw [mul_add, Matrix.trace_add, Complex.add_re, re_trace_sub_sq_mul_pow]
    rw [heq, re_trace_sub_sq_mul_pow]
    rw [hleft, hright, hprod, Matrix.trace_mul_comm (K ^ m) (H ^ 2), hprod,
      hprodH, hprodK]
    have he (x y : ℝ) : (x - y) ^ 2 * (x ^ m + y ^ m) =
        x ^ (m + 2) + x ^ m * y ^ 2 - 2 * (x ^ (m + 1) * y) +
        (y ^ (m + 2) + x ^ 2 * y ^ m - 2 * (x * y ^ (m + 1))) := by
      rw [pow_add x m 2, pow_add y m 2, pow_succ x m, pow_succ y m]
      ring
    simp_rw [he, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_assoc]
    simp only [mul_left_comm, ← Finset.mul_sum]
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    simp only [mul_assoc, mul_comm]
  rw [hL, hR]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      mul_le_mul_of_nonneg_left (sub_mul_sub_pow_le_of_even hm (a i) (b j))
        (sq_nonneg ‖(W : Matrix ι ι ℂ) i j‖)
  simpa only [w, mul_assoc, mul_left_comm, Finset.mul_sum] using hsum

end NLAlib
