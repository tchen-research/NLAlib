import NLAlib.Matrix.Functions.CFCTrace
import NLAlib.Matrix.Functions.TracePowerBounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Interpolating absolute trace powers of Hermitian matrices

Cauchy–Schwarz on the spectral counting measure bounds an absolute trace power by its
two neighboring even trace powers. This avoids choosing eigenvectors in probability arguments.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace NLAlib

/-- An absolute spectral trace power is bounded by the geometric mean of its two neighboring
even trace powers. Source: spectral Cauchy–Schwarz, used in Appendix `closed:thm:moment` of
the Khatri–Rao embedding manuscript. -/
theorem trace_cfc_abs_pow_le_sqrt_trace_even_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (cfc (fun x : ℝ => |x| ^ k) A).trace ≤
      Real.sqrt ((A ^ (2 * (k / 2))).trace * (A ^ (2 * ((k + 1) / 2))).trace) := by
  rw [trace_cfc_eq_sum_eigenvalues hA, trace_pow_eq_sum_eigenvalues hA,
    trace_pow_eq_sum_eigenvalues hA]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hpar : k / 2 + (k + 1) / 2 = k := by omega
  have he (x : ℝ) (j : ℕ) : (|x| ^ j) ^ 2 = x ^ (2 * j) := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, sq_abs, ← pow_mul]
  have hs : ∑ i, |hA.eigenvalues i| ^ k =
      ∑ i, |hA.eigenvalues i| ^ (k / 2) * |hA.eigenvalues i| ^ ((k + 1) / 2) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_add, hpar]
  rw [hs]
  apply Real.le_sqrt_of_sq_le
  simpa only [he] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |hA.eigenvalues i| ^ (k / 2))
    (fun i => |hA.eigenvalues i| ^ ((k + 1) / 2))

/-- Dividing all trace moments by the same positive mass preserves spectral
Cauchy–Schwarz interpolation. -/
theorem div_trace_cfc_abs_pow_le_sqrt_div_trace_even_pow {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℕ)
    {c : ℝ} (hc : 0 < c) :
    (cfc (fun x : ℝ => |x| ^ k) A).trace / c ≤
      Real.sqrt ((A ^ (2 * (k / 2))).trace / c) *
        Real.sqrt ((A ^ (2 * ((k + 1) / 2))).trace / c) := by
  have ha := trace_pow_nonneg_of_even hA (even_two_mul (k / 2))
  have hb := trace_pow_nonneg_of_even hA (even_two_mul ((k + 1) / 2))
  rw [Real.sqrt_div ha, Real.sqrt_div hb, div_mul_div_comm,
    Real.mul_self_sqrt hc.le, ← Real.sqrt_mul ha]
  exact div_le_div_of_nonneg_right (trace_cfc_abs_pow_le_sqrt_trace_even_pow hA k) hc.le

end NLAlib
