import NLAlib.Matrix.Norms.SchattenMoments
import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import NLAlib.Matrix.Functions.TracePowers
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Cubic absolute moments of bounded Hermitian matrices

Functional calculus gives `|A|³ ≤ c A²` when `||A|| ≤ c`. Ordinary trace
identifies the corresponding actual Schatten third-moment bound.
Source: bounded-summand reroute for `cauchy-transform-gaussian-universality`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A scalar spectral bound controls the actual cubic absolute matrix power
in Loewner order, including zero bound and singular matrices. -/
theorem cfc_abs_pow_three_le_smul_sq {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {c : ℝ} (hAc : specNorm A ≤ c) :
    cfc (fun x : ℝ => |x| ^ 3) A ≤ c • A ^ 2 := by
  rw [← cfc_pow_id (R := ℝ) A 2, ← cfc_smul c (fun x : ℝ => x ^ 2) A]
  refine (cfc_le_iff (fun x : ℝ => |x| ^ 3) (fun x : ℝ => c • x ^ 2) A
    (by fun_prop) (by fun_prop) hA).mpr ?_
  intro x hx
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have hi : |hA.eigenvalues i| ≤ c := by
    apply le_trans _ hAc
    rw [hA.specNorm_eq_norm_eigenvalues]
    exact norm_le_pi_norm hA.eigenvalues i
  have hh := mul_le_mul_of_nonneg_right hi (sq_nonneg (hA.eigenvalues i))
  have he : |hA.eigenvalues i| ^ 3 = |hA.eigenvalues i| * hA.eigenvalues i ^ 2 := by
    rw [pow_succ, sq_abs, mul_comm]
  simpa only [smul_eq_mul, he] using hh

open scoped Matrix.Norms.L2Operator in
/-- The actual third Schatten moment of a Hermitian matrix is at most its
spectral norm times its ordinary quadratic trace. -/
theorem schattenNormReal_pow_three_le_specNorm_mul_re_trace_sq
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    schattenNormReal A 3 ^ 3 ≤ specNorm A * (A ^ 2).trace.re := by
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num,
    schattenNormReal_pow_nat_eq_re_trace_cfc_abs hA (by norm_num : 0 < (3 : ℕ)),
    re_trace_cfc_eq_sum_eigenvalues hA, re_trace_pow_eq_sum_eigenvalues_pow A hA,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : |hA.eigenvalues i| ≤ specNorm A := by
    rw [hA.specNorm_eq_norm_eigenvalues]
    exact norm_le_pi_norm hA.eigenvalues i
  have hh := mul_le_mul_of_nonneg_right hi (sq_nonneg (hA.eigenvalues i))
  have he : |hA.eigenvalues i| ^ 3 = |hA.eigenvalues i| * hA.eigenvalues i ^ 2 := by
    rw [pow_succ, sq_abs, mul_comm]
  simpa only [he] using hh

end NLAlib
