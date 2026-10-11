import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Positive matrix norm, trace, and real scalar order

The spectral theorem bounds the norm of a PSD complex matrix by its real trace. Applied
to a Gram matrix this gives the exact squared operator-norm versus coordinate-sum bound.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Nonnegative real scaling preserves complex matrix Loewner order.
Source: scaling the actual PSD difference; supports `audit:combined` and
atlas `matrix-freedman` (partial). -/
theorem matrix_smul_le_smul_of_nonneg {A B : Matrix n n ℂ} (hAB : A ≤ B)
    {c : ℝ} (hc : 0 ≤ c) : c • A ≤ c • B := by
  apply Matrix.le_iff.mpr
  rw [← smul_sub]
  exact (Matrix.le_iff.mp hAB).smul hc

/-- The actual operator norm of a PSD complex matrix is at most its real trace.
Source: the finite spectral theorem and nonnegative eigenvalues; supports the audited
variance-budget localization `audit:combined`, atlas `matrix-freedman` (partial). -/
theorem norm_le_re_trace_of_posSemidef (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    ‖A‖ ≤ A.trace.re := by
  have htrace : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp
  have ht : 0 ≤ A.trace.re := (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  conv_lhs => rw [← cfc_id' ℝ A hA.isHermitian]
  apply norm_cfc_le ht
  intro x hx
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i), htrace]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

omit [DecidableEq n] in
/-- The real trace of the actual complex Gram matrix is the sum of squared entry norms.
Source: finite Gram expansion; supports `audit:combined`, `matrix-freedman` (partial). -/
theorem re_trace_conjTranspose_mul_self_eq_sum_sq_norm {m : Type*} [Fintype m]
    (A : Matrix m n ℂ) : (Aᴴ * A).trace.re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The squared complex matrix operator norm is bounded by the actual Hilbert-Schmidt
coordinate sum, with exact coefficient one.
Source: PSD Gram norm versus trace; supports `audit:combined`, `matrix-freedman` (partial). -/
theorem norm_sq_le_sum_sq_norm_entries {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n ℂ) : ‖A‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h := norm_le_re_trace_of_posSemidef (Aᴴ * A) (Matrix.posSemidef_conjTranspose_mul_self A)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, re_trace_conjTranspose_mul_self_eq_sum_sq_norm] at h
  simpa only [pow_two] using h

omit [DecidableEq n] in
/-- The real trace is monotone in complex matrix Loewner order.
Source: nonnegative trace of the PSD difference; supports `matrix-freedman`. -/
theorem re_trace_le_re_trace_of_le {A B : Matrix n n ℂ} (h : A ≤ B) :
    A.trace.re ≤ B.trace.re := by
  have ht := (RCLike.nonneg_iff.mp (Matrix.le_iff.mp h).trace_nonneg).1
  change 0 ≤ (B - A).trace.re at ht
  rw [Matrix.trace_sub, Complex.sub_re] at ht
  linarith

/-- The real trace of a Hermitian matrix is at most dimension times its operator norm.
Source: spectral theorem and the eigenvalue norm bound; supports `matrix-freedman`. -/
theorem re_trace_le_card_mul_norm_of_isHermitian [Nonempty n] (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    A.trace.re ≤ Fintype.card n * ‖A‖ := by
  have ht : A.trace.re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]
    simp
  rw [ht]
  calc
    (∑ i, hA.eigenvalues i) ≤ ∑ _i : n, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hnorm : |hA.eigenvalues i| ≤ ‖A‖ := by
        simpa only [Real.norm_eq_abs] using
          spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)
      exact (le_abs_self _).trans hnorm
    _ = Fintype.card n * ‖A‖ := by simp

end NLAlib
