import Mathlib.Analysis.Matrix.Order

/-!
# Real traces of complex positive semidefinite matrices

A complex PSD matrix has real diagonal and real trace, the real trace is nonnegative, and it
vanishes only for the zero matrix. These are thin wrappers around Mathlib's
`Matrix.PosSemidef.trace_nonneg` and `Matrix.PosSemidef.trace_eq_zero_iff` in the
`Complex.re` form used by the complex RPCholesky normalisation.
Source: CETW (2025), RPCholesky; manuscript `sa:rp-update`, `sa:rp-one-step`, audit Part VII.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib

variable {n : Type*} [Fintype n]

omit [Fintype n] in
/-- A complex PSD diagonal entry is exactly its embedded nonnegative real part.
Source: Hermitian positivity; manuscript `sa:rp-update`, pivot probabilities. -/
theorem diag_eq_ofReal_re_of_complex_posSemidef {R : Matrix n n ℂ}
    (hR : R.PosSemidef) (i : n) : R i i = ((R i i).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (hR.isHermitian.apply i i)).symm

/-- The ordered complex PSD trace is its real complex trace, with no dimension
doubling. Source: audit Part VII, complex RPCholesky normalization. -/
theorem trace_eq_ofReal_re_of_complex_posSemidef {R : Matrix n n ℂ}
    (hR : R.PosSemidef) : R.trace = (R.trace.re : ℂ) := by
  have hi := (RCLike.nonneg_iff.mp hR.trace_nonneg).2
  change R.trace.im = 0 at hi
  apply Complex.ext <;> simp [hi]

/-- A PSD matrix has nonnegative real complex trace.
Source: manuscript `sa:rp-one-step`; audit Part VII. -/
theorem re_trace_nonneg_of_complex_posSemidef {R : Matrix n n ℂ}
    (hR : R.PosSemidef) : 0 ≤ R.trace.re := (RCLike.nonneg_iff.mp hR.trace_nonneg).1

/-- Zero real complex trace characterizes the zero PSD matrix.
Source: manuscript `sa:rp-one-step`, absorbing residual. -/
theorem re_trace_eq_zero_iff_of_complex_posSemidef {R : Matrix n n ℂ}
    (hR : R.PosSemidef) : R.trace.re = 0 ↔ R = 0 := by
  constructor
  · intro ht
    apply hR.trace_eq_zero_iff.mp
    rw [trace_eq_ofReal_re_of_complex_posSemidef hR, ht, Complex.ofReal_zero]
  · rintro rfl
    simp

end NLAlib
