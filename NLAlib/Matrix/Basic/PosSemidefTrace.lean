import Mathlib.Analysis.Matrix.Order

/-!
# Real traces of positive semidefinite matrices

A positive semidefinite matrix over `𝕜` has real diagonal and real trace, the real part of the
trace is nonnegative, and it vanishes only for the zero matrix. Thin `RCLike.re` wrappers around
Mathlib's `Matrix.PosSemidef.trace_nonneg` and `Matrix.PosSemidef.trace_eq_zero_iff`, in the
form the RPCholesky pivot probabilities use (`(R i i).re / R.trace.re`).
Chen–Epperly–Tropp–Webber 2023 (RPCholesky), §2; Horn–Johnson 2013, §7.1.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

omit [Fintype n] in
/-- A diagonal entry of a PSD matrix is the embedding of its (nonnegative) real part.
Horn–Johnson 2013, §7.1. -/
theorem diag_eq_ofReal_re_of_posSemidef {R : Matrix n n 𝕜}
    (hR : R.PosSemidef) (i : n) : R i i = ((RCLike.re (R i i) : ℝ) : 𝕜) :=
  ((RCLike.conj_eq_iff_re.mp (hR.isHermitian.apply i i))).symm

/-- The trace of a PSD matrix is the embedding of its real part. Horn–Johnson 2013, §7.1. -/
theorem trace_eq_ofReal_re_of_posSemidef {R : Matrix n n 𝕜}
    (hR : R.PosSemidef) : R.trace = ((RCLike.re R.trace : ℝ) : 𝕜) := by
  have hi := (RCLike.nonneg_iff.mp hR.trace_nonneg).2
  exact (RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr hi)).symm

/-- A PSD matrix has nonnegative real trace. Horn–Johnson 2013, §7.1. -/
theorem re_trace_nonneg_of_posSemidef {R : Matrix n n 𝕜}
    (hR : R.PosSemidef) : 0 ≤ RCLike.re R.trace := (RCLike.nonneg_iff.mp hR.trace_nonneg).1

/-- A PSD matrix with zero real trace is zero. Horn–Johnson 2013, §7.1. -/
theorem re_trace_eq_zero_iff_of_posSemidef {R : Matrix n n 𝕜}
    (hR : R.PosSemidef) : RCLike.re R.trace = 0 ↔ R = 0 := by
  constructor
  · intro ht
    apply hR.trace_eq_zero_iff.mp
    rw [trace_eq_ofReal_re_of_posSemidef hR, ht, RCLike.ofReal_zero]
  · rintro rfl
    simp

end NLAlib
