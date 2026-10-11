import NLAlib.Matrix.ComplexFrobeniusTrace
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Complex orthogonal projector trace and diagonal budgets

Actual complex projectors have trace equal to rank, and diagonal capture
weights between zero and one. Source: Frobenius Eckart–Young proof;
supports `sa:volume-theorem` and `volume-sampling`.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical Matrix Matrix.Norms.Frobenius ComplexOrder
namespace NLAlib

/-- The real trace of any complex idempotent matrix equals its actual rank.
Source: Mathlib's projection trace theorem, `sa:volume-theorem`. -/
theorem re_trace_eq_rank_of_isIdempotentElem
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ)
    (hP : IsIdempotentElem P) : P.trace.re = (P.rank : ℝ) := by
  have hf : IsIdempotentElem P.mulVecLin := by
    change P.mulVecLin.comp P.mulVecLin = P.mulVecLin
    rw [← Matrix.mulVecLin_mul, show P * P = P from hP]
  have ht : P.trace = (P.rank : ℂ) := by
    calc
      _ = LinearMap.trace ℂ (ι → ℂ) P.toLin' := (Matrix.trace_toLin'_eq P).symm
      _ = LinearMap.trace ℂ (ι → ℂ) P.mulVecLin := by rw [Matrix.toLin'_apply']
      _ = _ := LinearMap.IsProj.trace
        ((LinearMap.isProj_range_iff_isIdempotentElem P.mulVecLin).mpr hf)
  simpa only [Complex.natCast_re] using congrArg Complex.re ht

/-- Every diagonal capture weight of a genuine complex orthogonal projector
lies in `[0,1]`, including zero dimensions. Source: `sa:volume-theorem`. -/
theorem re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem
    {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ)
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (j : ι) :
    (P j j).re ∈ Set.Icc (0 : ℝ) 1 := by
  have hgram : Pᴴ * P = P := by rw [hs.eq]; exact hp
  have hsum : (∑ i, ‖P i j‖ ^ 2) = (P j j).re := by
    have he := congrArg (fun M : Matrix ι ι ℂ => (M j j).re) hgram
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq] using he
  have h0 : 0 ≤ (P j j).re := by
    rw [← hsum]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : (P j j).re ^ 2 ≤ (P j j).re := by
    have ha := Complex.abs_re_le_norm (P j j)
    rw [abs_of_nonneg h0] at ha
    have hn : 0 ≤ ‖P j j‖ := norm_nonneg _
    have hb : ‖P j j‖ ^ 2 ≤ (P j j).re := by
      rw [← hsum]
      exact Finset.single_le_sum (fun i _ => sq_nonneg ‖P i j‖) (Finset.mem_univ j)
    nlinarith
  exact ⟨h0, by nlinarith⟩

/-- Real squared Frobenius mass splits over complementary complex
orthogonal projectors on the right. Source: `sa:volume-theorem`. -/
theorem frobenius_norm_sq_eq_right_projection_add_residual
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hs : P.IsHermitian) (hp : IsIdempotentElem P)
    (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ‖A * P‖ ^ 2 + ‖A * (1 - P)‖ ^ 2 := by
  have hleft : (A * P)ᴴ * (A * P) = P * (Aᴴ * A) * P := by
    simp only [Matrix.conjTranspose_mul, hs.eq, Matrix.mul_assoc]
  have hright : (A * (1 - P))ᴴ * (A * (1 - P)) =
      (1 - P) * (Aᴴ * A) * (1 - P) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hs.eq, Matrix.mul_assoc]
  have hcomp : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.one_mul, Matrix.mul_one, show P * P = P from hp]
    abel
  have htleft : (P * (Aᴴ * A) * P).trace = (P * (Aᴴ * A)).trace := by
    rw [Matrix.trace_mul_cycle, show P * P = P from hp]
  have htright : ((1 - P) * (Aᴴ * A) * (1 - P)).trace =
      ((1 - P) * (Aᴴ * A)).trace := by
    rw [Matrix.trace_mul_cycle, hcomp]
  rw [frobenius_norm_sq_eq_re_trace_conjTranspose_mul,
    frobenius_norm_sq_eq_re_trace_conjTranspose_mul,
    frobenius_norm_sq_eq_re_trace_conjTranspose_mul, hleft, hright, htleft, htright]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
  ring

end NLAlib
