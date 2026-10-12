import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Trace and diagonal of projectors

* `trace_eq_rank_of_isIdempotentElem`: an idempotent matrix over any field has trace equal to
  its rank (Mathlib's `LinearMap.IsProj.trace` in matrix coordinates);
* `re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem`: every diagonal entry of an orthogonal
  projector over `ℝ` or `ℂ` has real part in `[0, 1]`.

These are the projector facts behind the Frobenius Eckart–Young proof and leverage scores.
Source: Horn–Johnson, Matrix Analysis, Theorem 7.4.9 (proof); atlas `eckart-young`
(foundation), `sa:volume-theorem`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- The trace of an idempotent matrix over a field is its rank. Empty index types
are included. This is Mathlib's projection trace theorem in matrix coordinates; over `ℂ`, take
`Complex.re` of both sides for the real-trace form. Atlas `eckart-young` (foundation);
`sa:volume-theorem`. -/
theorem trace_eq_rank_of_isIdempotentElem {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (P : Matrix ι ι K) (hP : IsIdempotentElem P) : P.trace = (P.rank : K) := by
  have hf : IsIdempotentElem P.mulVecLin := by
    change P.mulVecLin.comp P.mulVecLin = P.mulVecLin
    rw [← Matrix.mulVecLin_mul, show P * P = P from hP]
  calc
    P.trace = LinearMap.trace K (ι → K) P.toLin' := (Matrix.trace_toLin'_eq P).symm
    _ = LinearMap.trace K (ι → K) P.mulVecLin := by rw [Matrix.toLin'_apply']
    _ = (P.rank : K) := LinearMap.IsProj.trace
      ((LinearMap.isProj_range_iff_isIdempotentElem P.mulVecLin).mpr hf)

/-- Every diagonal capture weight of an orthogonal projector (Hermitian idempotent) over `ℝ` or
`ℂ` has real part in `[0,1]`, including zero dimensions. The proof uses the squared column
length. For a real symmetric projector this reads `P j j ∈ [0, 1]`. Atlas `eckart-young`
(foundation); `sa:volume-theorem`. -/
theorem re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem {ι 𝕜 : Type*} [Fintype ι]
    [RCLike 𝕜] (P : Matrix ι ι 𝕜) (hs : P.IsHermitian) (hp : IsIdempotentElem P) (j : ι) :
    RCLike.re (P j j) ∈ Set.Icc (0 : ℝ) 1 := by
  have hgram : Pᴴ * P = P := by rw [hs.eq]; exact hp
  have hsum : (∑ i, ‖P i j‖ ^ 2) = RCLike.re (P j j) := by
    have he := congrArg (fun M : Matrix ι ι 𝕜 => RCLike.re (M j j)) hgram
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, RCLike.star_def,
      RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re] at he
    exact he
  have h0 : 0 ≤ RCLike.re (P j j) := by
    rw [← hsum]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : RCLike.re (P j j) ^ 2 ≤ RCLike.re (P j j) := by
    have ha := RCLike.abs_re_le_norm (P j j)
    rw [abs_of_nonneg h0] at ha
    have hn : 0 ≤ ‖P j j‖ := norm_nonneg _
    have hb : ‖P j j‖ ^ 2 ≤ RCLike.re (P j j) := by
      rw [← hsum]
      exact Finset.single_le_sum (fun i _ => sq_nonneg ‖P i j‖) (Finset.mem_univ j)
    nlinarith
  exact ⟨h0, by nlinarith⟩

end NLAlib
