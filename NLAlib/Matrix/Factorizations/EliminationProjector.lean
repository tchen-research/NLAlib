import NLAlib.Matrix.Factorizations.EliminationStep
import NLAlib.Matrix.Subspaces.ProjectorBlocks
import NLAlib.Matrix.Subspaces.ProjectorTrace
import NLAlib.Matrix.Factorizations.EliminationHistory
import Mathlib.Data.Nat.Factorial.Basic

/-! # Elimination of an orthogonal projector

A pivot removes one orthogonal direction from a projector. The update
remains a projector even at a zero pivot, which is the absorbing algebraic
branch of adaptive QR on an orthonormal frame.
Source: the projection-DPP pivot identity, Epperly 2025, Theorem 3.3.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A right matrix fixing the current residual also fixes its elimination
update. This tracks containment in an original projected range. -/
theorem eliminationStep_mul_of_mul_eq {A B : Matrix n n 𝕜}
    (hAB : A * B = A) (i : n) : eliminationStep A i * B = eliminationStep A i := by
  have hv : (fun j => A i j) ᵥ* B = fun j => A i j := by
    funext j
    exact congrFun (congrFun hAB i) j
  rw [eliminationStep, Matrix.sub_mul, Matrix.smul_mul, Matrix.vecMulVec_mul, hv,
    hAB]

/-- Eliminating a pivot from an idempotent leaves a matrix fixed by right
multiplication by the original idempotent. -/
theorem eliminationStep_mul_of_isIdempotentElem {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) (i : n) : eliminationStep P i * P = eliminationStep P i :=
  eliminationStep_mul_of_mul_eq hP i

/-- Every elimination update of an orthogonal projector is again an
orthogonal projector, including zero pivots. -/
theorem isIdempotentElem_eliminationStep_of_projector {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (i : n) :
    IsIdempotentElem (eliminationStep P i) := by
  have hPSD := hs.posSemidef_of_isIdempotentElem hp
  have hmul := eliminationStep_mul_of_isIdempotentElem hp i
  have hv : eliminationStep P i *ᵥ (fun j => P j i) = 0 := by
    have he := congrArg (fun M : Matrix n n 𝕜 => M *ᵥ Pi.single i 1) hmul
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at he
    change eliminationStep P i *ᵥ P.col i = 0
    rw [he]
    funext j
    exact eliminationStep_apply_pivot_right hPSD i j
  change eliminationStep P i * eliminationStep P i = eliminationStep P i
  conv_lhs => rhs; rw [eliminationStep]
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_vecMulVec, hv,
    Matrix.zero_vecMulVec, smul_zero, sub_zero, hmul]

/-- The residual projector's real trace drops by exactly one at a positive
pivot. This is the remaining-rank normalizer in adaptive QR. -/
theorem re_trace_eliminationStep_of_projector {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) {i : n} (hi : P i i ≠ 0) :
    RCLike.re (eliminationStep P i).trace = RCLike.re P.trace - 1 := by
  have he := isIdempotentElem_eliminationStep_of_projector hs hp i
  rw [trace_eq_rank_of_isIdempotentElem _ he,
    trace_eq_rank_of_isIdempotentElem _ hp, RCLike.natCast_re, RCLike.natCast_re]
  have hr := rank_eliminationStep_add_one_eq hi
  have hr' : ((eliminationStep P i).rank : ℝ) + 1 = P.rank := by exact_mod_cast hr
  linarith

/-- Along a projector history with nonzero determinant, the trace product
is the falling factorial of its original rank. No arbitrary eigenbasis
or regularity condition is involved. -/
theorem eliminationTraceProduct_eq_descFactorial_of_projector {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (l : List n)
    (hz : eliminationPivotProduct P l ≠ 0) :
    eliminationTraceProduct P l = (P.rank.descFactorial l.length : ℝ) := by
  induction l generalizing P with
  | nil => simp [eliminationTraceProduct]
  | cons i l ih =>
    have hzi : P i i ≠ 0 := (mul_ne_zero_iff.mp hz).1
    have hzl : eliminationPivotProduct (eliminationStep P i) l ≠ 0 := (mul_ne_zero_iff.mp hz).2
    have heS := isHermitian_eliminationStep hs i
    have heP := isIdempotentElem_eliminationStep_of_projector hs hp i
    have hr := rank_eliminationStep_add_one_eq hzi
    rw [eliminationTraceProduct, ih heS heP hzl,
      trace_eq_rank_of_isIdempotentElem P hp, RCLike.natCast_re, ← hr,
      List.length_cons, Nat.succ_descFactorial_succ, Nat.cast_mul]

/-- Every finite elimination history of a projector remains idempotent,
including histories containing zero or repeated pivots. -/
theorem isIdempotentElem_eliminationListResidual_of_projector {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (l : List n) :
    IsIdempotentElem (eliminationListResidual P l) := by
  induction l generalizing P with
  | nil => exact hp
  | cons i l ih =>
    exact ih (isHermitian_eliminationStep hs i)
      (isIdempotentElem_eliminationStep_of_projector hs hp i)

/-- A matrix fixing the starting residual also fixes every later residual. -/
theorem eliminationListResidual_mul_of_mul_eq {A B : Matrix n n 𝕜}
    (hAB : A * B = A) (l : List n) : eliminationListResidual A l * B = eliminationListResidual A l := by
  induction l generalizing A with
  | nil => exact hAB
  | cons i l ih => exact ih (eliminationStep_mul_of_mul_eq hAB i)

end NLAlib
