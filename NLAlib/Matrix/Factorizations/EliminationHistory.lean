/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import NLAlib.Matrix.Basic.SchurComplement
import NLAlib.Matrix.Factorizations.CholeskyPivotProbability
import NLAlib.Matrix.Basic.RankBounds

/-!
# Determinants along chronological elimination histories

The determinant of a selected principal matrix is the product of chronological
Schur pivots. The PSD statement includes zero pivots and repeated indices.
The trace product is kept division free, so it also applies after absorption.
Source: the supplied `determinantal.tex`, history determinant telescope; helpers
for `rpcholesky-factorial-trace-tail` and `adaptive-pivoting-projection-dpp`.
-/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The residual after the pivots in a list, in their chronological order. -/
def eliminationListResidual (A : Matrix n n 𝕜) (l : List n) : Matrix n n 𝕜 :=
  l.foldl eliminationStep A

/-- The product of the successive diagonal pivots, including a zero pivot. -/
def eliminationPivotProduct (A : Matrix n n 𝕜) : List n → 𝕜
  | [] => 1
  | i :: l => A i i * eliminationPivotProduct (eliminationStep A i) l

/-- The product of the real traces before the successive elimination steps. -/
def eliminationTraceProduct (A : Matrix n n 𝕜) : List n → ℝ
  | [] => 1
  | i :: l => RCLike.re A.trace * eliminationTraceProduct (eliminationStep A i) l

omit [Fintype n] [DecidableEq n] in
/-- Concatenating histories continues elimination from the first residual. -/
theorem eliminationListResidual_append (A : Matrix n n 𝕜) (l r : List n) :
    eliminationListResidual A (l ++ r) = eliminationListResidual (eliminationListResidual A l) r := by
  simp [eliminationListResidual, List.foldl_append]

omit [Fintype n] [DecidableEq n] in
/-- Appending a pivot applies one additional Schur update. -/
theorem eliminationListResidual_append_singleton (A : Matrix n n 𝕜) (l : List n) (i : n) :
    eliminationListResidual A (l ++ [i]) = eliminationStep (eliminationListResidual A l) i := by
  simp [eliminationListResidual, List.foldl_append]

omit [Fintype n] [DecidableEq n] in
/-- Appending a pivot multiplies the pivot product by the next residual diagonal. -/
theorem eliminationPivotProduct_append_singleton (A : Matrix n n 𝕜) (l : List n) (i : n) :
    eliminationPivotProduct A (l ++ [i]) =
      eliminationPivotProduct A l * eliminationListResidual A l i i := by
  induction l generalizing A with
  | nil => simp [eliminationPivotProduct, eliminationListResidual]
  | cons j l ih => simp [eliminationPivotProduct, eliminationListResidual, ih, mul_assoc]

omit [DecidableEq n] in
/-- Appending a pivot multiplies the trace product by the current residual trace. -/
theorem eliminationTraceProduct_append_singleton (A : Matrix n n 𝕜) (l : List n) (i : n) :
    eliminationTraceProduct A (l ++ [i]) =
      eliminationTraceProduct A l * RCLike.re (eliminationListResidual A l).trace := by
  induction l generalizing A with
  | nil => simp [eliminationTraceProduct, eliminationListResidual]
  | cons j l ih => simp [eliminationTraceProduct, eliminationListResidual, ih, mul_assoc]

/-- Every chronological elimination residual of a PSD matrix remains PSD. -/
theorem posSemidef_eliminationListResidual {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (l : List n) : (eliminationListResidual A l).PosSemidef := by
  induction l generalizing A with
  | nil => exact hA
  | cons i l ih => exact ih (posSemidef_eliminationStep hA i)

/-- Chronological PSD residuals decrease in Loewner order. -/
theorem eliminationListResidual_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) (l : List n) :
    eliminationListResidual A l ≤ A := by
  induction l generalizing A with
  | nil => exact le_rfl
  | cons i l ih => exact (ih (posSemidef_eliminationStep hA i)).trans (eliminationStep_le hA i)

/-- Chronological PSD residuals have nonincreasing real trace. -/
theorem re_trace_eliminationListResidual_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) (l : List n) :
    RCLike.re (eliminationListResidual A l).trace ≤ RCLike.re A.trace := by
  have hn := re_trace_nonneg_of_posSemidef (Matrix.le_iff.mp (eliminationListResidual_le hA l))
  rw [Matrix.trace_sub, map_sub] at hn
  linarith

omit [Fintype n] [DecidableEq n] in
private theorem det_submatrix_cons_of_ne_zero (A : Matrix n n 𝕜) {k : ℕ}
    (i : n) (h : Fin k → n) (hi : A i i ≠ 0) :
    (A.submatrix (Fin.cons i h) (Fin.cons i h)).det =
      A i i * ((eliminationStep A i).submatrix h h).det := by
  let D : Matrix (Fin 1) (Fin 1) 𝕜 := Matrix.diagonal fun _ => A i i
  let R : Matrix (Fin 1) (Fin k) 𝕜 := fun _ j => A i (h j)
  let C : Matrix (Fin k) (Fin 1) 𝕜 := fun j _ => A (h j) i
  have hD : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr (by
    simpa [D, Matrix.det_unique] using isUnit_iff_ne_zero.mpr hi)
  let := hD.invertible
  have he : (A.submatrix (Fin.cons i h) (Fin.cons i h)).submatrix
      (finOneSumEquiv k) (finOneSumEquiv k) = Matrix.fromBlocks D R C (A.submatrix h h) := by
    ext a b
    cases a <;> cases b <;> simp [D, R, C, Matrix.fromBlocks, Matrix.diagonal, Fin.eq_zero]
  rw [← Matrix.det_submatrix_equiv_self (finOneSumEquiv k), he, Matrix.det_fromBlocks₁₁]
  have hs : A.submatrix h h - C * ⅟D * R = (eliminationStep A i).submatrix h h := by
    rw [Matrix.invOf_eq_nonsing_inv, show D⁻¹ = Matrix.diagonal (fun _ : Fin 1 => (A i i)⁻¹) by
      simp [D]]
    ext a b
    change A (h a) (h b) - _ = A (h a) (h b) - _
    congr 1
    change (∑ x : Fin 1, (∑ y : Fin 1, A (h a) i *
      (Matrix.diagonal (fun _ : Fin 1 => (A i i)⁻¹)) y x) * A i (h b)) =
        (A i i)⁻¹ * (A (h a) i * A i (h b))
    simp only [Fin.sum_univ_one, Matrix.diagonal_apply_eq]
    ring
  rw [hs]
  simp [D, Matrix.det_unique]

/-- A PSD selected principal determinant factors through its first Schur pivot,
including zero pivots and repeated selected indices. -/
theorem det_submatrix_cons_eq_mul_det_eliminationStep {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {k : ℕ} (i : n) (h : Fin k → n) :
    (A.submatrix (Fin.cons i h) (Fin.cons i h)).det =
      A i i * ((eliminationStep A i).submatrix h h).det := by
  by_cases hi : A i i = 0
  · rw [hi, zero_mul]
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    simpa using apply_eq_zero_of_posSemidef_of_apply_self_eq_zero' hA hi
      ((Fin.cons i h : Fin (k + 1) → n) j)
  · exact det_submatrix_cons_of_ne_zero A i h hi

/-- The selected principal determinant equals the product of chronological
elimination pivots. No distinctness or positive-pivot assumption is needed. -/
theorem det_submatrix_eq_eliminationPivotProduct {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {k : ℕ} (h : Fin k → n) :
    (A.submatrix h h).det = eliminationPivotProduct A (List.ofFn h) := by
  induction k generalizing A with
  | zero => simp [eliminationPivotProduct]
  | succ k ih =>
    rw [← Fin.cons_self_tail h, List.ofFn_cons, eliminationPivotProduct,
      det_submatrix_cons_eq_mul_det_eliminationStep hA]
    rw [ih (posSemidef_eliminationStep hA (h 0))]

/-- The real trace product is nonnegative for every PSD pivot history. -/
theorem eliminationTraceProduct_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (l : List n) : 0 ≤ eliminationTraceProduct A l := by
  induction l generalizing A with
  | nil => exact zero_le_one
  | cons i l ih =>
    exact mul_nonneg (re_trace_nonneg_of_posSemidef hA)
      (ih (posSemidef_eliminationStep hA i))

/-- The real chronological pivot product also has the expected last-step
factorization: PSD diagonal pivots are real even for complex matrices. -/
theorem re_eliminationPivotProduct_append_singleton {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (l : List n) (i : n) :
    RCLike.re (eliminationPivotProduct A (l ++ [i])) =
      RCLike.re (eliminationPivotProduct A l) *
        RCLike.re (eliminationListResidual A l i i) := by
  rw [eliminationPivotProduct_append_singleton,
    diag_eq_ofReal_re_of_posSemidef (posSemidef_eliminationListResidual hA l) i]
  simp

/-- Every elimination step removes at most one rank, including a zero pivot. -/
theorem rank_le_rank_eliminationStep_add_one (A : Matrix n n 𝕜) (i : n) :
    A.rank ≤ (eliminationStep A i).rank + 1 := by
  by_cases hi : A i i = 0
  · rw [eliminationStep_eq_self_of_apply_self_eq_zero hi]
    omega
  · exact (rank_eliminationStep_add_one_eq hi).ge

/-- A chronological history removes at most its length in rank. This bound
does not assume that the chosen pivots are supported or nonzero. -/
theorem rank_le_rank_eliminationListResidual_add_length (A : Matrix n n 𝕜) (l : List n) :
    A.rank ≤ (eliminationListResidual A l).rank + l.length := by
  induction l generalizing A with
  | nil => exact le_rfl
  | cons i l ih =>
    have hOne := rank_le_rank_eliminationStep_add_one A i
    have hRest := ih (eliminationStep A i)
    change A.rank ≤ (eliminationListResidual (eliminationStep A i) l).rank + (l.length + 1)
    omega

/-- All pre-step traces are positive until the number of requested steps exceeds
the original rank, even for an arbitrary list of zero or repeated pivots. -/
theorem eliminationTraceProduct_pos {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (l : List n) (hl : l.length ≤ A.rank) : 0 < eliminationTraceProduct A l := by
  induction l generalizing A with
  | nil => exact zero_lt_one
  | cons i l ih =>
    have hRank : 0 < A.rank := by simpa using lt_of_lt_of_le (by simp : 0 < (i :: l).length) hl
    have hTrace : 0 < RCLike.re A.trace := by
      refine lt_of_le_of_ne (re_trace_nonneg_of_posSemidef hA) ?_
      intro hz
      have hZero := (re_trace_eq_zero_iff_of_posSemidef hA).mp hz.symm
      simp [hZero] at hRank
    have hOne := rank_le_rank_eliminationStep_add_one A i
    have hLen : l.length ≤ (eliminationStep A i).rank := by simp only [List.length_cons] at hl; omega
    exact mul_pos hTrace (ih (posSemidef_eliminationStep hA i) hLen)

omit [DecidableEq n] in
/-- One elimination correction has rank at most one, including a zero pivot. -/
theorem rank_sub_eliminationStep_le_one (A : Matrix n n 𝕜) (i : n) :
    (A - eliminationStep A i).rank ≤ 1 := by
  rw [eliminationStep, sub_sub_cancel, ← Matrix.smul_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _

omit [DecidableEq n] in
/-- The actual approximation accumulated along a history has rank at most
the history length, even for repeated or zero pivots. -/
theorem rank_sub_eliminationListResidual_le_length (A : Matrix n n 𝕜) (l : List n) :
    (A - eliminationListResidual A l).rank ≤ l.length := by
  induction l generalizing A with
  | nil => simp [eliminationListResidual]
  | cons i l ih =>
    have he : A - eliminationListResidual A (i :: l) =
        (A - eliminationStep A i) +
          (eliminationStep A i - eliminationListResidual (eliminationStep A i) l) := by
      change A - eliminationListResidual (eliminationStep A i) l = _
      abel
    rw [he]
    exact (rank_add_le _ _).trans
      ((add_le_add (rank_sub_eliminationStep_le_one A i) (ih _)).trans (by simp only [List.length_cons]; omega))

/-- A nonzero chronological pivot product certifies exactly one rank removed
per step. Positivity is unnecessary for this algebraic rank identity. -/
theorem rank_eliminationListResidual_add_length_eq_of_pivotProduct_ne_zero
    (A : Matrix n n 𝕜) (l : List n) (hl : eliminationPivotProduct A l ≠ 0) :
    (eliminationListResidual A l).rank + l.length = A.rank := by
  induction l generalizing A with
  | nil => simp [eliminationListResidual]
  | cons i l ih =>
    have hp : A i i ≠ 0 ∧ eliminationPivotProduct (eliminationStep A i) l ≠ 0 :=
      mul_ne_zero_iff.mp hl
    have hOne := rank_eliminationStep_add_one_eq hp.1
    have hRest := ih (eliminationStep A i) hp.2
    change (eliminationListResidual (eliminationStep A i) l).rank + (l.length + 1) = A.rank
    omega

end NLAlib
