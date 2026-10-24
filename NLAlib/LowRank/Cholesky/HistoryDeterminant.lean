/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.EliminationHistory
import NLAlib.LowRank.Cholesky.CholeskyHistories
import NLAlib.LowRank.Cholesky.ComplexCholeskyHistories

/-!
# Determinant telescopes for the native adaptive Cholesky laws

Each actual finite-history weight times the product of its pre-step residual
traces equals the selected principal determinant. These division-free identities
include repeated pivots and absorption. Division is exposed only for a positive
trace product. Source: `determinantal.tex`, chronological determinant telescope;
helpers for `rpcholesky-factorial-trace-tail` and
`adaptive-pivoting-projection-dpp`.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- The generic chronological residual is the native real partial-Cholesky
residual, including zero pivots. -/
theorem eliminationListResidual_ofFn_eq_partialCholeskyResidual
    (A : Matrix n n ℝ) {t : ℕ} (h : Fin t → n) :
    eliminationListResidual A (List.ofFn h) = partialCholeskyResidual A h := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.ofFn_succ', List.concat_eq_append]
    change eliminationListResidual A (List.ofFn (Fin.init h) ++ [h (Fin.last t)]) = _
    rw [eliminationListResidual_append_singleton, ih]
    rfl

omit [Fintype n] [DecidableEq n] in
/-- The generic chronological residual is the native complex adaptive residual. -/
theorem eliminationListResidual_ofFn_eq_complexCholeskyResidualHistory
    (A : Matrix n n ℂ) {t : ℕ} (h : Fin t → n) :
    eliminationListResidual A (List.ofFn h) = complexCholeskyResidualHistory A t h := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.ofFn_succ', List.concat_eq_append]
    change eliminationListResidual A (List.ofFn (Fin.init h) ++ [h (Fin.last t)]) = _
    rw [eliminationListResidual_append_singleton, ih]
    rfl

/-- The product of the residual traces immediately before the chronological
pivots. Its generic definition agrees with both native Cholesky processes. -/
def choleskyHistoryTraceProduct {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix n n 𝕜) {t : ℕ} (h : Fin t → n) : ℝ :=
  eliminationTraceProduct A (List.ofFn h)

/-- Every native pre-step trace product is positive for a history no longer
than the original rank. The history itself need not have positive mass. -/
theorem choleskyHistoryTraceProduct_pos {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {t : ℕ} (h : Fin t → n)
    (ht : t ≤ A.rank) : 0 < choleskyHistoryTraceProduct A h :=
  eliminationTraceProduct_pos hA _ (by simpa using ht)

omit [DecidableEq n] in
/-- Real native history trace product at the next time. -/
theorem choleskyHistoryTraceProduct_succ (A : Matrix n n ℝ) {t : ℕ}
    (h : Fin (t + 1) → n) :
    choleskyHistoryTraceProduct A h =
      choleskyHistoryTraceProduct A (Fin.init h) *
        (partialCholeskyResidual A (Fin.init h)).trace := by
  rw [choleskyHistoryTraceProduct, List.ofFn_succ', List.concat_eq_append]
  change eliminationTraceProduct A (List.ofFn (Fin.init h) ++ [h (Fin.last t)]) = _
  rw [eliminationTraceProduct_append_singleton,
    eliminationListResidual_ofFn_eq_partialCholeskyResidual]
  rfl

omit [DecidableEq n] in
/-- Complex native history trace product at the next time. -/
theorem choleskyHistoryTraceProduct_succ_complex (A : Matrix n n ℂ) {t : ℕ}
    (h : Fin (t + 1) → n) :
    choleskyHistoryTraceProduct A h =
      choleskyHistoryTraceProduct A (Fin.init h) *
        (complexCholeskyResidualHistory A t (Fin.init h)).trace.re := by
  rw [choleskyHistoryTraceProduct, List.ofFn_succ', List.concat_eq_append]
  change eliminationTraceProduct A (List.ofFn (Fin.init h) ++ [h (Fin.last t)]) = _
  rw [eliminationTraceProduct_append_singleton,
    eliminationListResidual_ofFn_eq_complexCholeskyResidualHistory]
  rfl

/-- The native real history weight times its trace product is the selected
principal determinant, also when a history has repeated or zero pivots. -/
theorem choleskyHistoryWeight_mul_traceProduct_eq_det {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {t : ℕ} (h : Fin t → n) :
    choleskyHistoryWeight A t h * choleskyHistoryTraceProduct A h =
      (A.submatrix h h).det := by
  rw [det_submatrix_eq_eliminationPivotProduct hA]
  induction t with
  | zero => simp [choleskyHistoryWeight, choleskyHistoryTraceProduct,
      eliminationTraceProduct, eliminationPivotProduct]
  | succ t ih =>
    rw [choleskyHistoryWeight, choleskyHistoryTraceProduct_succ,
      List.ofFn_succ', List.concat_eq_append]
    change _ = eliminationPivotProduct A (List.ofFn (Fin.init h) ++ [h (Fin.last t)])
    rw [eliminationPivotProduct_append_singleton,
      eliminationListResidual_ofFn_eq_partialCholeskyResidual]
    have hp := choleskyPivotProbability_mul_re_trace
      (posSemidef_partialCholeskyResidual hA (Fin.init h)) (h (Fin.last t))
    change choleskyPivotProbability _ _ *
      (partialCholeskyResidual A (Fin.init h)).trace =
        (partialCholeskyResidual A (Fin.init h)) (h (Fin.last t)) (h (Fin.last t)) at hp
    rw [show _ * _ * (_ * _) =
      (choleskyHistoryWeight A t (Fin.init h) * choleskyHistoryTraceProduct A (Fin.init h)) *
        (choleskyPivotProbability (partialCholeskyResidual A (Fin.init h)) (h (Fin.last t)) *
          (partialCholeskyResidual A (Fin.init h)).trace) by ring,
      ih, hp]

/-- The native complex history weight times its trace product is the real part
of the selected principal determinant, with no activity assumption. -/
theorem complexCholeskyHistoryWeight_mul_traceProduct_eq_re_det {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {t : ℕ} (h : Fin t → n) :
    complexCholeskyHistoryWeight A t h * choleskyHistoryTraceProduct A h =
      (A.submatrix h h).det.re := by
  rw [det_submatrix_eq_eliminationPivotProduct hA]
  induction t with
  | zero => simp [complexCholeskyHistoryWeight, choleskyHistoryTraceProduct,
      eliminationTraceProduct, eliminationPivotProduct]
  | succ t ih =>
    rw [complexCholeskyHistoryWeight, choleskyHistoryTraceProduct_succ_complex,
      List.ofFn_succ', List.concat_eq_append]
    change _ = Complex.re (eliminationPivotProduct A (List.ofFn (Fin.init h) ++ [h (Fin.last t)]))
    have hpiv : (eliminationPivotProduct A (List.ofFn (Fin.init h) ++ [h (Fin.last t)])).re =
        (eliminationPivotProduct A (List.ofFn (Fin.init h))).re *
          (eliminationListResidual A (List.ofFn (Fin.init h)) (h (Fin.last t)) (h (Fin.last t))).re :=
      re_eliminationPivotProduct_append_singleton hA _ _
    rw [hpiv,
      eliminationListResidual_ofFn_eq_complexCholeskyResidualHistory]
    have hp := choleskyPivotProbability_mul_re_trace
      (posSemidef_complexCholeskyResidualHistory hA t (Fin.init h)) (h (Fin.last t))
    change choleskyPivotProbability _ _ *
      (complexCholeskyResidualHistory A t (Fin.init h)).trace.re =
        (complexCholeskyResidualHistory A t (Fin.init h) (h (Fin.last t)) (h (Fin.last t))).re at hp
    rw [show _ * _ * (_ * _) =
      (complexCholeskyHistoryWeight A t (Fin.init h) * choleskyHistoryTraceProduct A (Fin.init h)) *
        (choleskyPivotProbability (complexCholeskyResidualHistory A t (Fin.init h)) (h (Fin.last t)) *
          (complexCholeskyResidualHistory A t (Fin.init h)).trace.re) by ring,
      ih, hp]

/-- Supported division form of the actual real adaptive history law. -/
theorem choleskyHistoryWeight_eq_det_div_traceProduct {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {t : ℕ} (h : Fin t → n)
    (ht : 0 < choleskyHistoryTraceProduct A h) :
    choleskyHistoryWeight A t h = (A.submatrix h h).det / choleskyHistoryTraceProduct A h :=
  (eq_div_iff (ne_of_gt ht)).mpr (choleskyHistoryWeight_mul_traceProduct_eq_det hA h)

/-- Supported division form of the actual complex adaptive history law. -/
theorem complexCholeskyHistoryWeight_eq_re_det_div_traceProduct {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {t : ℕ} (h : Fin t → n)
    (ht : 0 < choleskyHistoryTraceProduct A h) :
    complexCholeskyHistoryWeight A t h = (A.submatrix h h).det.re / choleskyHistoryTraceProduct A h :=
  (eq_div_iff (ne_of_gt ht)).mpr (complexCholeskyHistoryWeight_mul_traceProduct_eq_re_det hA h)

/-- Singleton mass of the actual real adaptive law satisfies the division-free
determinant telescope. Zero-mass histories are included. -/
theorem choleskyHistoryLaw_singleton_mul_traceProduct_eq_det [Nonempty n]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (t : ℕ) (h : Fin t → n) :
    (choleskyHistoryLaw A hA t).real {h} * choleskyHistoryTraceProduct A h =
      (A.submatrix h h).det := by
  rw [choleskyHistoryLaw_singleton]
  exact choleskyHistoryWeight_mul_traceProduct_eq_det hA h

/-- Singleton mass of the actual complex adaptive law satisfies the same
division-free telescope with real determinant. -/
theorem complexCholeskyHistoryLaw_singleton_mul_traceProduct_eq_re_det [Nonempty n]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) (t : ℕ) (h : Fin t → n) :
    (complexCholeskyHistoryLaw A hA t).real {h} * choleskyHistoryTraceProduct A h =
      (A.submatrix h h).det.re := by
  rw [complexCholeskyHistoryLaw_singleton]
  exact complexCholeskyHistoryWeight_mul_traceProduct_eq_re_det hA h

end NLAlib
