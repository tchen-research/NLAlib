/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Factorizations.EliminationHistory
import NLAlib.Matrix.Inequalities.TraceRankBudget

/-!
# Lower bounds for chronological trace products

The first traces pay the deterministic spectral rank budget. Later traces
are bounded below by the final residual trace. These bounds include arbitrary
zero or repeated pivot labels and require no activity hypothesis.
Source: `determinantal.tex`, RPCholesky history denominator bound.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonnegative pointwise lower bound on pre-step traces bounds their product. -/
theorem prod_le_eliminationTraceProduct {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (l : List n) (b : ℕ → ℝ) (hb : ∀ j < l.length, 0 ≤ b j)
    (hLower : ∀ j < l.length, b j ≤ RCLike.re (eliminationListResidual A (l.take j)).trace) :
    (∏ j : Fin l.length, b j) ≤ eliminationTraceProduct A l := by
  induction l generalizing A b with
  | nil => simp [eliminationTraceProduct]
  | cons i l ih =>
    have hHead := hLower 0 (by simp)
    simp only [List.take_zero, eliminationListResidual, List.foldl_nil] at hHead
    have hRest := ih (posSemidef_eliminationStep hA i) (fun j => b (j + 1))
      (fun j hj => hb (j + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hj))
      (by
        intro j hj
        have hh := hLower (j + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hj)
        simpa only [List.take_succ_cons, eliminationListResidual, List.foldl_cons] using hh)
    rw [List.length_cons, Fin.prod_univ_succ]
    exact mul_le_mul hHead hRest
      (Finset.prod_nonneg fun j _ => hb (j + 1) (Nat.succ_lt_succ j.isLt))
      (re_trace_nonneg_of_posSemidef hA)

private theorem prod_fin_ite_lt_eq_mul_pow (a : ℕ → ℝ) (c : ℝ) {t r : ℕ} (hr : r ≤ t) :
    (∏ j : Fin t, if (j : ℕ) < r then a j else c) =
      (∏ j : Fin r, a j) * c ^ (t - r) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Fin.prod_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Nat.add_sub_cancel_left]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    rw [if_pos j.isLt]
  · have hNo : ∀ j : Fin s, ¬ r + (j : ℕ) < r := fun _ => by omega
    simp only [hNo, ↓reduceIte, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- On a history with final trace at least `c≥0`, its trace denominator is
at least the first `r` optimal trace tails times `c^(length-r)`.
No selected-block inverse or distinct-pivot hypothesis is used. -/
theorem prod_spectralTraceTail_mul_pow_le_eliminationTraceProduct
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (l : List n) {r : ℕ} (hr : r ≤ l.length)
    {c : ℝ} (hc : 0 ≤ c) (hFinal : c ≤ RCLike.re (eliminationListResidual A l).trace) :
    (∏ j : Fin r, spectralTraceTail A hA.isHermitian j) * c ^ (l.length - r) ≤
      eliminationTraceProduct A l := by
  rw [← prod_fin_ite_lt_eq_mul_pow _ c hr]
  apply prod_le_eliminationTraceProduct hA l
    (fun j => if j < r then spectralTraceTail A hA.isHermitian j else c)
  · intro j hj
    split_ifs
    · exact spectralTraceTail_nonneg hA j
    · exact hc
  · intro j hj
    split_ifs with hjr
    · exact spectralTraceTail_le_re_trace_of_rank_sub_le hA
        (posSemidef_eliminationListResidual hA (l.take j))
        ((rank_sub_eliminationListResidual_le_length A (l.take j)).trans (List.length_take_le _ _))
    · have hMono := re_trace_eliminationListResidual_le
        (posSemidef_eliminationListResidual hA (l.take j)) (l.drop j)
      rw [← eliminationListResidual_append, List.take_append_drop] at hMono
      exact hFinal.trans hMono

end NLAlib
