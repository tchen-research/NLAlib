import Mathlib.Order.Fin.Basic
import Mathlib.Data.Real.Basic

/-!
# Deleting a forced repeated root from interlacing lists

Monotone lists that are not strictly monotone contain an equal adjacent pair.
Deleting the associated forced common root preserves weak interlacing.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

/-- A non-strict monotone finite real list has an equal adjacent pair.
Horn–Johnson 2013, Theorems 4.3.21 and 4.3.26; repeated-root deletion helper. -/
theorem exists_adjacent_eq_of_monotone_not_strictMono {n : ℕ}
    (d : Fin (n + 1) → ℝ) (hd : Monotone d) (hn : ¬StrictMono d) :
    ∃ i : Fin n, d i.castSucc = d i.succ := by
  by_contra h
  push Not at h
  apply hn
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact lt_of_le_of_ne (hd (Fin.castSucc_le_succ i)) (h i)

/-- Adjacent upper rank-one interlacing inequalities imply the corresponding
inequality at every strictly later original eigenvalue. Horn–Johnson 2013,
Theorem 4.3.26; finite-list convention bridge. -/
theorem interlacing_upper_of_adjacent {n : ℕ} (d b : Fin n → ℝ)
    (hd : Monotone d) (h : ∀ i j, i.val + 1 = j.val → b i ≤ d j) :
    ∀ i j, i < j → b i ≤ d j := by
  intro i j hij
  let l : Fin n := ⟨i.val + 1, by omega⟩
  exact (h i l rfl).trans (hd (show l ≤ j by change i.val + 1 ≤ j.val; omega))

/-- Numeric coordinates of the increasing embedding that omits one finite
index. Mathlib's `Fin.succAbove`; supports repeated interlacing deletion. -/
theorem val_succAbove_eq_ite {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

/-- Removing an original eigenvalue at `p` and a target eigenvalue at
`p+1` preserves bordered weak interlacing. Equality of the two removed
values is a separate hypothesis used by the polynomial reconstruction.
Horn–Johnson 2013, Theorem 4.3.21; repeated-root deletion helper. -/
theorem bordered_interlacing_succAbove {n : ℕ}
    (d : Fin (n + 1) → ℝ) (b : Fin (n + 2) → ℝ) (hb : Monotone b)
    (h : ∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ) (p : Fin (n + 1)) :
    ∀ i : Fin n,
      b (p.succ.succAbove i.castSucc) ≤ d (p.succAbove i) ∧
      d (p.succAbove i) ≤ b (p.succ.succAbove i.succ) := by
  intro i
  constructor
  · apply le_trans (hb ?_) (h (p.succAbove i)).1
    change (p.succ.succAbove i.castSucc).val ≤ (p.succAbove i).val
    simp only [val_succAbove_eq_ite, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · apply le_trans (h (p.succAbove i)).2 (hb ?_)
    change (p.succAbove i).val + 1 ≤ (p.succ.succAbove i.succ).val
    simp only [val_succAbove_eq_ite, Fin.val_succ]
    split_ifs <;> omega

/-- An adjacent repeated original eigenvalue forces the intervening target
eigenvalue in bordered interlacing. Horn–Johnson 2013, Theorem 4.3.21;
the weak-equality case is retained exactly. -/
theorem bordered_interlacing_forced_root {n : ℕ}
    (d : Fin (n + 1) → ℝ) (b : Fin (n + 2) → ℝ)
    (h : ∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ)
    (i : Fin n) (hi : d i.castSucc = d i.succ) :
    b i.castSucc.succ = d i.castSucc := by
  have hidx : i.succ.castSucc = i.castSucc.succ := rfl
  exact le_antisymm (by simpa only [hidx, ← hi] using (h i.succ).1) (h i.castSucc).2

/-- An adjacent repeated original eigenvalue forces the corresponding
target eigenvalue in positive rank-one interlacing. Horn–Johnson 2013,
Theorem 4.3.26; repeated-root deletion helper. -/
theorem rank_one_interlacing_forced_root {n : ℕ}
    (d b : Fin (n + 1) → ℝ) (hlo : ∀ i, d i ≤ b i)
    (hhi : ∀ i j, i < j → b i ≤ d j) (i : Fin n)
    (hi : d i.castSucc = d i.succ) : b i.castSucc = d i.castSucc := by
  exact le_antisymm (by simpa only [← hi] using hhi i.castSucc i.succ Fin.castSucc_lt_succ)
    (hlo i.castSucc)

end NLAlib
