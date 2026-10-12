import Mathlib.Tactic

/-!
# Nonnegative residue weights for strict original spectra

Interlacing gives nonnegative quotients after matching each non-pivot
target factor with the corresponding original-spectrum factor. This avoids
sign counting and permits target equalities and repeated target roots.
Source: Horn--Johnson (2013), Section 4.3;
supports `interlacing-converse`.
-/

noncomputable section
open scoped BigOperators
namespace NLAlib

/-- Weakly interlacing bordered targets give nonnegative interpolation
residues when the original spectrum is strictly increasing. Target
equalities, repeated target roots, and zero residues are allowed.
Horn--Johnson (2013), Section 4.3; helper for bordered inverse interlacing. -/
theorem neg_prod_sub_div_prod_erase_nonneg_of_bordered_interlacing
    {n : ℕ} (d : Fin n → ℝ) (b : Fin (n + 1) → ℝ)
    (hd : StrictMono d) (hb : Monotone b)
    (h : ∀ i, b i.castSucc ≤ d i ∧ d i ≤ b i.succ) (j : Fin n) :
    0 ≤ -(∏ i, (d j - b i)) / (∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (d j - d l)) := by
  have hrat (l : Fin n) (hl : l ∈ (Finset.univ : Finset (Fin n)).erase j) :
      0 ≤ (d j - b l.castSucc) / (d j - d l) := by
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    rcases lt_or_gt_of_ne hlj with hlt | hgt
    · exact div_nonneg (sub_nonneg.mpr ((hb (by exact hlt.le)).trans (h j).1))
        (sub_pos.mpr (hd hlt)).le
    · apply div_nonneg_of_nonpos
      · apply sub_nonpos.mpr
        exact (h j).2.trans (hb (by change j.val + 1 ≤ l.val; omega))
      · exact (sub_neg.mpr (hd hgt)).le
  have hprod : 0 ≤ ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (d j - b l.castSucc) / (d j - d l) :=
    Finset.prod_nonneg hrat
  have hj : 0 ≤ d j - b j.castSucc := sub_nonneg.mpr (h j).1
  have hlast : 0 ≤ b (Fin.last n) - d j := sub_nonneg.mpr
    ((h j).2.trans (hb (Fin.le_last _)))
  calc
    0 ≤ (d j - b j.castSucc) * (b (Fin.last n) - d j) *
        (∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (d j - b l.castSucc) / (d j - d l)) :=
      mul_nonneg (mul_nonneg hj hlast) hprod
    _ = _ := by
      rw [Finset.prod_div_distrib, Fin.prod_univ_castSucc]
      rw [← Finset.prod_erase_mul Finset.univ (fun l : Fin n => d j - b l.castSucc)
        (Finset.mem_univ j)]
      ring

/-- Weakly interlacing positive rank-one targets give nonnegative residues
when the original list is strictly increasing. No strictness is required
of any target inequality. Horn--Johnson (2013), Section 4.3;
helper for positive rank-one inverse interlacing. -/
theorem neg_prod_sub_div_prod_erase_nonneg_of_rank_one_interlacing
    {n : ℕ} (d b : Fin n → ℝ) (hd : StrictMono d) (hb : Monotone b)
    (hlo : ∀ i, d i ≤ b i)
    (hhi : ∀ i j : Fin n, i.val + 1 = j.val → b i ≤ d j) (j : Fin n) :
    0 ≤ -(∏ i, (d j - b i)) / (∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (d j - d l)) := by
  have hrat (l : Fin n) (hl : l ∈ (Finset.univ : Finset (Fin n)).erase j) :
      0 ≤ (d j - b l) / (d j - d l) := by
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    rcases lt_or_gt_of_ne hlj with hlt | hgt
    · have hlNext : l.val + 1 < n := by have := j.isLt; change l.val < j.val at hlt; omega
      let t : Fin n := ⟨l.val + 1, hlNext⟩
      have hbt : b l ≤ d t := hhi l t rfl
      have htj : t ≤ j := by change l.val + 1 ≤ j.val; change l.val < j.val at hlt; omega
      exact div_nonneg (sub_nonneg.mpr (hbt.trans (hd.monotone htj)))
        (sub_pos.mpr (hd hlt)).le
    · exact div_nonneg_of_nonpos (sub_nonpos.mpr ((hlo j).trans (hb hgt.le)))
        (sub_neg.mpr (hd hgt)).le
  have hprod : 0 ≤ ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (d j - b l) / (d j - d l) :=
    Finset.prod_nonneg hrat
  calc
    0 ≤ (b j - d j) * (∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (d j - b l) / (d j - d l)) :=
      mul_nonneg (sub_nonneg.mpr (hlo j)) hprod
    _ = _ := by
      rw [Finset.prod_div_distrib, ← Finset.prod_erase_mul Finset.univ (fun l => d j - b l)
        (Finset.mem_univ j)]
      ring

end NLAlib
