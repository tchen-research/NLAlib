import NLAlib.Sketching.Sampling.RowVolumeComposition
import NLAlib.Matrix.Basic.RowSubsetLeverage

/-! # Reverse row-volume deletion is a finite Markov recursion

Each step samples a literal one-row deletion with its Gram determinant
weight. Invalid or deficient states are absorbing; the law theorem shows
that those fallbacks are unreachable from a full-rank valid state.
Source: Dereziński–Warmuth 2018, Theorem 2.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

/-- One reverse-deletion step draws a subset one row smaller, using its
Gram determinant. The total conditional kernel absorbs malformed states. -/
def rowVolumeDeletionStep (X : Matrix n d 𝕜) (T : Finset n) : PMF (Finset n) :=
  rowVolumeKernel X (T.card - 1) T

/-- The actual finite reverse-deletion process, starting from `T` and
performing `q` one-row transitions. -/
def rowVolumeDeletionPMF (X : Matrix n d 𝕜) : ℕ → Finset n → PMF (Finset n)
  | 0, T => pure T
  | q + 1, T => (rowVolumeDeletionPMF X q T).bind (rowVolumeDeletionStep X)

/-- The actual one-row deletion mass is `(1-h_i)/(|T|-d)`, including
zero-probability deletions that would destroy column rank.
Dereziński–Warmuth 2018, Theorem 2.
atlas: row-volume-sampling-deletion-law (partial)-/
theorem rowVolumeDeletionStep_toReal_erase (X : Matrix n d 𝕜) (T : Finset n) {i : n}
    (hi : i ∈ T) (hT : 0 < rowSubsetVolume X T) (hdt : Fintype.card d < T.card) :
    (rowVolumeDeletionStep X T (T.erase i)).toReal =
      (1 - rowSubsetLeverage X T i) / (T.card - Fintype.card d : ℕ) := by
  have hE : T.erase i ∈ T.powersetCard (T.card - 1) :=
    Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, Finset.card_erase_of_mem hi⟩
  have hc : (T.card - Fintype.card d).choose (T.card - 1 - Fintype.card d) =
      T.card - Fintype.card d := by
    rw [show T.card - 1 - Fintype.card d = (T.card - Fintype.card d) - 1 by omega,
      Nat.choose_symm (by omega), Nat.choose_one_right]
  rw [rowVolumeDeletionStep, rowVolumeKernel_eq X T (T.card - 1) hT (by omega) (Nat.sub_le _ _),
    rowVolumePMF_toReal, rowVolumeWeight, if_pos hE, hc,
    rowSubsetVolume_erase_eq X T hi hT]
  have ht : ((T.card - Fintype.card d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hdt).ne'
  field_simp

private theorem pmf_eq_zero_of_not_mem (X : Matrix n d 𝕜) (T R : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card)
    (hR : R ∉ T.powersetCard s) : rowVolumePMF X T s hT hds hst R = 0 := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
  rw [rowVolumePMF_toReal, rowVolumeWeight, if_neg hR, zero_div, ENNReal.toReal_zero]

private theorem pmf_full_size (X : Matrix n d 𝕜) (T : Finset n)
    (hT : 0 < rowSubsetVolume X T) (hdt : Fintype.card d ≤ T.card) :
    rowVolumePMF X T T.card hT hdt le_rfl = pure T := by
  classical
  apply PMF.ext
  intro R
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change (rowVolumePMF X T T.card hT hdt le_rfl R).toReal = (PMF.pure T R).toReal
  rw [rowVolumePMF_toReal, rowVolumeWeight, Finset.powersetCard_self]
  by_cases hR : R = T
  · subst R
    simp [hT.ne', PMF.pure_apply]
  · simp [hR, PMF.pure_apply]

private theorem bind_deletionStep (X : Matrix n d 𝕜) (T : Finset n) (t : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hdt : Fintype.card d < t) (htt : t ≤ T.card) :
    (rowVolumePMF X T t hT hdt.le htt).bind (rowVolumeDeletionStep X) =
      rowVolumePMF X T (t - 1) hT (by omega) (by omega) := by
  classical
  calc
    _ = (rowVolumePMF X T t hT hdt.le htt).bind (rowVolumeKernel X (t - 1)) := by
      apply PMF.ext
      intro S
      rw [PMF.bind_apply, PMF.bind_apply]
      apply tsum_congr
      intro R
      by_cases hR : R ∈ T.powersetCard t
      · rw [rowVolumeDeletionStep, (Finset.mem_powersetCard.mp hR).2]
      · rw [pmf_eq_zero_of_not_mem X T R t hT hdt.le htt hR, zero_mul, zero_mul]
    _ = _ := rowVolumePMF_bind_kernel X T (t - 1) t hT (by omega) (by omega) htt

/-- The actual reverse-deletion recursion has precisely the fixed-size
row-volume law. Rank-destroying deletions have zero probability, so every
intermediate state is supported and the absorbing fallback is harmless.
Dereziński–Warmuth 2018, Theorem 2.
atlas: row-volume-sampling-deletion-law (partial) -/
theorem rowVolumeDeletionPMF_eq (X : Matrix n d 𝕜) (T : Finset n) (q : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hq : q + Fintype.card d ≤ T.card) :
    rowVolumeDeletionPMF X q T =
      rowVolumePMF X T (T.card - q) hT (by omega) (Nat.sub_le _ _) := by
  induction q with
  | zero =>
    simpa only [rowVolumeDeletionPMF, Nat.sub_zero] using (pmf_full_size X T hT (by omega)).symm
  | succ q ih =>
    rw [rowVolumeDeletionPMF, ih (by omega), bind_deletionStep X T (T.card - q) hT
      (by omega) (Nat.sub_le _ _)]
    congr 1

/-- Stopping after exactly `|T|-s` one-row deletions produces the requested
size-`s` row-volume PMF, including the empty-path case `s=|T|`.
Dereziński–Warmuth 2018, Theorem 2.
atlas: row-volume-sampling-deletion-law (partial)-/
theorem rowVolumeDeletionPMF_sub_eq (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    rowVolumeDeletionPMF X (T.card - s) T = rowVolumePMF X T s hT hds hst := by
  rw [rowVolumeDeletionPMF_eq X T (T.card - s) hT (by omega)]
  congr 1
  omega

/-- The probability measure of the actual finite reverse-deletion process. -/
def rowVolumeDeletionLaw (X : Matrix n d 𝕜) (T : Finset n) (q : ℕ) : Measure (Finset n) :=
  (rowVolumeDeletionPMF X q T).toMeasure

/-- The measure produced by the actual reverse-deletion process is the
fixed-size row-volume measure, without any general-position assumption.
Dereziński–Warmuth 2018, Theorem 2.
atlas: row-volume-sampling-deletion-law (partial)-/
theorem rowVolumeDeletionLaw_sub_eq (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    rowVolumeDeletionLaw X T (T.card - s) = rowVolumeLaw X T s hT hds hst := by
  unfold rowVolumeDeletionLaw rowVolumeLaw
  rw [rowVolumeDeletionPMF_sub_eq X T s hT hds hst]

end NLAlib
