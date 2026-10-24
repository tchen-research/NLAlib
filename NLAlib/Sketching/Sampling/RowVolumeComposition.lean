import NLAlib.Sketching.Sampling.RowVolumeLaw
import NLAlib.ForMathlib.Probability.FinitePMF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Composition of row-volume sampling

Conditional row-volume sampling has an absorbing fallback on deficient or
malformed states. Those states have zero mass under a valid starting law.
Source: Dereziński–Warmuth 2018, Corollary 3.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

/-- Conditional row-volume sampling is total: invalid sample sizes or
deficient ambient row sets are absorbing. -/
def rowVolumeKernel (X : Matrix n d 𝕜) (s : ℕ) (T : Finset n) : PMF (Finset n) :=
  if hT : 0 < rowSubsetVolume X T then
    if hs : Fintype.card d ≤ s ∧ s ≤ T.card then
      rowVolumePMF X T s hT hs.1 hs.2
    else pure T
  else pure T

/-- On a valid state the total kernel is the intended conditional law. -/
theorem rowVolumeKernel_eq (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    rowVolumeKernel X s T = rowVolumePMF X T s hT hds hst := by
  simp [rowVolumeKernel, hT, hds, hst]

private theorem mass_mul_kernel (X : Matrix n d 𝕜) (T R S : Finset n) (s t : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s)
    (hst : s ≤ t) (htt : t ≤ T.card) (hR : R ∈ T.powersetCard t) :
    (rowVolumePMF X T t hT (hds.trans hst) htt R).toReal *
        (rowVolumeKernel X s R S).toReal =
      if S ∈ R.powersetCard s then rowSubsetVolume X S /
        ((((T.card - Fintype.card d).choose (t - Fintype.card d) : ℝ) *
          ((t - Fintype.card d).choose (s - Fintype.card d) : ℝ)) * rowSubsetVolume X T)
      else 0 := by
  have hRc := (Finset.mem_powersetCard.mp hR).2
  have hc₁ : ((T.card - Fintype.card d).choose (t - Fintype.card d) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (Nat.sub_le_sub_right htt _))
  have hc₂ : ((t - Fintype.card d).choose (s - Fintype.card d) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (Nat.sub_le_sub_right hst _))
  rw [rowVolumePMF_toReal, rowVolumeWeight, if_pos hR]
  by_cases hRp : 0 < rowSubsetVolume X R
  · rw [rowVolumeKernel_eq X R s hRp hds (hRc ▸ hst), rowVolumePMF_toReal,
      hRc, rowVolumeWeight]
    split_ifs
    · field_simp
    · simp
  · have hz : rowSubsetVolume X R = 0 := le_antisymm (not_lt.mp hRp) (rowSubsetVolume_nonneg X R)
    rw [hz, zero_div, zero_mul]
    split_ifs with hSR
    · have hSz : rowSubsetVolume X S = 0 := le_antisymm
        ((rowSubsetVolume_mono X (Finset.mem_powersetCard.mp hSR).1).trans_eq hz)
        (rowSubsetVolume_nonneg X S)
      rw [hSz, zero_div]
    · rfl

/-- Sampling `t` rows and then `s` rows from them has exactly the direct
size-`s` row-volume distribution. Singular intermediate states have zero
outer mass, so the total kernel's fallback cannot change this identity.
Dereziński–Warmuth 2018, Corollary 3.
atlas: row-volume-sampling-deletion-law (partial)-/
theorem rowVolumePMF_bind_kernel (X : Matrix n d 𝕜) (T : Finset n) (s t : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s)
    (hst : s ≤ t) (htt : t ≤ T.card) :
    (rowVolumePMF X T t hT (hds.trans hst) htt).bind (rowVolumeKernel X s) =
      rowVolumePMF X T s hT hds (hst.trans htt) := by
  classical
  apply PMF.ext
  intro S
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [PMF.toReal_bind_eq_sum]
  let den : ℝ := (((T.card - Fintype.card d).choose (t - Fintype.card d) : ℝ) *
    ((t - Fintype.card d).choose (s - Fintype.card d) : ℝ)) * rowSubsetVolume X T
  have hsum : (∑ R : Finset n,
      (rowVolumePMF X T t hT (hds.trans hst) htt R).toReal * (rowVolumeKernel X s R S).toReal) =
      ∑ R ∈ T.powersetCard t, if S ∈ R.powersetCard s then rowSubsetVolume X S / den else 0 := by
    calc
      _ = ∑ R ∈ T.powersetCard t,
          (rowVolumePMF X T t hT (hds.trans hst) htt R).toReal *
            (rowVolumeKernel X s R S).toReal := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro R _ hR
        rw [rowVolumePMF_toReal, rowVolumeWeight, if_neg hR, zero_div, zero_mul]
      _ = _ := Finset.sum_congr rfl fun R hR => mass_mul_kernel X T R S s t hT hds hst htt hR
  rw [hsum, Finset.sum_powersetCard_ite_mem T S s t hst,
    rowVolumePMF_toReal, rowVolumeWeight]
  split_ifs with hS
  · have hc := Nat.choose_mul (n := T.card - Fintype.card d)
      (k := t - Fintype.card d) (s := s - Fintype.card d) (Nat.sub_le_sub_right hst _)
    have he₁ : T.card - Fintype.card d - (s - Fintype.card d) = T.card - s := by omega
    have he₂ : t - Fintype.card d - (s - Fintype.card d) = t - s := by omega
    rw [he₁, he₂] at hc
    have hcr : ((T.card - Fintype.card d).choose (t - Fintype.card d) : ℝ) *
        ((t - Fintype.card d).choose (s - Fintype.card d) : ℝ) =
      ((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) *
        ((T.card - s).choose (t - s) : ℝ) := by exact_mod_cast hc
    have hn : ((T.card - s).choose (t - s) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (Nat.sub_le_sub_right htt s))
    dsimp only [den]
    rw [hcr, nsmul_eq_mul]
    field_simp
  · simp

end NLAlib
