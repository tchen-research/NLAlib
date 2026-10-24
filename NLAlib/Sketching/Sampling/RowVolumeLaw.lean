import NLAlib.Matrix.Basic.RowSubsetGram
import NLAlib.Probability.Sampling.FiniteSampling
import Mathlib.Probability.HasLaw

/-! # Fixed-size row-volume sampling

Literal row subsets receive their column-Gram determinant weights. The
ambient set is explicit so the same law describes the conditional output
of reverse deletion after any supported prefix.
Source: Dereziński–Warmuth 2018, Theorem 2 and Corollary 3.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

/-- The unnormalized fixed-size row-volume weight is zero outside the
prescribed ambient set or cardinality. -/
def rowVolumeWeight (X : Matrix n d 𝕜) (T S : Finset n) (s : ℕ) : ℝ :=
  if S ∈ T.powersetCard s then rowSubsetVolume X S else 0

/-- Fixed-size row-volume weights are nonnegative. -/
theorem rowVolumeWeight_nonneg (X : Matrix n d 𝕜) (T S : Finset n) (s : ℕ) :
    0 ≤ rowVolumeWeight X T S s := by
  unfold rowVolumeWeight
  split_ifs
  · exact rowSubsetVolume_nonneg X S
  · exact le_rfl

/-- The row-volume normalizer inside `T` is its exact binomial Gram weight. -/
theorem sum_rowVolumeWeight (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hds : Fintype.card d ≤ s) :
    (∑ S : Finset n, rowVolumeWeight X T S s) =
      ((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) * rowSubsetVolume X T := by
  classical
  simp only [rowVolumeWeight, ← Finset.sum_filter]
  have he : Finset.univ.filter (fun S : Finset n => S ∈ T.powersetCard s) =
      T.powersetCard s := by ext S; simp
  rw [he, sum_rowSubsetVolume_powersetCard X T s hds]

/-- A full-column-rank ambient restriction has positive row-volume mass at
every sample size between its column dimension and its number of rows. -/
theorem sum_rowVolumeWeight_pos (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    0 < ∑ S : Finset n, rowVolumeWeight X T S s := by
  rw [sum_rowVolumeWeight X T s hds]
  exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (Nat.sub_le_sub_right hst _))) hT

/-- The actual normalized row-volume PMF. A deficient ambient restriction
does not receive a fabricated probability law. -/
def rowVolumePMF (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    PMF (Finset n) :=
  finiteSamplingPMF (normalizedSamplingProbabilities (fun S => rowVolumeWeight X T S s))
    (sum_normalizedSamplingProbabilities _ (fun S => rowVolumeWeight_nonneg X T S s)
      (sum_rowVolumeWeight_pos X T s hT hds hst))

/-- The probability measure of actual size-`s` row-volume sampling inside
the ambient row set `T`. -/
def rowVolumeLaw (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    Measure (Finset n) := (rowVolumePMF X T s hT hds hst).toMeasure

/-- The real PMF mass is its normalized row-volume weight. -/
theorem rowVolumePMF_toReal (X : Matrix n d 𝕜) (T S : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (rowVolumePMF X T s hT hds hst S).toReal =
      rowVolumeWeight X T S s /
        (((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) * rowSubsetVolume X T) := by
  simp only [rowVolumePMF, finiteSamplingPMF, PMF.ofFintype_apply, ENNReal.coe_toReal]
  rw [coe_normalizedSamplingProbabilities _ (fun U => rowVolumeWeight_nonneg X T U s)
    (sum_rowVolumeWeight_pos X T s hT hds hst), sum_rowVolumeWeight X T s hds]

/-- Supported row-volume samples have exactly the requested size, lie in
the ambient set, and retain full column rank. Conversely every such subset
has positive mass.
atlas: row-volume-sampling-deletion-law (partial) -/
theorem mem_support_rowVolumePMF_iff (X : Matrix n d 𝕜) (T S : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    S ∈ (rowVolumePMF X T s hT hds hst).support ↔
      S ∈ T.powersetCard s ∧ 0 < rowSubsetVolume X S := by
  have hd : 0 < ((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) *
      rowSubsetVolume X T := by
    rw [← sum_rowVolumeWeight X T s hds]
    exact sum_rowVolumeWeight_pos X T s hT hds hst
  have he : S ∈ (rowVolumePMF X T s hT hds hst).support ↔
      0 < (rowVolumePMF X T s hT hds hst S).toReal := by
    rw [ENNReal.toReal_pos_iff, and_iff_left (PMF.apply_lt_top _ _), PMF.apply_pos_iff]
  rw [he, rowVolumePMF_toReal, div_pos_iff_of_pos_right hd, rowVolumeWeight]
  by_cases hS : S ∈ T.powersetCard s <;> simp [hS]

/-- The row-volume law is a probability measure. -/
instance rowVolumeLaw_isProbabilityMeasure (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    IsProbabilityMeasure (rowVolumeLaw X T s hT hds hst) := by
  unfold rowVolumeLaw
  infer_instance

/-- Every subset has exactly its normalized Gram determinant mass, with
zero mass outside the requested cardinality or ambient row set.
Dereziński–Warmuth 2018, Theorem 2.
atlas: row-volume-sampling-deletion-law (partial)-/
theorem rowVolumeLaw_singleton (X : Matrix n d 𝕜) (T S : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card) :
    (rowVolumeLaw X T s hT hds hst).real {S} =
      rowVolumeWeight X T S s /
        (((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) * rowSubsetVolume X T) := by
  rw [Measure.real, rowVolumeLaw, PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton S)]
  simp only [rowVolumePMF, finiteSamplingPMF, PMF.ofFintype_apply,
    ENNReal.coe_toReal]
  rw [coe_normalizedSamplingProbabilities _ (fun U => rowVolumeWeight_nonneg X T U s)
    (sum_rowVolumeWeight_pos X T s hT hds hst), sum_rowVolumeWeight X T s hds]

/-- Expectations under row-volume sampling are finite weighted sums. -/
theorem integral_rowVolumeLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (X : Matrix n d 𝕜) (T : Finset n) (s : ℕ)
    (hT : 0 < rowSubsetVolume X T) (hds : Fintype.card d ≤ s) (hst : s ≤ T.card)
    (f : Finset n → E) :
    ∫ S, f S ∂rowVolumeLaw X T s hT hds hst =
      ∑ S : Finset n, (rowVolumeWeight X T S s /
        (((T.card - Fintype.card d).choose (s - Fintype.card d) : ℝ) * rowSubsetVolume X T)) • f S := by
  classical
  rw [rowVolumeLaw, PMF.integral_eq_sum]
  simp only [rowVolumePMF, finiteSamplingPMF, PMF.ofFintype_apply, ENNReal.coe_toReal]
  simp_rw [coe_normalizedSamplingProbabilities _ (fun U => rowVolumeWeight_nonneg X T U s)
    (sum_rowVolumeWeight_pos X T s hT hds hst), sum_rowVolumeWeight X T s hds]

end NLAlib
