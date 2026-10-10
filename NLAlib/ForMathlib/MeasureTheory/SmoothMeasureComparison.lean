/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto, Oliver Butterley

The compact-set comparison proof is adapted from Mathlib's
MeasureTheory.Integral.RieszMarkovKakutani.Real.
-/
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Comparing measures using nonnegative smooth tests

Positive smooth compact tests supported in an open real set determine domination
of measures on that set. This supplies the absolute-continuity step of the scalar
weak-density argument in operator rederivations, Section 5, atlas
wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Manifold ENNReal

namespace NLAlib

/-- A compact subset of an open real set can be bounded in measure using integral
comparison only for nonnegative smooth compact tests in that open set.
Source: the smooth-cutoff version of Mathlib's Riesz--Markov measure comparison;
operator rederivations, Section 5, atlas wishart-lambda-min-tail (helper). -/
theorem measure_isCompact_le_of_integral_contDiff_le
    (μ ν : Measure ℝ) [μ.Regular] [ν.Regular] {U K : Set ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hbound : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν) :
    μ K ≤ ν K := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hνK' => ?_
  have hνK : ν K ≠ ⊤ := hνK'.ne
  have hμK : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have heps : (ε : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  obtain ⟨V, hKV, hV, hνV⟩ :=
    K.exists_isOpen_le_add ν (ENNReal.coe_ne_zero.mpr (ne_of_gt hε))
  obtain ⟨W, hW, hKW, hWV, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK (hV.inter hU) (subset_inter hKV hKU)
  obtain ⟨f, hf, hfrange, hfsupport, hfK⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ, ℝ)) (n := ⊤)
      hW hK.isClosed hKW
  have hfc : HasCompactSupport f := by
    rw [HasCompactSupport, tsupport, hfsupport]
    exact hWc
  have hfs : tsupport f ⊆ U := by
    rw [tsupport, hfsupport]
    exact hWV.trans inter_subset_right
  have hfiμ := hf.contDiff.continuous.integrable_of_hasCompactSupport (μ := μ) hfc
  have hfiν := hf.contDiff.continuous.integrable_of_hasCompactSupport (μ := ν) hfc
  have hf0 (x : ℝ) : 0 ≤ f x := (hfrange (mem_range_self x)).1
  have hf1 (x : ℝ) : f x ≤ 1 := (hfrange (mem_range_self x)).2
  have hfV (x : ℝ) : f x ≤ V.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ V
    · simpa [hx] using hf1 x
    · have hfx : f x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        rw [tsupport, hfsupport] at h
        exact hx ((hWV h).1)
      simp [hx, hfx]
  have hKf (x : ℝ) : K.indicator (fun _ => (1 : ℝ)) x ≤ f x := by
    by_cases hx : x ∈ K
    · simp [hx, (hfK x).mp hx]
    · simpa [hx] using hf0 x
  have hνVtop : ν V < ⊤ := hνV.trans_lt (by finiteness)
  have hm : μ.real K ≤ ν.real K + ε := by
    calc
      μ.real K = ∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂μ :=
        (integral_indicator_one hK.measurableSet).symm
      _ ≤ ∫ x, f x ∂μ := integral_mono
        ((continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet)
        hfiμ hKf
      _ ≤ ∫ x, f x ∂ν := hbound f hf.contDiff hfc hfs hf0
      _ ≤ ∫ x, V.indicator (fun _ => (1 : ℝ)) x ∂ν := integral_mono hfiν
        ((integrableOn_const hνVtop.ne).integrable_indicator hV.measurableSet) hfV
      _ ≤ ν.real K + ε := by
        have hi : (∫ x, V.indicator (fun _ => (1 : ℝ)) x ∂ν) = ν.real V :=
          integral_indicator_one hV.measurableSet
        rw [hi]
        have hh := (ENNReal.toReal_le_toReal hνVtop.ne (by finiteness)).mpr hνV
        simpa only [measureReal_def, ENNReal.toReal_add hνK heps,
          ENNReal.coe_toReal] using hh
  apply (ENNReal.toReal_le_toReal hμK (by finiteness)).mp
  simpa only [measureReal_def, ENNReal.toReal_add hνK heps,
    ENNReal.coe_toReal] using hm

/-- Nonnegative smooth compact tests in an open real set imply domination of the
restriction to that set. This proves measure domination, and hence absolute
continuity when the comparison measure is a multiple of Lebesgue measure.
Source: operator rederivations, Section 5, interval alternative;
atlas wishart-lambda-min-tail (helper). -/
theorem measure_restrict_le_of_integral_contDiff_le
    (μ ν : Measure ℝ) [μ.Regular] [ν.Regular] {U : Set ℝ} (hU : IsOpen U)
    (hbound : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν) :
    μ.restrict U ≤ ν := by
  have hopen (V : Set ℝ) (hV : IsOpen V) : μ.restrict U V ≤ ν V := by
    rw [Measure.restrict_apply hV.measurableSet, (hV.inter hU).measure_eq_iSup_isCompact μ]
    refine iSup_le fun K => iSup_le fun hKV => iSup_le fun hK => ?_
    exact (measure_isCompact_le_of_integral_contDiff_le μ ν hU hK
      (hKV.trans inter_subset_right) hbound).trans (measure_mono (hKV.trans inter_subset_left))
  apply Measure.le_iff'.mpr
  intro s
  rw [s.measure_eq_iInf_isOpen ν]
  refine le_iInf fun V => le_iInf fun hsV => le_iInf fun hV => ?_
  exact (measure_mono hsV).trans (hopen V hV)

end NLAlib
