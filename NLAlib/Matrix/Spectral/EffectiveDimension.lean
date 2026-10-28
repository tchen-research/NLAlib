/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# Finite spectral estimates from effective dimension

Two elementary finite-sum estimates control the eigenvalue cutoff and the spectral
tail from `∑ lam/(lam+μ)`. Neither requires a limiting measure nor an integral.
Source: Frangella–Tropp–Udell 2023, Theorem 5.1 proof; the tail-sum rearrangement is
the equivalent finite-sum route in the accompanying solver derivations.
Atlas: `nystrom-pcg` (spectral-budget kernel).
-/

noncomputable section
namespace NLAlib

/-- Effective dimension of a finite nonnegative spectrum at regularization `μ>0`. -/
def effectiveDimensionOfSpectrum {ι : Type*} [Fintype ι] (lam : ι → ℝ) (μ : ℝ) : ℝ :=
  ∑ i, lam i / (lam i + μ)

private theorem threshold_le_mul_ridgeFraction {x t μ : ℝ}
    (hx : 0 ≤ x) (hμ : 0 < μ) (htx : t ≤ x) :
    t ≤ (t + μ) * (x / (x + μ)) := by
  rw [← mul_div_assoc, le_div_iff₀ (add_pos_of_nonneg_of_pos hx hμ)]
  nlinarith

private theorem le_mul_ridgeFraction_of_le {x t μ : ℝ}
    (hx : 0 ≤ x) (hμ : 0 < μ) (hxt : x ≤ t) :
    x ≤ (t + μ) * (x / (x + μ)) := by
  rw [← mul_div_assoc, le_div_iff₀ (add_pos_of_nonneg_of_pos hx hμ)]
  nlinarith

/-- A set of eigenvalues above a threshold pays at least its cardinality times the
threshold in the rescaled effective dimension. -/
theorem card_mul_le_mul_effectiveDimensionOfSpectrum {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t)
    (S : Finset ι) (hS : ∀ i ∈ S, t ≤ lam i) :
    (S.card : ℝ) * t ≤ (t + μ) * effectiveDimensionOfSpectrum lam μ := by
  have hsum : ∑ i ∈ S, lam i / (lam i + μ) ≤ effectiveDimensionOfSpectrum lam μ := by
    apply Finset.sum_le_univ_sum_of_nonneg
    intro i
    exact div_nonneg (hlam i) (add_nonneg (hlam i) hμ.le)
  calc
    _ = ∑ _i ∈ S, t := by simp
    _ ≤ ∑ i ∈ S, (t + μ) * (lam i / (lam i + μ)) :=
      Finset.sum_le_sum fun i hi => threshold_le_mul_ridgeFraction (hlam i) hμ (hS i hi)
    _ = (t + μ) * ∑ i ∈ S, lam i / (lam i + μ) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (add_nonneg ht hμ.le)

/-- **Effective-dimension tail bound.** If a head set has at least the effective dimension
many eigenvalues and separates a nonnegative spectrum at a threshold, the remaining sum
is at most `μ` times the effective dimension. -/
theorem sum_compl_le_mul_effectiveDimensionOfSpectrum {ι : Type*} [Fintype ι]
    [DecidableEq ι] (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) {μ t : ℝ}
    (hμ : 0 < μ) (ht : 0 ≤ t) (S : Finset ι)
    (hhead : ∀ i ∈ S, t ≤ lam i) (htail : ∀ i ∉ S, lam i ≤ t)
    (hcard : effectiveDimensionOfSpectrum lam μ ≤ S.card) :
    ∑ i ∈ Sᶜ, lam i ≤ μ * effectiveDimensionOfSpectrum lam μ := by
  have hh : (S.card : ℝ) * t ≤ (t + μ) * ∑ i ∈ S, lam i / (lam i + μ) := by
    calc
      _ = ∑ _i ∈ S, t := by simp
      _ ≤ ∑ i ∈ S, (t + μ) * (lam i / (lam i + μ)) :=
        Finset.sum_le_sum fun i hi => threshold_le_mul_ridgeFraction (hlam i) hμ (hhead i hi)
      _ = _ := (Finset.mul_sum ..).symm
  have hr : ∑ i ∈ Sᶜ, lam i ≤ (t + μ) * ∑ i ∈ Sᶜ, lam i / (lam i + μ) := by
    calc
      _ ≤ ∑ i ∈ Sᶜ, (t + μ) * (lam i / (lam i + μ)) :=
        Finset.sum_le_sum fun i hi => le_mul_ridgeFraction_of_le (hlam i) hμ
          (htail i (Finset.mem_compl.mp hi))
      _ = _ := (Finset.mul_sum ..).symm
  have hsplit : (∑ i ∈ S, lam i / (lam i + μ)) +
      (∑ i ∈ Sᶜ, lam i / (lam i + μ)) = effectiveDimensionOfSpectrum lam μ := by
    exact Finset.sum_add_sum_compl S _
  have hc := mul_le_mul_of_nonneg_right hcard ht
  rw [← hsplit] at hc ⊢
  nlinarith only [hh, hr, hc]

/-- For decreasing eigenvalues, an index past `(1+1/γ)d_eff` has eigenvalue at most `γμ`.
The index is one-based in the cardinality hypothesis. -/
theorem apply_le_mul_of_effectiveDimensionOfSpectrum_le {n : ℕ}
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hmono : Antitone lam)
    {μ γ : ℝ} (hμ : 0 < μ) (hγ : 0 < γ) (j : Fin n)
    (hj : (1 + 1 / γ) * effectiveDimensionOfSpectrum lam μ ≤ (j.val : ℝ) + 1) :
    lam j ≤ γ * μ := by
  have hc := card_mul_le_mul_effectiveDimensionOfSpectrum lam hlam hμ (hlam j)
    (Finset.Iic j) (fun i hi => hmono (Finset.mem_Iic.mp hi))
  simp only [Fin.card_Iic, Nat.cast_add, Nat.cast_one] at hc
  by_contra hbad
  have hjpos : 0 < lam j := lt_trans (mul_pos hγ hμ) (lt_of_not_ge hbad)
  have hD : 0 < effectiveDimensionOfSpectrum lam μ := by
    apply lt_of_lt_of_le (div_pos hjpos (add_pos hjpos hμ))
    exact Finset.single_le_sum (fun i _ => div_nonneg (hlam i)
      (add_nonneg (hlam i) hμ.le)) (Finset.mem_univ j)
  have hb := mul_le_mul_of_nonneg_right hj hγ.le
  have he : (1 + 1 / γ) * effectiveDimensionOfSpectrum lam μ * γ =
      (1 + γ) * effectiveDimensionOfSpectrum lam μ := by field_simp [ne_of_gt hγ]; ring
  rw [he] at hb
  have h1 := mul_le_mul_of_nonneg_right hc hγ.le
  have h2 := mul_le_mul_of_nonneg_right hb (hlam j)
  have h3 := mul_pos hD (sub_pos.mpr (lt_of_not_ge hbad))
  nlinarith only [h1, h2, h3]

/-- The spectral tail after an integer `k≥d_eff` is at most `μd_eff`, including an empty
tail. This is the effective-dimension estimate needed for the FTU sketch budget. -/
theorem sum_filter_ge_le_mul_effectiveDimensionOfSpectrum {n : ℕ}
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hmono : Antitone lam)
    {μ : ℝ} (hμ : 0 < μ) (k : ℕ) (hk : effectiveDimensionOfSpectrum lam μ ≤ k) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), lam i ≤
      μ * effectiveDimensionOfSpectrum lam μ := by
  by_cases hkn : k < n
  · let j : Fin n := ⟨k, hkn⟩
    have h := sum_compl_le_mul_effectiveDimensionOfSpectrum lam hlam hμ (hlam j)
      (Finset.Iio j) (fun i hi => hmono (Finset.mem_Iio.mp hi).le)
      (fun i hi => hmono (le_of_not_gt (fun h => hi (Finset.mem_Iio.mpr h))))
      (by simpa [j] using hk)
    convert h using 1
    congr 1
    ext i
    simp [j, Finset.mem_Iio, Fin.lt_def, not_lt]
  · have hz : Finset.univ.filter (fun i : Fin n => k ≤ i.val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := (Finset.mem_filter.mp hi).2
      omega
    rw [hz, Finset.sum_empty]
    apply mul_nonneg hμ.le
    exact Finset.sum_nonneg fun i _ => div_nonneg (hlam i) (add_nonneg (hlam i) hμ.le)

end NLAlib
