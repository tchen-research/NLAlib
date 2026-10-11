import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Bounded stopping and the anytime bound for nonnegative supermartingales

Actual bounded hitting times and optional stopping give Ville's inequality. Passing
from finite horizons to the increasing union preserves the exact initial-mean constant.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace NLAlib

/-- Bounded optional stopping for a real supermartingale, obtained from Mathlib's actual
submartingale theorem by negation.
Source: bounded optional stopping; operator rederivations Section 3.4;
atlas `matrix-freedman` (partial). -/
theorem integral_stoppedValue_le_integral_zero_of_supermartingale
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ] {S : ℕ → Ω → ℝ} (hS : Supermartingale S ℱ μ)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime ℱ τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    (∫ ω, stoppedValue S τ ω ∂μ) ≤ ∫ ω, S 0 ω ∂μ := by
  have h := hS.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hτ
    (fun _ => bot_le) hbdd
  rw [stoppedValue_const] at h
  change (∫ ω, -S 0 ω ∂μ) ≤ ∫ ω, -(stoppedValue S τ ω) ∂μ at h
  rw [integral_neg, integral_neg, neg_le_neg_iff] at h
  exact h

/-- The actual finite-horizon hitting event of a nonnegative supermartingale has measure
at most its initial mean divided by the positive threshold.
Source: bounded optional stopping and Markov's inequality;
operator rederivations Section 3.4, atlas `matrix-freedman` (partial). -/
theorem measure_exists_le_nat_le_supermartingale_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {S : ℕ → Ω → ℝ} (hS : Supermartingale S ℱ μ)
    (hNonneg : ∀ k, 0 ≤ᵐ[μ] S k) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (μ {ω | ∃ k ≤ N, c ≤ S k ω}).toReal ≤ (∫ ω, S 0 ω ∂μ) / c := by
  let τ : Ω → ℕ∞ := fun ω => (hittingBtwn S (Ici c) 0 N ω : ℕ)
  have hτ : IsStoppingTime ℱ τ :=
    hS.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ N := fun ω => by
    change ((hittingBtwn S (Ici c) 0 N ω : ℕ) : ℕ∞) ≤ (N : ℕ∞)
    exact_mod_cast (hittingBtwn_le (u := S) (s := Ici c) (n := 0) (m := N) (ω := ω))
  let R : Ω → ℝ := stoppedValue S τ
  have hRI : Integrable R μ := integrable_stoppedValue ℕ hτ hS.integrable hbdd
  have hR0 : 0 ≤ᵐ[μ] R := by
    have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, 0 ≤ S k ω := ae_all_iff.mpr hNonneg
    filter_upwards [hall] with ω hω
    exact hω (τ ω).untopA
  have hcross : {ω | ∃ k ≤ N, c ≤ S k ω} ⊆ {ω | c ≤ R ω} := by
    intro ω hω
    obtain ⟨k, hk, hkc⟩ := hω
    exact stoppedValue_hittingBtwn_mem ⟨k, ⟨Nat.zero_le k, hk⟩, hkc⟩
  have hbound : c * (μ {ω | ∃ k ≤ N, c ≤ S k ω}).toReal ≤ ∫ ω, S 0 ω ∂μ := by
    calc c * (μ {ω | ∃ k ≤ N, c ≤ S k ω}).toReal ≤ c * (μ {ω | c ≤ R ω}).toReal :=
        mul_le_mul_of_nonneg_left (measureReal_mono hcross) hc.le
      _ ≤ ∫ ω, R ω ∂μ := mul_meas_ge_le_integral_of_nonneg hR0 hRI c
      _ ≤ ∫ ω, S 0 ω ∂μ := integral_stoppedValue_le_integral_zero_of_supermartingale hS hτ hbdd
  rw [le_div_iff₀ hc]
  simpa only [mul_comm] using hbound

/-- Ville's exact anytime inequality for an actual nonnegative real supermartingale:
`P(∃k, S_k≥c) ≤ E[S_0]/c`. No union bound over individual times is used.
Source: bounded optional stopping and continuity of measure on an increasing union;
operator rederivations `eq:freedmanparameter`, atlas `matrix-freedman` (partial). -/
theorem measure_exists_le_supermartingale_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {S : ℕ → Ω → ℝ} (hS : Supermartingale S ℱ μ)
    (hNonneg : ∀ k, 0 ≤ᵐ[μ] S k) {c : ℝ} (hc : 0 < c) :
    (μ {ω | ∃ k, c ≤ S k ω}).toReal ≤ (∫ ω, S 0 ω ∂μ) / c := by
  let E : ℕ → Set Ω := fun N => {ω | ∃ k ≤ N, c ≤ S k ω}
  have hmono : Monotone E := by
    intro a b hab ω hω
    obtain ⟨k, hk, hc⟩ := hω
    exact ⟨k, hk.trans hab, hc⟩
  have heq : {ω | ∃ k, c ≤ S k ω} = ⋃ N, E N := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, k, le_rfl, hk⟩
    · rintro ⟨N, k, hkN, hk⟩
      exact ⟨k, hk⟩
  have hbound : μ {ω | ∃ k, c ≤ S k ω} ≤ ENNReal.ofReal ((∫ ω, S 0 ω ∂μ) / c) := by
    rw [heq, hmono.measure_iUnion]
    apply iSup_le
    intro N
    calc μ (E N) = ENNReal.ofReal (μ (E N)).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top μ (E N))).symm
      _ ≤ ENNReal.ofReal ((∫ ω, S 0 ω ∂μ) / c) := ENNReal.ofReal_le_ofReal
        (measure_exists_le_nat_le_supermartingale_le hS hNonneg hc N)
  have h0 : 0 ≤ (∫ ω, S 0 ω ∂μ) / c := div_nonneg (integral_nonneg_of_ae (hNonneg 0)) hc.le
  simpa only [ENNReal.toReal_ofReal h0] using ENNReal.toReal_mono (by simp) hbound

end NLAlib
