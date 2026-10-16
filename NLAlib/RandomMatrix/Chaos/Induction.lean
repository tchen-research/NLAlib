import NLAlib.RandomMatrix.Chaos.ExpectationRecursion
import NLAlib.RandomMatrix.Chaos.DimensionBudget
import Mathlib.Logic.Equiv.Option

/-!
# Simultaneous ordinary and strong coefficient-array induction

This module isolates the exact finite recursion from the analytic linear-series
theorems. The final norm bounds instantiate both linear assumptions with proved
subgaussian estimates; no chaos bound is assumed here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace NLAlib

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

/-- Iterating ordinary and covariance-sensitive linear-series estimates gives
the corresponding degree-dependent chaos estimates. The common dimension
product controls all intermediate matrices, and the covariance branch always
uses a nonempty original row subset.
This is a reusable induction principle; the analytic linear estimates are
proved separately and supplied by the final chaos theorem. -/
theorem expectedDecoupledMatrixChaosNorm_bounds_of_linear_bounds
    (hν : ∀ i, Integrable id (ν i)) (a t : ℝ) (ha : 0 ≤ a) (ht : 1 ≤ t) (D : ℕ)
    (hordinary : ∀ (m n : Type u) [Fintype m] [Fintype n]
      [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n],
      Fintype.card m * Fintype.card n ≤ D → ∀ B : ι → Matrix m n ℝ,
      (∫ y : ι → ℝ, specNorm (∑ j, y j • B j) ∂Measure.pi ν) ≤
        (a * t) * (specNorm (coefficientRow B) + specNorm (coefficientColumn B)))
    (hstrong : ∀ (m n : Type u) [Fintype m] [Fintype n]
      [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n],
      Fintype.card m * Fintype.card n ≤ D → ∀ B : ι → Matrix m n ℝ,
      (∫ y : ι → ℝ, specNorm (∑ j, y j • B j) ∂Measure.pi ν) ≤
        a * (specNorm (coefficientRow B) + specNorm (coefficientColumn B)) +
          (a * t) * specNorm (coefficientEntryRows B)) (q : ℕ) :
    ∀ (τ : Type u) [Fintype τ] [DecidableEq τ], Fintype.card τ = q →
      ∀ (m n : Type u) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
      [Nonempty m] [Nonempty n] (A : (τ → ι) → Matrix m n ℝ),
      chaosDimensionProduct τ ι m n ≤ D →
      (expectedDecoupledMatrixChaosNorm ν A ≤ (2 * a * t) ^ q * chaosSigma A) ∧
      (expectedDecoupledMatrixChaosNorm ν A ≤
        (2 * a) ^ q * (chaosSigma A + (q : ℝ) / 2 * t ^ q * chaosCovariance A)) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro τ _ _ hcard m n _ _ _ _ _ _ A hsize
    by_cases hq : q = 0
    · haveI : IsEmpty τ := Fintype.card_eq_zero_iff.mp (hcard.trans hq)
      simp [hq, expectedDecoupledMatrixChaosNorm_of_isEmpty]
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
      haveI : Nonempty τ := Fintype.card_pos_iff.mp (hcard ▸ hqpos)
      let t₀ : τ := Classical.choice inferInstance
      let τ' := {t : τ // t ≠ t₀}
      let e : τ' ⊕ Unit ≃ τ :=
        ((Equiv.refl τ').sumCongr (Equiv.ofUnique Unit PUnit.{u + 1})).trans
          (Equiv.subtypeNeSumPUnit t₀)
      let r := Fintype.card τ'
      have hrq : r + 1 = q := by
        simpa only [Fintype.card_sum, Fintype.card_punit, hcard, r] using
          Fintype.card_congr e
      have hrlt : r < q := by omega
      let B := chaosReindexModes e A
      have hBsize : chaosDimensionProduct (τ' ⊕ Unit) ι m n ≤ D := by
        simpa only [chaosDimensionProduct, Fintype.card_congr e] using hsize
      have hR := ih r hrlt τ' rfl m (ι × n) (chaosRowCoefficients B)
        (by simpa only [chaosDimensionProduct_row] using hBsize)
      have hC := ih r hrlt τ' rfl (ι × m) n (chaosColumnCoefficients B)
        (by simpa only [chaosDimensionProduct_column] using hBsize)
      have hV := ih r hrlt τ' rfl ι (m × n) (chaosEntryCoefficients B)
        (by simpa only [chaosDimensionProduct_entry] using hBsize)
      have hshape : Fintype.card m * Fintype.card n ≤ D :=
        (card_mul_card_le_chaosDimensionProduct (τ := τ' ⊕ Unit)).trans hBsize
      have ht0 : 0 ≤ t := le_trans (by norm_num) ht
      have hbase0 : 0 ≤ 2 * a * t := by positivity
      have hRord : expectedDecoupledMatrixChaosNorm ν (chaosRowCoefficients B) ≤
          (2 * a * t) ^ r * chaosSigma B :=
        hR.1.trans (mul_le_mul_of_nonneg_left (chaosSigma_rowCoefficients_le B)
          (pow_nonneg hbase0 r))
      have hCord : expectedDecoupledMatrixChaosNorm ν (chaosColumnCoefficients B) ≤
          (2 * a * t) ^ r * chaosSigma B :=
        hC.1.trans (mul_le_mul_of_nonneg_left (chaosSigma_columnCoefficients_le B)
          (pow_nonneg hbase0 r))
      have hVord : expectedDecoupledMatrixChaosNorm ν (chaosEntryCoefficients B) ≤
          (2 * a * t) ^ r * chaosCovariance B :=
        hV.1.trans (mul_le_mul_of_nonneg_left (chaosSigma_entryCoefficients_le B)
          (pow_nonneg hbase0 r))
      have hRstrong : expectedDecoupledMatrixChaosNorm ν (chaosRowCoefficients B) ≤
          (2 * a) ^ r * (chaosSigma B + (r : ℝ) / 2 * t ^ r * chaosCovariance B) := by
        apply hR.2.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (chaosSigma_rowCoefficients_le B)
          (mul_le_mul_of_nonneg_left (chaosCovariance_rowCoefficients_le B) (by positivity))
      have hCstrong : expectedDecoupledMatrixChaosNorm ν (chaosColumnCoefficients B) ≤
          (2 * a) ^ r * (chaosSigma B + (r : ℝ) / 2 * t ^ r * chaosCovariance B) := by
        apply hC.2.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (chaosSigma_columnCoefficients_le B)
          (mul_le_mul_of_nonneg_left (chaosCovariance_columnCoefficients_le B) (by positivity))
      have hBo : expectedDecoupledMatrixChaosNorm ν B ≤
          (2 * a * t) ^ (r + 1) * chaosSigma B := by
        have hstep := expectedDecoupledMatrixChaosNorm_le_of_linear_bound ν B hν (a * t) 0
          (fun C => by simpa using hordinary m n hshape C)
        simp only [zero_mul, add_zero] at hstep
        calc
          _ ≤ (a * t) * ((2 * a * t) ^ r * chaosSigma B +
              (2 * a * t) ^ r * chaosSigma B) :=
            hstep.trans (mul_le_mul_of_nonneg_left (add_le_add hRord hCord) (by positivity))
          _ = _ := by rw [pow_succ]; ring
      have hBs : expectedDecoupledMatrixChaosNorm ν B ≤
          (2 * a) ^ (r + 1) *
            (chaosSigma B + ((r + 1 : ℕ) : ℝ) / 2 * t ^ (r + 1) * chaosCovariance B) := by
        have hstep := expectedDecoupledMatrixChaosNorm_le_of_linear_bound ν B hν a (a * t)
          (hstrong m n hshape)
        calc
          _ ≤ a * ((2 * a) ^ r *
              (chaosSigma B + (r : ℝ) / 2 * t ^ r * chaosCovariance B) +
              (2 * a) ^ r * (chaosSigma B + (r : ℝ) / 2 * t ^ r * chaosCovariance B)) +
              (a * t) * ((2 * a * t) ^ r * chaosCovariance B) :=
            hstep.trans (add_le_add
              (mul_le_mul_of_nonneg_left (add_le_add hRstrong hCstrong) ha)
              (mul_le_mul_of_nonneg_left hVord (by positivity)))
          _ ≤ _ := by
            have hp : t ^ r ≤ t ^ (r + 1) := by
              rw [pow_succ]
              nlinarith [pow_nonneg ht0 r]
            have hdiff : 0 ≤ a * (2 * a) ^ r * (r : ℝ) *
                (t ^ (r + 1) - t ^ r) * chaosCovariance B := by
              exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hp))
                (chaosCovariance_nonneg B)
            rw [pow_succ t r] at hdiff
            rw [mul_pow (2 * a) t r, pow_succ (2 * a) r, pow_succ t r]
            push_cast
            nlinarith only [hdiff]
      have heE := expectedDecoupledMatrixChaosNorm_reindexModes ν e A
      have heS := chaosSigma_reindexModes e A
      have heV := chaosCovariance_reindexModes e A
      constructor
      · rw [← heE, ← heS, ← hrq]
        exact hBo
      · rw [← heE, ← heS, ← heV, ← hrq]
        exact hBs

end NLAlib
