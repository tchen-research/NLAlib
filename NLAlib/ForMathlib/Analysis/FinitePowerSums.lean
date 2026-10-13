import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Finite nonnegative power-sum comparisons

Monotonicity of finite scalar power norms and the sharp cardinality comparison.
These scalar facts support the Schatten comparisons in Bhatia (1997), §IV.2.
-/

noncomputable section

namespace NLAlib

/-- A finite sum of nonnegative powers is bounded by the power of the sum at
every exponent at least one. Scalar helper for Schatten comparisons.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) {r : ℝ} (hr : 1 ≤ r) :
    (∑ i ∈ s, f i ^ r) ≤ (∑ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (add_le_add_right (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))) _).trans
      (Real.add_rpow_le_rpow_add (hf a (Finset.mem_insert_self a s))
        (Finset.sum_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))) hr)

/-- Finite nonnegative power norms decrease with their positive exponent.
This includes the empty list.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem sum_rpow_root_le_sum_rpow_root {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i ∈ s, f i ^ q) ^ (1 / q) ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) := by
  have hq : 0 < q := hp.trans_le hpq
  have hr : 1 ≤ q / p := (one_le_div hp).mpr hpq
  have hS : 0 ≤ ∑ i ∈ s, f i ^ p := Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hf i hi) p)
  have h := sum_rpow_le_rpow_sum s (fun i => f i ^ p)
    (fun i hi => Real.rpow_nonneg (hf i hi) p) hr
  have hmul : p * (q / p) = q := by field_simp
  have hsum : (∑ i ∈ s, f i ^ q) = ∑ i ∈ s, (f i ^ p) ^ (q / p) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hf i hi), hmul]
  rw [← hsum] at h
  have hroot := Real.rpow_le_rpow
    (Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hf i hi) q)) h (one_div_nonneg.mpr hq.le)
  rw [← Real.rpow_mul hS] at hroot
  have hexp : q / p * (1 / q) = 1 / p := by field_simp
  rwa [hexp] at hroot

/-- The sharp cardinality comparison for finite nonnegative power norms.
Zero cardinality causes no exception.
Bhatia (1997), §IV.2; matrix toolkit derivations, (10)–(12). -/
theorem sum_rpow_root_le_card_rpow_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i ∈ s, f i ^ p) ^ (1 / p) ≤
      (s.card : ℝ) ^ (1 / p - 1 / q) * (∑ i ∈ s, f i ^ q) ^ (1 / q) := by
  have hq : 0 < q := hp.trans_le hpq
  have hr : 1 ≤ q / p := (one_le_div hp).mpr hpq
  have hS : 0 ≤ ∑ i ∈ s, f i ^ p := Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hf i hi) p)
  have hQ : 0 ≤ ∑ i ∈ s, f i ^ q := Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hf i hi) q)
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s hr
    (f := fun i => f i ^ p) (fun i hi => Real.rpow_nonneg (hf i hi) p)
  have hmul : p * (q / p) = q := by field_simp
  have hsum : (∑ i ∈ s, (f i ^ p) ^ (q / p)) = ∑ i ∈ s, f i ^ q := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hf i hi), hmul]
  rw [hsum] at h
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg hS _) h (one_div_nonneg.mpr hq.le)
  rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg s.card) _) hQ,
    ← Real.rpow_mul hS, ← Real.rpow_mul (Nat.cast_nonneg s.card)] at hroot
  have hleft : q / p * (1 / q) = 1 / p := by field_simp
  have hright : (q / p - 1) * (1 / q) = 1 / p - 1 / q := by field_simp
  rwa [hleft, hright] at hroot

end NLAlib
