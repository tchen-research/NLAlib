import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Fin

/-!
# Cardinality bounds for heavy coordinates

An energy budget controls the number of coordinates above an inverse-square-root
threshold. A logarithmically weighted coordinate envelope controls the number
above its corresponding logarithmic threshold. These are the counting facts
used in the finite rearrangement of Latała--van Handel--Youssef, Lemma 3.10.
-/

noncomputable section

namespace Finset

/-- An energy budget permits fewer than `r` coordinates strictly above
`a / sqrt r`. The ambient finite type may be empty. -/
theorem card_filter_div_sqrt_lt_of_sum_sq_le
    {ι : Type*} [Fintype ι] (f : ι → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hsum : ∑ i, f i ^ 2 ≤ a ^ 2)
    {r : ℕ} (hr : 0 < r) :
    ((univ : Finset ι).filter fun i => a / Real.sqrt r < f i).card < r := by
  classical
  let S := (univ : Finset ι).filter fun i => a / Real.sqrt r < f i
  by_contra hn
  have hcard : r ≤ S.card := Nat.le_of_not_gt hn
  have hS : S.Nonempty := card_pos.mp (lt_of_lt_of_le hr hcard)
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hsqrt := Real.sqrt_pos.mpr hr0
  have hsq : (a / Real.sqrt r) ^ 2 * r = a ^ 2 := by
    rw [div_pow, Real.sq_sqrt hr0.le]
    field_simp
  have hstrict : (S.card : ℝ) * (a / Real.sqrt r) ^ 2 < ∑ i ∈ S, f i ^ 2 := by
    calc
      _ = ∑ _i ∈ S, (a / Real.sqrt r) ^ 2 := by simp
      _ < _ := sum_lt_sum_of_nonempty hS (fun i hi => by
        have hfi := (mem_filter.mp hi).2
        have hnonneg := div_nonneg ha hsqrt.le
        nlinarith)
  have hpartial : ∑ i ∈ S, f i ^ 2 ≤ ∑ i, f i ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => sq_nonneg (f i))
  have hcard' : (r : ℝ) ≤ S.card := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcard' (sq_nonneg (a / Real.sqrt r))
  nlinarith

/-- A predicate supported on the first `r` positions has at most `r` members. -/
theorem card_filter_le_of_imp_val_lt
    {n r : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : ∀ i, P i → i.val < r) :
    ((univ : Finset (Fin n)).filter P).card ≤ r := by
  classical
  by_cases hr : r < n
  · have hsub : ((univ : Finset (Fin n)).filter P) ⊆
        Iio (⟨r, hr⟩ : Fin n) := by
      intro i hi
      exact mem_Iio.mpr (h i (mem_filter.mp hi).2)
    simpa using card_le_card hsub
  · exact (card_le_univ _).trans (by simpa using Nat.le_of_not_gt hr)

/-- If all coordinates from position `r` onward are small, at most `r`
coordinates exceed that threshold. -/
theorem card_filter_lt_le_of_le_from
    {n r : ℕ} (f : Fin n → ℝ) {t : ℝ} (h : ∀ i, r ≤ i.val → f i ≤ t) :
    ((univ : Finset (Fin n)).filter fun i => t < f i).card ≤ r := by
  classical
  apply card_filter_le_of_imp_val_lt
  intro i hi
  by_contra hn
  exact (not_lt_of_ge (h i (Nat.le_of_not_gt hn))) hi

/-- A nonnegative logarithmically weighted envelope bounds every coordinate
past a prescribed position. Positions are zero based, and the weight is
`sqrt (log (i+1))`, so the first coordinate is harmless. -/
theorem le_div_sqrt_log_of_weighted_le
    {n : ℕ} (f : Fin n → ℝ) {b : ℝ} (hf : ∀ i, 0 ≤ f i)
    (hweight : ∀ i, f i * Real.sqrt (Real.log (i.val + 1)) ≤ b)
    {r : ℕ} (hr : 1 < r) (i : Fin n) (hi : r ≤ i.val) :
    f i ≤ b / Real.sqrt (Real.log r) := by
  have hr1 : 1 < (r : ℝ) := by exact_mod_cast hr
  have hr0 := Real.log_pos hr1
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hr0)).mpr
  apply le_trans _ (hweight i)
  apply mul_le_mul_of_nonneg_left _ (hf i)
  apply Real.sqrt_le_sqrt
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.le_trans hi (Nat.le_add_right i.val 1)

/-- A logarithmic envelope implies the corresponding heavy-set counting
bound, without requiring the coordinates to be distinct or strictly ordered. -/
theorem card_filter_div_sqrt_log_le_of_weighted_le
    {n : ℕ} (f : Fin n → ℝ) {b : ℝ} (hf : ∀ i, 0 ≤ f i)
    (hweight : ∀ i, f i * Real.sqrt (Real.log (i.val + 1)) ≤ b)
    {r : ℕ} (hr : 1 < r) :
    ((univ : Finset (Fin n)).filter fun i =>
      b / Real.sqrt (Real.log r) < f i).card ≤ r :=
  card_filter_lt_le_of_le_from f (le_div_sqrt_log_of_weighted_le f hf hweight hr)

end Finset
