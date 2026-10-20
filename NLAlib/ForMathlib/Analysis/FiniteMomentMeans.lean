import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum

/-!
# Finite normalized power-moment comparisons

Jensen's inequality compares positive power means without a cardinality loss.
A uniform pointwise bound additionally controls every larger power by a
lower moment. Empty indexing types use the native zero-over-zero mean.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Real

/-- A finite normalized positive integer moment is bounded by the appropriate
fractional power of any higher normalized moment. Empty indexing types are
included using division by zero and a strictly positive outer exponent. -/
theorem sum_pow_div_card_le_rpow_sum_pow_div_card
    {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    {k j : ℕ} (hk : 0 < k) (hkj : k ≤ j) :
    (∑ i, f i ^ k) / (Fintype.card ι : ℝ) ≤
      ((∑ i, f i ^ j) / (Fintype.card ι : ℝ)) ^ ((k : ℝ) / j) := by
  have hj : 0 < j := hk.trans_le hkj
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  cases isEmpty_or_nonempty ι with
  | inl h =>
    simp [Real.zero_rpow (div_pos hkR hjR).ne']
  | inr h =>
    have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hθ0 : 0 ≤ (k : ℝ) / j := (div_pos hkR hjR).le
    have hθ1 : (k : ℝ) / j ≤ 1 := (div_le_one hjR).mpr (by exact_mod_cast hkj)
    have hw : (∑ _i : ι, (Fintype.card ι : ℝ)⁻¹) = 1 := by
      simp [hd.ne']
    have hJ := (Real.concaveOn_rpow hθ0 hθ1).le_map_sum
      (t := Finset.univ) (w := fun _ : ι => (Fintype.card ι : ℝ)⁻¹)
      (p := fun i => f i ^ j)
      (fun _ _ => inv_nonneg.mpr hd.le) hw (fun i _ => pow_nonneg (hf i) j)
    have hpower (i : ι) : (f i ^ j) ^ ((k : ℝ) / j) = f i ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hf i)]
      have he : (j : ℝ) * ((k : ℝ) / j) = k := by
        rw [mul_comm, div_mul_cancel₀ _ hjR.ne']
      rw [he, Real.rpow_natCast]
    simp only [smul_eq_mul] at hJ
    simp_rw [hpower] at hJ
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hJ
    simpa only [div_eq_mul_inv, mul_comm] using hJ

/-- A uniform bound absorbs extra powers while a lower positive moment
is controlled by a higher normalized moment. Zero bounds and empty finite
indexing types are included. -/
theorem sum_pow_div_card_le_pow_mul_rpow_sum_pow_div_card
    {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    {r : ℝ} (hr : 0 ≤ r) (hfr : ∀ i, f i ≤ r)
    {k j L : ℕ} (hk : 0 < k) (hkj : k ≤ j) (hkL : k ≤ L) :
    (∑ i, f i ^ L) / (Fintype.card ι : ℝ) ≤
      r ^ (L - k) *
        ((∑ i, f i ^ j) / (Fintype.card ι : ℝ)) ^ ((k : ℝ) / j) := by
  have hpoint (i : ι) : f i ^ L ≤ r ^ (L - k) * f i ^ k := by
    calc
      f i ^ L = f i ^ (L - k) * f i ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkL]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (hf i) (hfr i) _) (pow_nonneg (hf i) _)
  calc
    _ ≤ (∑ i, r ^ (L - k) * f i ^ k) / (Fintype.card ι : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hpoint i)
        (Nat.cast_nonneg _)
    _ = r ^ (L - k) * ((∑ i, f i ^ k) / (Fintype.card ι : ℝ)) := by
      rw [← Finset.mul_sum, mul_div_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_pow_div_card_le_rpow_sum_pow_div_card f hf hk hkj) (pow_nonneg hr _)

end Real
