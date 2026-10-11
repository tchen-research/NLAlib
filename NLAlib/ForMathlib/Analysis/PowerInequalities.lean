import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Scalar power comparisons for polynomial trace inequalities

Oppositely paired powers and the integer Young inequality are the scalar inputs
to the deterministic noncommutative Khintchine argument. All endpoint cases are
ordinary natural powers, so no division by a random moment is needed.
Source: operator manuscript `eq:scalarpair` and `eq:young`.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

/-- Paired mixed powers are bounded by the two endpoint powers for nonnegative
scalars. Source: manuscript `eq:scalarpair`; supports `noncommutative-khintchine`. -/
theorem mixed_pow_add_mixed_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {m l : ℕ} (hl : l ≤ m) :
    x ^ l * y ^ (m - l) + x ^ (m - l) * y ^ l ≤ x ^ m + y ^ m := by
  have hpowx : x ^ l * x ^ (m - l) = x ^ m := by rw [← pow_add, Nat.add_sub_of_le hl]
  have hpowy : y ^ l * y ^ (m - l) = y ^ m := by rw [← pow_add, Nat.add_sub_of_le hl]
  rcases le_total y x with hxy | hxy
  · have h1 : 0 ≤ x ^ l - y ^ l := sub_nonneg.mpr (pow_le_pow_left₀ hy hxy l)
    have h2 : 0 ≤ x ^ (m - l) - y ^ (m - l) :=
      sub_nonneg.mpr (pow_le_pow_left₀ hy hxy _)
    have h := mul_nonneg h1 h2
    nlinarith [hpowx, hpowy]
  · have h1 : 0 ≤ y ^ l - x ^ l := sub_nonneg.mpr (pow_le_pow_left₀ hx hxy l)
    have h2 : 0 ≤ y ^ (m - l) - x ^ (m - l) :=
      sub_nonneg.mpr (pow_le_pow_left₀ hx hxy _)
    have h := mul_nonneg h1 h2
    nlinarith [hpowx, hpowy]

/-- Integer Young's inequality, including zero scalars and order one.
Source: operator manuscript `eq:young`; supports `noncommutative-khintchine`.
The proof reuses Mathlib's convex Bernoulli inequality for positive `y`. -/
theorem nat_mul_mul_pow_le_pow_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {p : ℕ} (hp : 1 ≤ p) :
    (p : ℝ) * x * y ^ (p - 1) ≤ x ^ p + (p - 1 : ℕ) * y ^ p := by
  by_cases hy0 : y = 0
  · subst y
    by_cases hp1 : p = 1
    · subst p; simp
    · have hpos : 0 < p - 1 := by omega
      simp only [zero_pow hpos.ne', mul_zero]
      positivity
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hratio : -1 ≤ x / y - 1 := by linarith [div_nonneg hx hy]
  have hbern := one_add_mul_self_le_rpow_one_add hratio
    (p := (p : ℝ)) (by exact_mod_cast hp)
  rw [add_sub_cancel, Real.rpow_natCast] at hbern
  have h := mul_le_mul_of_nonneg_right hbern (pow_nonneg hy p)
  have hquot : (x / y) ^ p * y ^ p = x ^ p := by rw [div_pow]; field_simp
  have hprev : y ^ (p - 1) * y = y ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  rw [hquot] at h
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hp)
  rw [hcast]
  have hleft : (1 + (p : ℝ) * (x / y - 1)) * y ^ p =
      y ^ p + (p : ℝ) * x * y ^ (p - 1) - (p : ℝ) * y ^ p := by
    rw [← hprev]
    field_simp
    ring
  rw [hleft] at h
  linarith

/-- The scalar polynomial mean-value inequality at an odd natural power.
Source: manuscript `lem:meanvalue`; supports the individual sign-flip proof
of `noncommutative-khintchine`. Negative scalars and exponent zero are included. -/
theorem sub_mul_sub_pow_le_of_even {m : ℕ} (hm : Even m) (a b : ℝ) :
    (a - b) * (a ^ (m + 1) - b ^ (m + 1)) ≤
      ((m + 1 : ℕ) : ℝ) / 2 * (a - b) ^ 2 * (a ^ m + b ^ m) := by
  let T := ∑ l ∈ Finset.range (m + 1), |a| ^ l * |b| ^ (m - l)
  have hrefl : (∑ l ∈ Finset.range (m + 1), |a| ^ (m - l) * |b| ^ l) = T := by
    calc _ = ∑ l ∈ Finset.range (m + 1),
        |a| ^ (m - l) * |b| ^ (m - (m - l)) := by
          refine Finset.sum_congr rfl fun l hl => ?_
          rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))]
      _ = T := by
        simpa only [Nat.add_sub_cancel] using
          Finset.sum_range_reflect (fun l => |a| ^ l * |b| ^ (m - l)) (m + 1)
  have hpair := Finset.sum_le_sum fun l (hl : l ∈ Finset.range (m + 1)) =>
    mixed_pow_add_mixed_pow_le (abs_nonneg a) (abs_nonneg b)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))
  have hT : T ≤ ((m + 1 : ℕ) : ℝ) / 2 * (a ^ m + b ^ m) := by
    simp only [Finset.sum_add_distrib, hrefl, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, hm.pow_abs] at hpair
    change T + T ≤ _ at hpair
    linarith
  have hsum : (∑ l ∈ Finset.range (m + 1), a ^ l * b ^ (m - l)) ≤ T := by
    apply Finset.sum_le_sum
    intro l _
    simpa only [abs_mul, abs_pow] using le_abs_self (a ^ l * b ^ (m - l))
  have hgeom := (Commute.all a b).mul_geom_sum₂ (m + 1)
  simp only [Nat.add_sub_cancel] at hgeom
  calc (a - b) * (a ^ (m + 1) - b ^ (m + 1)) =
        (a - b) ^ 2 * (∑ l ∈ Finset.range (m + 1), a ^ l * b ^ (m - l)) := by
          rw [← hgeom]; ring
    _ ≤ (a - b) ^ 2 * T := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ (a - b) ^ 2 * (((m + 1 : ℕ) : ℝ) / 2 * (a ^ m + b ^ m)) :=
      mul_le_mul_of_nonneg_left hT (sq_nonneg _)
    _ = _ := by ring

/-- Taking the nonnegative `2p`-th root of an integer moment bound gives
the square-root constant, including zero moments and zero parameters.
Source: final rooted form in manuscript `thm:khintchine`; supports
`noncommutative-khintchine`. -/
theorem rpow_le_sqrt_mul_rpow_of_nat_pow_le
    {M V q : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hq : 0 ≤ q)
    {p : ℕ} (hp : 1 ≤ p) (hbound : M ≤ q ^ p * V) :
    M ^ (1 / (2 * (p : ℝ))) ≤ Real.sqrt q * V ^ (1 / (2 * (p : ℝ))) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hr : (p : ℝ) * (1 / (2 * (p : ℝ))) = (1 / 2 : ℝ) := by
    field_simp
  have h := Real.rpow_le_rpow hM hbound (by positivity : 0 ≤ 1 / (2 * (p : ℝ)))
  rw [Real.mul_rpow (pow_nonneg hq p) hV, ← Real.rpow_natCast,
    ← Real.rpow_mul hq, hr, ← Real.sqrt_eq_rpow] at h
  exact h

end NLAlib
