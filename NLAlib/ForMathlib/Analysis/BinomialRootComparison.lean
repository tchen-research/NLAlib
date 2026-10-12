import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp

/-!
# Binomially normalized root comparisons

The consecutive binomial exponent ratio converts integer-power product
inequalities into Szász's normalized root comparisons, including zero bases.
-/

noncomputable section
namespace NLAlib

/-- Consecutive binomial exponents turn a normalized-root comparison and
equality into the corresponding integer-power comparison and equality.
Nonnegative bases include zero. Horn--Johnson (2013), Theorem 7.8.11;
scalar helper for Szász's inequality. -/
theorem rpow_inv_choose_compare_iff_pow_compare {N k : ℕ} (hk : 1 ≤ k) (hkn : k < N)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (y ^ (1 / ((N - 1).choose k : ℝ)) ≤ x ^ (1 / ((N - 1).choose (k - 1) : ℝ)) ↔
      y ^ k ≤ x ^ (N - k)) ∧
    (y ^ (1 / ((N - 1).choose k : ℝ)) = x ^ (1 / ((N - 1).choose (k - 1) : ℝ)) ↔
      y ^ k = x ^ (N - k)) := by
  have hpNat : 0 < (N - 1).choose (k - 1) := Nat.choose_pos (by omega)
  have hqNat : 0 < (N - 1).choose k := Nat.choose_pos (by omega)
  have hp : (0 : ℝ) < (N - 1).choose (k - 1) := by exact_mod_cast hpNat
  have hq : (0 : ℝ) < (N - 1).choose k := by exact_mod_cast hqNat
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcNat : k * (N - 1).choose k = (N - k) * (N - 1).choose (k - 1) := by
    have h := Nat.choose_succ_right_eq (N - 1) (k - 1)
    have h1 : k - 1 + 1 = k := by omega
    have h2 : (N - 1) - (k - 1) = N - k := by omega
    simpa only [h1, h2, mul_comm] using h
  have hc : (k : ℝ) * ((N - 1).choose k : ℝ) =
      ((N - k : ℕ) : ℝ) * ((N - 1).choose (k - 1) : ℝ) := by exact_mod_cast hcNat
  let e : ℝ := (k : ℝ) * ((N - 1).choose k : ℝ)
  have he : 0 < e := mul_pos hkR hq
  have hye : (y ^ (1 / ((N - 1).choose k : ℝ))) ^ e = y ^ k := by
    rw [← Real.rpow_mul hy]
    have harg : (1 / ((N - 1).choose k : ℝ)) * e = k := by dsimp [e]; field_simp
    rw [harg, Real.rpow_natCast]
  have hxe : (x ^ (1 / ((N - 1).choose (k - 1) : ℝ))) ^ e = x ^ (N - k) := by
    rw [← Real.rpow_mul hx]
    have harg : (1 / ((N - 1).choose (k - 1) : ℝ)) * e = (N - k : ℕ) := by
      dsimp [e]
      rw [hc]
      field_simp
    rw [harg, Real.rpow_natCast]
  have hle := Real.rpow_le_rpow_iff (Real.rpow_nonneg hy (1 / ((N - 1).choose k : ℝ)))
    (Real.rpow_nonneg hx (1 / ((N - 1).choose (k - 1) : ℝ))) he
  have heq := Real.rpow_left_inj (Real.rpow_nonneg hy (1 / ((N - 1).choose k : ℝ)))
    (Real.rpow_nonneg hx (1 / ((N - 1).choose (k - 1) : ℝ))) he.ne'
  rw [hye, hxe] at hle heq
  exact ⟨hle.symm, heq.symm⟩

end NLAlib
