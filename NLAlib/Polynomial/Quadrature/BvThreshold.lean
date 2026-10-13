import NLAlib.Polynomial.Quadrature.Basic
import NLAlib.ForMathlib.Analysis.FiniteProductBounds

/-! # Finite-product BV envelopes and the explicit eventual quadrature cutoff

The scalar arithmetic uses the smaller focused-reroute cutoff, with no division
by the variation bound, so variation zero is included.
-/
noncomputable section
namespace NLAlib

private theorem cast_half_mul_succ (ν : ℕ) :
    ((ν * (ν + 1) / 2 : ℕ) : ℝ) = (ν : ℝ) * (ν + 1) / 2 := by
  have he := Nat.even_iff.mp (Nat.even_mul_succ_self ν)
  have h := Nat.div_add_mod (ν * (ν + 1)) 2
  rw [he, add_zero] at h
  have hR := congrArg (fun n : ℕ => (n : ℝ)) h
  push_cast at hR
  linarith

/-- The exact integer threshold dominates its real-valued expression with the
ceiling removed. Source: focused reroutes, eventual quadrature threshold theorem. -/
theorem mul_pow_le_sub_of_quadratureBvThreshold_le {ν n : ℕ}
    (hn : quadratureBvThreshold ν ≤ n) :
    (105 / 16 : ℝ) * ν * 2 ^ ν ≤ (n : ℝ) - (ν : ℝ) * (ν + 1) / 2 := by
  have hc : 105 * ν * 2 ^ ν ≤ 16 * ((105 * ν * 2 ^ ν + 15) / 16) := by omega
  have hs : ν * (ν + 1) / 2 ≤ n := by unfold quadratureBvThreshold at hn; omega
  have hN : 105 * ν * 2 ^ ν ≤ 16 * (n - ν * (ν + 1) / 2) := by
    unfold quadratureBvThreshold at hn
    omega
  have hR := congrArg (fun n : ℕ => (n : ℝ)) (Nat.sub_add_cancel hs)
  push_cast at hR
  have hCast : (105 : ℝ) * ν * 2 ^ ν ≤ 16 * ((n : ℝ) - ((ν * (ν + 1) / 2 : ℕ) : ℝ)) := by
    exact_mod_cast hN
  rw [cast_half_mul_succ] at hCast
  linarith

/-- A coefficient bounded by the exact descending-factorial BV denominator has
the sharper finite-product power envelope beyond a cutoff. Source: focused reroutes,
finite product replaces an exponential loss lemma. -/
theorem abs_le_power_envelope_of_descFactorial {ν n k : ℕ} {V a : ℝ}
    (hV : 0 ≤ V) (hnν : ν ≤ n) (hk : n < k)
    (hs : (ν : ℝ) * (ν + 1) / 2 < n + 1)
    (ha : |a| ≤ 2 * V / (Real.pi * (k.descFactorial (ν + 1) : ℝ))) :
    |a| ≤ (2 * V / (Real.pi * (1 - ((ν : ℝ) * (ν + 1) / 2) / (n + 1)))) /
      (k : ℝ) ^ (ν + 1) := by
  let s := (ν : ℝ) * (ν + 1) / 2
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hkn : (n + 1 : ℝ) ≤ k := by exact_mod_cast (show n + 1 ≤ k by omega)
  have hd : 0 < 1 - s / (n + 1) := sub_pos.mpr ((div_lt_one hn0).mpr hs)
  have hdiv : s / k ≤ s / (n + 1) := div_le_div_of_nonneg_left hs0 hn0 hkn
  have hprod := pow_mul_one_sub_le_cast_descFactorial (show ν < k by omega)
  have hlow : (k : ℝ) ^ (ν + 1) * (1 - s / (n + 1)) ≤
      (k.descFactorial (ν + 1) : ℝ) := by
    refine (mul_le_mul_of_nonneg_left (sub_le_sub_left hdiv 1) (pow_nonneg hk0.le _)).trans hprod
  have hlpos : 0 < (k : ℝ) ^ (ν + 1) * (1 - s / (n + 1)) := by positivity
  have hdp : 0 < (k.descFactorial (ν + 1) : ℝ) := hlpos.trans_le hlow
  refine ha.trans ?_
  have hle := div_le_div_of_nonneg_left (show 0 ≤ 2 * V by positivity)
    (mul_pos Real.pi_pos hlpos) (mul_le_mul_of_nonneg_left hlow Real.pi_pos.le)
  convert hle using 1
  dsimp [s]
  field_simp

/-- At the explicit smaller cutoff, the stronger finite-block error constant is
bounded by the corrected eventual constant. Source: focused reroutes, eventual
quadrature threshold theorem. The comparison does not divide by `V`.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem bv_stronger_rate_le_eventual_of_quadratureBvThreshold_le {ν n : ℕ} {V : ℝ}
    (hν : 1 ≤ ν) (hn : quadratureBvThreshold ν ≤ n) (hV : 0 ≤ V) :
    14 * V / (Real.pi * (1 - ((ν : ℝ) * (ν + 1) / 2) / (n + 1)) * (n : ℝ) ^ (ν + 1)) ≤
      32 * V / (15 * Real.pi * ν * (2 * (n : ℝ) + 1 - ν) ^ ν) := by
  let s := (ν : ℝ) * (ν + 1) / 2
  let d := 1 - s / (n + 1)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hνR : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hpow : (1 : ℝ) ≤ 2 ^ ν := one_le_pow₀ (by norm_num)
  have hbig : (105 / 16 : ℝ) ≤ (105 / 16 : ℝ) * ν * 2 ^ ν := by
    have h := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg ν : (0 : ℝ) ≤ ν)
    nlinarith
  have hc := mul_pow_le_sub_of_quadratureBvThreshold_le hn
  change (105 / 16 : ℝ) * ν * 2 ^ ν ≤ (n : ℝ) - s at hc
  have hn2R : (2 : ℝ) ≤ n := by linarith
  have hsn : s < (n : ℝ) + 1 := by linarith
  have hnνR : (ν : ℝ) ≤ n := by dsimp [s] at hc; nlinarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n + 1 := by linarith
  have hd : 0 < d := by dsimp [d]; exact sub_pos.mpr ((div_lt_one hn1).mpr hsn)
  have hident : (n : ℝ) * d = n - s + s / (n + 1) := by
    dsimp [d]
    field_simp
    ring
  have hcn : (105 / 16 : ℝ) * ν * 2 ^ ν ≤ (n : ℝ) * d := by
    rw [hident]
    exact hc.trans (le_add_of_nonneg_right (div_nonneg hs0 hn1.le))
  have hbase : 0 < 2 * (n : ℝ) + 1 - ν := by linarith
  change 14 * V / (Real.pi * d * (n : ℝ) ^ (ν + 1)) ≤ _
  calc
    _ ≤ 32 * V / (15 * Real.pi * ν * (2 * (n : ℝ)) ^ ν) := by
      apply (div_le_div_iff₀ (by positivity : 0 < Real.pi * d * (n : ℝ) ^ (ν + 1))
        (by positivity : 0 < 15 * Real.pi * (ν : ℝ) * (2 * (n : ℝ)) ^ ν)).mpr
      have h := mul_le_mul_of_nonneg_right hcn
        (show (0 : ℝ) ≤ 32 * V * Real.pi * (n : ℝ) ^ ν by positivity)
      rw [mul_pow, pow_succ]
      convert h using 1 <;> ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (show 0 ≤ 32 * V by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 15 * Real.pi * (ν : ℝ))
      apply pow_le_pow_left₀ hbase.le
      linarith

end NLAlib
