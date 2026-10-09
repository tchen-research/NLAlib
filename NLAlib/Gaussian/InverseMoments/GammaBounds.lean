import NLAlib.Gaussian.InverseMoments.LambdaMinTail

/-!
# Gamma estimates for operator inverse moments

Half-step log-convexity and the factorial Stirling lower bound yield the
sharp arithmetic-progression base `(k+r-1)/4` in the direct quadratic-probe
proof of inverse Gaussian spectral moments.

Sources: `Re-derivations/operator_rederivations.tex`, Gamma estimates and
the master inverse spectral moment. Atlas: `inverse-wishart-spectral-moment`,
`pinv-spectral-expectation`.
-/

noncomputable section

open Real

namespace NLAlib

/-- Iterating Gamma log-convexity over half steps bounds its square by an
arithmetic-progression product. Source: direct quadratic-probe proof,
Gamma estimates. Atlas: `inverse-wishart-spectral-moment` (helper). -/
theorem Gamma_add_nat_div_two_sq_le_mul_prod {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n / 2) ^ 2 ≤ Real.Gamma x ^ 2 *
      ∏ i ∈ Finset.range n, (x + i / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : 0 < x + (n : ℝ) / 2 := by positivity
    have hg : Real.Gamma (x + n / 2 + 1 / 2) ^ 2
        ≤ (x + n / 2) * Real.Gamma (x + n / 2) ^ 2 := by
      have h0 : 0 ≤ Real.Gamma (x + n / 2 + 1 / 2) :=
        (Real.Gamma_pos_of_pos (by linarith)).le
      calc Real.Gamma (x + n / 2 + 1 / 2) ^ 2
          ≤ (Real.Gamma (x + n / 2) * √(x + n / 2)) ^ 2 :=
            pow_le_pow_left₀ h0 (Gamma_add_half_le_mul_sqrt hz) 2
        _ = _ := by rw [mul_pow, Real.sq_sqrt hz.le]; ring
    have he : x + n / 2 + 1 / 2 = x + ((n + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
    rw [he] at hg
    rw [Finset.prod_range_succ]
    calc Real.Gamma (x + ((n + 1 : ℕ) : ℝ) / 2) ^ 2
        ≤ (x + n / 2) * Real.Gamma (x + n / 2) ^ 2 := hg
      _ ≤ (x + n / 2) * (Real.Gamma x ^ 2 * ∏ i ∈ Finset.range n, (x + i / 2)) :=
          mul_le_mul_of_nonneg_left ih hz.le
      _ = _ := by ring

/-- The Gamma half-step ratio is bounded by the arithmetic mean of all
its half-step factors, retaining the final `-1`. Source: direct quadratic-probe
proof, Gamma estimates. Atlas: `inverse-wishart-spectral-moment` (helper). -/
theorem Gamma_add_nat_div_two_le {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    Real.Gamma (x + n / 2) ≤ Real.Gamma x *
      (x + ((n : ℝ) - 1) / 4) ^ ((n : ℝ) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := Gamma_add_nat_div_two_sq_le_mul_prod hx (m + 1)
  have h2 := prod_range_add_le_pow (2 * x) (by positivity) m
  have hprod : ∏ i ∈ Finset.range (m + 1), (x + i / 2)
      = (∏ i ∈ Finset.range (m + 1), (2 * x + i)) / 2 ^ (m + 1) := by
    calc _ = ∏ i ∈ Finset.range (m + 1), ((2 * x + i) / 2) := by
          apply Finset.prod_congr rfl
          intro i _; ring
      _ = _ := by rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  rw [hprod] at h1
  have h3 : (∏ i ∈ Finset.range (m + 1), (2 * x + i)) / 2 ^ (m + 1)
      ≤ (x + m / 4) ^ (m + 1) := by
    calc _ ≤ ((2 * (2 * x) + m) / 2) ^ (m + 1) / 2 ^ (m + 1) := by gcongr
      _ = (x + m / 4) ^ (m + 1) := by rw [← div_pow]; congr 1; ring
  have h4 := h1.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
  have hxmean : 0 ≤ x + (m : ℝ) / 4 := by positivity
  have hrpow : (x + (m : ℝ) / 4) ^ (((m + 1 : ℕ) : ℝ) / 2)
      = Real.sqrt ((x + (m : ℝ) / 4) ^ (m + 1)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hxmean]
    congr 1; push_cast; ring
  have hs := Real.sqrt_le_sqrt h4
  rw [Real.sqrt_sq (Real.Gamma_pos_of_pos (by positivity)).le,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.Gamma_pos_of_pos hx).le] at hs
  convert hs using 1
  rw [show ((m + 1 : ℕ) : ℝ) - 1 = m by push_cast; ring, hrpow]

/-- A squared Gamma value at an integer half-step dominates the explicit
Stirling expression needed for inverse moments. Source: direct quadratic-probe
proof, Gamma estimates. Atlas: `inverse-wishart-spectral-moment` (helper). -/
theorem Gamma_nat_add_one_div_two_sq_ge {d : ℕ} (hd : 1 ≤ d) :
    Real.pi * ((d : ℝ) / (2 * Real.exp 1)) ^ d ≤
      Real.Gamma (((d : ℝ) + 1) / 2) ^ 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set z : ℝ := ((d : ℝ) + 1) / 2 with hz
  have hz0 : 0 < z := by positivity
  have hg0 := Real.Gamma_pos_of_pos hz0
  have hdup := Real.Gamma_mul_Gamma_add_half z
  have hdup' : Real.Gamma z * Real.Gamma (z + 1 / 2)
      = (d.factorial : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) * Real.sqrt Real.pi := by
    rw [show 1 - 2 * z = -(d : ℝ) by rw [hz]; ring,
      show 2 * z = (d : ℝ) + 1 by rw [hz]; ring,
      Real.Gamma_nat_eq_factorial] at hdup
    exact hdup
  have hupper : (d.factorial : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) * Real.sqrt Real.pi
      ≤ Real.Gamma z ^ 2 * Real.sqrt z := by
    rw [← hdup']
    have := mul_le_mul_of_nonneg_left (Gamma_add_half_le_mul_sqrt hz0) hg0.le
    nlinarith
  have htwo : (2 : ℝ) ^ (-(d : ℝ)) * 2 ^ d = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    simp
  have hfac : (d.factorial : ℝ) * Real.sqrt Real.pi
      ≤ 2 ^ d * Real.Gamma z ^ 2 * Real.sqrt z := by
    calc _ = 2 ^ d * ((d.factorial : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) * Real.sqrt Real.pi) := by
          rw [show 2 ^ d * ((d.factorial : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) * Real.sqrt Real.pi)
            = (d.factorial : ℝ) * ((2 : ℝ) ^ (-(d : ℝ)) * 2 ^ d) * Real.sqrt Real.pi by ring,
            htwo, mul_one]
      _ ≤ 2 ^ d * (Real.Gamma z ^ 2 * Real.sqrt z) := by gcongr
      _ = _ := by ring
  have hsqrt : Real.pi * Real.sqrt z ≤ Real.sqrt (2 * Real.pi * d) * Real.sqrt Real.pi := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1
    rw [mul_pow, Real.sq_sqrt hz0.le, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt Real.pi_pos.le, hz]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [sq_nonneg Real.pi]
  have hst := Stirling.le_factorial_stirling d
  have hpower : (2 : ℝ) ^ d * ((d : ℝ) / (2 * Real.exp 1)) ^ d
      = ((d : ℝ) / Real.exp 1) ^ d := by rw [← mul_pow]; congr 1; field_simp
  have hfinal : 2 ^ d * (Real.pi * ((d : ℝ) / (2 * Real.exp 1)) ^ d) * Real.sqrt z
      ≤ 2 ^ d * Real.Gamma z ^ 2 * Real.sqrt z := by
    calc _ = (Real.pi * Real.sqrt z) * ((d : ℝ) / Real.exp 1) ^ d := by rw [← hpower]; ring
      _ ≤ (Real.sqrt (2 * Real.pi * d) * Real.sqrt Real.pi) * ((d : ℝ) / Real.exp 1) ^ d := by gcongr
      _ = (Real.sqrt (2 * Real.pi * d) * ((d : ℝ) / Real.exp 1) ^ d) * Real.sqrt Real.pi := by ring
      _ ≤ (d.factorial : ℝ) * Real.sqrt Real.pi := by gcongr
      _ ≤ _ := hfac
  exact le_of_mul_le_mul_left (le_of_mul_le_mul_right hfinal (Real.sqrt_pos.mpr hz0))
    (by positivity)

/-- The scalar constant in the master quadratic-probe moment bound has
the sharper base retaining `-1`. Source: direct quadratic-probe proof,
endpoint moment calculation. Atlas: `inverse-wishart-spectral-moment` (helper). -/
theorem Gamma_endpoint_moment_le {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 1 ≤ d) :
    2 ^ (-(d : ℝ) / 2) * Real.pi * Real.Gamma (x + d / 2) /
        (Real.Gamma x * Real.Gamma (((d : ℝ) + 1) / 2) ^ 2)
      ≤ (2 * Real.exp 1 ^ 2 * (x + ((d : ℝ) - 1) / 4) / (d : ℝ) ^ 2) ^
        ((d : ℝ) / 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set q : ℝ := (d : ℝ) / 2 with hq
  set M : ℝ := x + ((d : ℝ) - 1) / 4 with hM
  set T : ℝ := (d : ℝ) / (2 * Real.exp 1) with hT
  have hq0 : 0 < q := by positivity
  have hM0 : 0 < M := by rw [hM]; linarith
  have hT0 : 0 < T := by rw [hT]; positivity
  have hg0 := Real.Gamma_pos_of_pos hx
  have hz0 := Real.Gamma_pos_of_pos (show 0 < ((d : ℝ) + 1) / 2 by positivity)
  have hratio : Real.Gamma (x + d / 2) / Real.Gamma x ≤ M ^ q := by
    apply (div_le_iff₀ hg0).2
    simpa [hM, hq, mul_comm] using Gamma_add_nat_div_two_le hx hd
  have hinv : Real.pi / Real.Gamma (((d : ℝ) + 1) / 2) ^ 2 ≤ 1 / T ^ d := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simpa [hT] using Gamma_nat_add_one_div_two_sq_ge hd
  have hfactor : 2 ^ (-q) * Real.pi * Real.Gamma (x + d / 2) /
        (Real.Gamma x * Real.Gamma (((d : ℝ) + 1) / 2) ^ 2)
      ≤ 2 ^ (-q) * M ^ q / T ^ d := by
    calc _ = 2 ^ (-q) * (Real.Gamma (x + d / 2) / Real.Gamma x) *
          (Real.pi / Real.Gamma (((d : ℝ) + 1) / 2) ^ 2) := by ring
      _ ≤ 2 ^ (-q) * M ^ q * (1 / T ^ d) := by gcongr
      _ = _ := by ring
  have hTpow : T ^ d = (T ^ 2) ^ q := by
    rw [← Real.rpow_natCast T d, ← Real.rpow_natCast T 2, ← Real.rpow_mul hT0.le]
    congr 1; rw [hq]; push_cast; ring
  have htwo : (2 : ℝ) ^ (-q) = (1 / 2 : ℝ) ^ q := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  have heq : 2 ^ (-q) * M ^ q / T ^ d =
      (2 * Real.exp 1 ^ 2 * M / (d : ℝ) ^ 2) ^ q := by
    rw [hTpow, htwo, ← Real.mul_rpow (by norm_num) hM0.le,
      ← Real.div_rpow (by positivity) (by positivity)]
    congr 1
    rw [hT]
    field_simp
  simpa [hq, hM, neg_div] using hfactor.trans heq.le

/-- The endpoint quadratic-probe constant for an `r × k` Gaussian matrix
is bounded by the strengthened inverse spectral moment constant.
Source: direct quadratic-probe proof, endpoint moment calculation; the
arithmetic-progression mean retains `k+r-1`. Atlas:
`inverse-wishart-spectral-moment` (helper). -/
theorem gamma_inverse_spectral_endpoint_le {r k : ℕ} (hr : 1 ≤ r) (hrk : r < k) :
    2 ^ (-((k : ℝ) - r) / 2) * Real.pi * Real.Gamma ((k : ℝ) / 2) /
        (Real.Gamma ((r : ℝ) / 2) * Real.Gamma (((k : ℝ) - r + 1) / 2) ^ 2)
      ≤ (Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) / (2 * ((k : ℝ) - r) ^ 2)) ^
        (((k : ℝ) - r) / 2) := by
  obtain ⟨d, hk⟩ := Nat.exists_eq_add_of_le hrk.le
  have hd : 1 ≤ d := by omega
  subst k
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h := Gamma_endpoint_moment_le (show 0 < (r : ℝ) / 2 by positivity) hd
  have he1 : (r : ℝ) / 2 + d / 2 = ((r : ℝ) + d) / 2 := by ring
  have he2 : 2 * Real.exp 1 ^ 2 * ((r : ℝ) / 2 + ((d : ℝ) - 1) / 4) / (d : ℝ) ^ 2
      = Real.exp 1 ^ 2 * (((r : ℝ) + d) + r - 1) / (2 * (d : ℝ) ^ 2) := by ring
  rw [he1, he2] at h
  simpa only [Nat.cast_add, add_sub_cancel_left] using h

end NLAlib
