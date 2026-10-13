import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-! # An explicit midpoint harmonic remainder

The finite odd-harmonic remainder retains the additive constant needed by
the sharp universal interpolation lower bound.
-/
noncomputable section
open Real Set Filter
open scoped Topology
namespace NLAlib

/-- A cubic rational lower bound for the symmetric logarithm.
Source: focused reroutes, the harmonic-remainder calculation; direct differentiation. -/
theorem two_mul_add_cubic_le_log_div {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    2 * t + 2 * t ^ 3 / 3 ≤ log ((1 + t) / (1 - t)) := by
  let f := fun x : ℝ => log (1 + x) - log (1 - x) - 2 * x - 2 * x ^ 3 / 3
  have hd (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
      HasDerivAt f (2 * x ^ 4 / (1 - x ^ 2)) x := by
    have hp : 1 + x ≠ 0 := by linarith [hx.1]
    have hm : 1 - x ≠ 0 := by linarith [hx.2]
    have h := ((((Real.hasDerivAt_log hp).comp x ((hasDerivAt_id x).const_add 1)).sub
      ((Real.hasDerivAt_log hm).comp x ((hasDerivAt_const x 1).sub (hasDerivAt_id x)))).sub
      ((hasDerivAt_id x).const_mul 2)).sub ((((hasDerivAt_id x).pow 3).const_mul 2).div_const 3)
    apply h.congr_deriv
    dsimp only [id_eq]
    have hden : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
    field_simp [hp, hm, hden]
    ring
  have hf : MonotoneOn f (Ico (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => by
        have hx' := interior_subset hx
        apply div_nonneg (by positivity)
        nlinarith [hx'.1, hx'.2])
  have h := hf (by norm_num) ⟨ht, ht1⟩ ht
  dsimp [f] at h
  simp only [add_zero, sub_zero, mul_zero, zero_pow (by decide : 3 ≠ 0), zero_div, log_one] at h
  have hp : 1 + t ≠ 0 := by linarith
  have hm : 1 - t ≠ 0 := by linarith
  rw [log_div hp hm]
  nlinarith

/-- The midpoint harmonic remainder used by the Chebyshev-root lower bound.
Source: focused reroutes, equation `polyretry:harmonic-remainder`. -/
def harmonicMidpointRemainder (m : ℕ) : ℝ :=
  2 * (harmonic (2 * m) : ℝ) - (harmonic m : ℝ) - log m - eulerMascheroniConstant - 2 * log 2

/-- Adjacent midpoint harmonic remainders have an exact logarithmic difference.
Source: focused reroutes, finite harmonic-remainder telescope. -/
theorem harmonicMidpointRemainder_sub_succ {k : ℕ} (hk : 0 < k) :
    harmonicMidpointRemainder k - harmonicMidpointRemainder (k + 1) =
      log (((k : ℝ) + 1) / k) - 2 / (2 * (k : ℝ) + 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkp : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2k : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  have h2kp : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
  unfold harmonicMidpointRemainder
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, harmonic_succ, harmonic_succ, harmonic_succ]
  push_cast
  rw [log_div hkp hkR.ne']
  field_simp [hkp, h2k, h2kp]
  ring

/-- The adjacent remainder difference dominates an explicit cubic reciprocal.
Source: focused reroutes, finite harmonic-remainder telescope. -/
theorem cubic_inv_le_harmonicMidpointRemainder_sub_succ {k : ℕ} (hk : 0 < k) :
    2 / (3 * (2 * (k : ℝ) + 1) ^ 3) ≤
      harmonicMidpointRemainder k - harmonicMidpointRemainder (k + 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : 0 < 2 * (k : ℝ) + 1 := by positivity
  have ht : (2 * (k : ℝ) + 1)⁻¹ < 1 := (inv_lt_one₀ hden).mpr (by linarith)
  have h := two_mul_add_cubic_le_log_div (inv_nonneg.mpr hden.le) ht
  have heq : (1 + (2 * (k : ℝ) + 1)⁻¹) / (1 - (2 * (k : ℝ) + 1)⁻¹) =
      ((k : ℝ) + 1) / k := by
    field_simp
    ring
  rw [heq] at h
  rw [harmonicMidpointRemainder_sub_succ hk]
  have hc : 2 * ((2 * (k : ℝ) + 1)⁻¹) ^ 3 / 3 =
      2 / (3 * (2 * (k : ℝ) + 1) ^ 3) := by simp only [inv_pow, div_eq_mul_inv, mul_inv_rev]; ring
  rw [hc] at h
  rw [show 2 * (2 * (k : ℝ) + 1)⁻¹ = 2 / (2 * (k : ℝ) + 1) by ring] at h
  linarith

/-- The midpoint harmonic remainder tends to zero.
Source: the defining harmonic-log limit of the Euler–Mascheroni constant. -/
theorem tendsto_harmonicMidpointRemainder :
    Tendsto harmonicMidpointRemainder atTop (𝓝 0) := by
  have h2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by dsimp only [id_eq]; omega) tendsto_id
  have h := (((tendsto_harmonic_sub_log.comp h2).const_mul 2).sub
    tendsto_harmonic_sub_log).sub (tendsto_const_nhds (x := eulerMascheroniConstant))
  have heq : (fun m : ℕ => 2 * ((harmonic (2 * m) : ℝ) - log (2 * m : ℕ)) -
      ((harmonic m : ℝ) - log m) - eulerMascheroniConstant) =ᶠ[atTop] harmonicMidpointRemainder := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    dsimp [harmonicMidpointRemainder]
    rw [Nat.cast_mul, Nat.cast_ofNat, log_mul (by norm_num) hmR.ne']
    ring
  convert h.congr' heq using 1
  ring_nf

/-- The explicit midpoint harmonic remainder is at least `1/[6(2m+1)^2]`.
Source: focused reroutes, equation `polyretry:harmonic-remainder`. A rational
finite telescope replaces the improper integral in the printed proof. -/
theorem inv_sq_le_harmonicMidpointRemainder {m : ℕ} (hm : 1 ≤ m) :
    1 / (6 * (2 * (m : ℝ) + 1) ^ 2) ≤ harmonicMidpointRemainder m := by
  let R := fun k : ℕ => 1 / (6 * (2 * (k : ℝ) + 1) ^ 2)
  have hR (k : ℕ) : R k - R (k + 1) ≤ 2 / (3 * (2 * (k : ℝ) + 1) ^ 3) := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hA : 0 < 2 * (k : ℝ) + 1 := by positivity
    have hB : 0 < 2 * (k : ℝ) + 3 := by positivity
    dsimp [R]
    push_cast
    rw [show 2 * ((k : ℝ) + 1) + 1 = 2 * k + 3 by ring]
    have heq : 1 / (6 * (2 * (k : ℝ) + 1) ^ 2) - 1 / (6 * (2 * k + 3) ^ 2) =
        2 * (2 * k + 2) / (3 * (2 * k + 1) ^ 2 * (2 * k + 3) ^ 2) := by
      field_simp
      ring
    rw [heq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hbase : (2 * (k : ℝ) + 1) * (2 * k + 2) ≤ (2 * k + 3) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 6 * (2 * (k : ℝ) + 1) ^ 2 by positivity)
    convert hmul using 1 <;> ring
  let E := fun j : ℕ => harmonicMidpointRemainder (j + 1) - R (j + 1)
  have hE : Antitone E := by
    apply antitone_nat_of_succ_le
    intro j
    have h := cubic_inv_le_harmonicMidpointRemainder_sub_succ (show 0 < j + 1 by omega)
    have hRj := hR (j + 1)
    dsimp [E]
    linarith
  have hden : Tendsto (fun k : ℕ => 6 * (2 * (k : ℝ) + 1) ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun k => by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) tendsto_natCast_atTop_atTop
  have hRt : Tendsto R atTop (𝓝 0) := by
    simpa only [Function.comp_def, R, one_div] using tendsto_inv_atTop_zero.comp hden
  have hEt : Tendsto E atTop (𝓝 0) := by
    have h := (tendsto_harmonicMidpointRemainder.sub hRt).comp (tendsto_add_atTop_nat 1)
    simpa only [E, Function.comp_def, sub_zero] using h
  have h := hE.le_of_tendsto hEt (m - 1)
  dsimp [E] at h
  rw [show m - 1 + 1 = m by omega] at h
  exact sub_nonneg.mp h

end NLAlib
