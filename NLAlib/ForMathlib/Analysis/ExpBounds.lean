import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Elementary exponential bounds and series

Real-variable facts about `exp` and `cosh` used by the sub-Gaussian moment theory and the
Hanson–Wright proof: the power series of `exp (θ x²)`, a factorial ratio estimate, the bound of a
`cosh` Taylor term by `cosh`, two quadratic bounds for `exp (-u)`, the midpoint convexity bound
`exp (a + b) ≤ (exp (2a) + exp (2b)) / 2`, the global remainder bound
`exp x ≤ 1 + x + x² exp |x|`, and the two logarithmic Chernoff-exponent bounds
`-ε - (1 - ε) log (1 - ε) ≤ -ε²/2`, `ε - (1 + ε) log (1 + ε) ≤ -ε²/3`, and the one-sided
Bernstein bound `exp (θx) ≤ 1 + θx + ((θ²/2)/(1 - θL/3)) x²` for `x ≤ L`
(`exp_mul_le_one_add_mul_add_sq_mul_of_le`, moved from
`NLAlib.Probability.Concentration.Matrix.BernsteinMgfCgf`). Candidates for `Mathlib/Analysis/SpecialFunctions/Exp.lean`.

Moved here from `NLAlib.Probability.Concentration.QuadraticForms.*` (ported from HighDimProb commit
c0cb8d9) and `NLAlib.Probability.SubGaussian.OrliczMGF`, `NLAlib.Probability.Concentration.Matrix.Sampling`
(dedup round, 2026-10-12).
-/

open Real

namespace NLAlib

/-- Pointwise power-series expansion `exp (θ x²) = ∑ₘ θᵐ x^{2m} / m!`.
Atlas `hanson-wright` (helper). -/
theorem exp_mul_sq_eq_tsum (θ x : ℝ) :
    exp (θ * x ^ 2) =
      ∑' m : ℕ, θ ^ m * x ^ (2 * m) / (Nat.factorial m : ℝ) := by
  rw [show exp (θ * x ^ 2) = ∑' m : ℕ, (θ * x ^ 2) ^ m / (Nat.factorial m : ℝ) by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]]
  congr with m
  rw [mul_pow, ← pow_mul]

/-- The factorial estimate `(2m)! / m! ≤ (2m + 1)ᵐ`, used to sum the square-exponential moment
series. Atlas `hanson-wright` (helper). -/
theorem factorial_two_mul_div_factorial_le_succ_pow (m : ℕ) :
    (Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ) ≤
      ((2 * m + 1 : ℕ) : ℝ) ^ m := by
  have hnat : Nat.factorial (2 * m) ≤ (2 * m + 1) ^ m * Nat.factorial m := by
    calc Nat.factorial (2 * m)
        ≤ (2 * m) ^ m * Nat.factorial m := Nat.factorial_two_mul_le m
      _ ≤ (2 * m + 1) ^ m * Nat.factorial m := by
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ _) m)
  have hfac_pos : 0 < (Nat.factorial m : ℝ) := by positivity
  rw [div_le_iff₀ hfac_pos]
  exact_mod_cast hnat

/-- Each (nonnegative) Taylor term of `cosh` is bounded by `cosh` itself:
`y^{2m} / (2m)! ≤ cosh y`. Atlas `hanson-wright` (helper). -/
theorem cosh_taylor_term_le (y : ℝ) (m : ℕ) :
    y ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ≤ cosh y := by
  rw [Real.cosh_eq_tsum]
  have hs := (Real.hasSum_cosh y).summable
  have hnonneg : ∀ n : ℕ, 0 ≤ y ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
    intro n
    exact div_nonneg (Even.pow_nonneg (even_two.mul_right n) y)
      (Nat.cast_nonneg (Nat.factorial (2 * n)))
  have hsingle :=
    hs.sum_le_tsum ({m} : Finset ℕ) (fun n _ => hnonneg n)
  simpa using hsingle

/-- A global quadratic upper bound for the negative exponential on the nonnegative half-line:
`exp (-u) ≤ 1 - u + u²` for `u ≥ 0`. Atlas `hanson-wright` (helper). -/
theorem exp_neg_le_one_sub_add_sq {u : ℝ} (hu : 0 ≤ u) :
    exp (-u) ≤ 1 - u + u ^ 2 := by
  have hden_pos : 0 < 1 + u := by linarith
  have h_exp_ge : 1 + u ≤ exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  have hinv : (exp u)⁻¹ ≤ (1 + u)⁻¹ :=
    (inv_le_inv₀ (exp_pos u) hden_pos).2 h_exp_ge
  have hrat : (1 + u)⁻¹ ≤ 1 - u + u ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hden_pos]
    ring_nf
    nlinarith [pow_nonneg hu 3]
  calc
    exp (-u) = (exp u)⁻¹ := by rw [exp_neg]
    _ ≤ (1 + u)⁻¹ := hinv
    _ ≤ 1 - u + u ^ 2 := hrat

/-- The linear Taylor term cancels after multiplying by `exp (-u)`: `exp (-u) (1 + u) ≤ 1`.
Atlas `hanson-wright` (helper). -/
theorem exp_neg_mul_one_add_le_one (u : ℝ) :
    exp (-u) * (1 + u) ≤ 1 := by
  have h_exp_ge : 1 + u ≤ exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  calc
    exp (-u) * (1 + u) ≤ exp (-u) * exp u := by
      exact mul_le_mul_of_nonneg_left h_exp_ge (exp_nonneg _)
    _ = 1 := by
      rw [← exp_add]
      ring_nf
      simp

/-- Midpoint convexity of `exp`: `exp (a + b) ≤ (exp (2a) + exp (2b)) / 2`.
Atlas `hanson-wright` (helper). -/
theorem exp_add_le_average_exp_two (a b : ℝ) :
    exp (a + b) ≤ (exp (2 * a) + exp (2 * b)) / 2 := by
  have hconv := convexOn_exp.2 (Set.mem_univ (2 * a)) (Set.mem_univ (2 * b))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  calc
    exp (a + b) = exp ((1 / 2 : ℝ) • (2 * a) + (1 / 2 : ℝ) • (2 * b)) := by
      congr 1
      norm_num
      ring
    _ ≤ (1 / 2 : ℝ) * exp (2 * a) + (1 / 2 : ℝ) * exp (2 * b) := hconv
    _ = (exp (2 * a) + exp (2 * b)) / 2 := by ring

/-- A global first-order exponential remainder bound: `exp x ≤ 1 + x + x² exp |x|`. Used to
recover the quadratic MGF behavior of a centered variable from an Orlicz exponential moment.
Atlas `subgaussian-def`, `bernstein-scalar` (analytic helper). -/
theorem exp_le_one_add_add_sq_mul_exp_abs (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have he : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  by_cases hsmall : |x| ≤ 1
  · have hrem := Real.abs_exp_sub_one_sub_id_le hsmall
    have hupper : Real.exp x ≤ 1 + x + x ^ 2 := by
      linarith [(le_abs_self (Real.exp x - 1 - x)).trans hrem]
    have hmul : x ^ 2 ≤ x ^ 2 * Real.exp |x| := by
      simpa using mul_le_mul_of_nonneg_left he (sq_nonneg x)
    linarith
  · by_cases hx : 0 ≤ x
    · have hx1 : 1 ≤ x := by simpa [abs_of_nonneg hx] using (not_le.mp hsmall).le
      rw [abs_of_nonneg hx]
      have hsq : 1 ≤ x ^ 2 := by nlinarith
      have hmul : Real.exp x ≤ x ^ 2 * Real.exp x := by
        simpa using mul_le_mul_of_nonneg_right hsq (Real.exp_pos x).le
      linarith
    · have hx0 : x ≤ 0 := (not_le.mp hx).le
      have hx1 : x ≤ -1 := by
        have h := (not_le.mp hsmall).le
        rw [abs_of_nonpos hx0] at h
        linarith
      have hex : Real.exp x ≤ 1 := by simpa using Real.exp_le_exp.mpr hx0
      have hsq : -x ≤ x ^ 2 := by nlinarith
      have hmul : x ^ 2 ≤ x ^ 2 * Real.exp |x| := by
        simpa using mul_le_mul_of_nonneg_left he (sq_nonneg x)
      linarith

/-- `-ε - (1 - ε) log(1 - ε) ≤ -ε²/2` for `0 ≤ ε < 1`. Proof: `g(ε) = (1-ε)log(1-ε) + ε - ε²/2`
vanishes at `0` and has derivative `-log(1-ε) - ε ≥ 0`. Tropp 2012, Rem 5.3 (lower tail);
atlas `matrix-chernoff-sampling` (helper). -/
theorem neg_sub_mul_log_one_sub_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    -ε - (1 - ε) * log (1 - ε) ≤ -(ε ^ 2 / 2) := by
  let g : ℝ → ℝ := fun t => (1 - t) * log (1 - t) + t - t ^ 2 / 2
  have hderiv : ∀ t, t < 1 → HasDerivAt g (-log (1 - t) - t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have hlog := h1.log (by linarith)
    have hprod := h1.mul hlog
    have hp : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - t) t := by
      have := (hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)
      exact this.congr_deriv (by norm_num)
    have := hprod.add hp
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    · field_simp [show (1 - t) ≠ 0 by linarith]
      ring
    · simp only [g, Pi.add_apply, Pi.mul_apply]; ring
  have hmono : MonotoneOn g (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1) ?_ ?_ ?_
    · exact fun t ht => (hderiv t ht.2).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      exact (hderiv t ht.2).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      rw [(hderiv t ht.2).deriv]
      have := log_le_sub_one_of_pos (show 0 < 1 - t by linarith [ht.2])
      linarith
  have := hmono (Set.mem_Ico.2 ⟨le_rfl, by norm_num⟩) (Set.mem_Ico.2 ⟨hε0, hε1⟩) hε0
  simp only [g, sub_zero, log_one, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at this
  linarith

/-- `ε - (1 + ε) log(1 + ε) ≤ -ε²/3` for `0 ≤ ε ≤ 1`. Proof: `log(1+ε) ≥ 2ε/(ε+2)` (first
term of Mathlib's `hasSum_log_one_add`), and `(1+ε)·2ε/(ε+2) ≥ ε + ε²/3` iff `ε ≤ 1`.
Tropp 2012, Rem 5.3 (upper tail); atlas `matrix-chernoff-sampling` (helper). -/
theorem sub_mul_log_one_add_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε - (1 + ε) * log (1 + ε) ≤ -(ε ^ 2 / 3) := by
  have h := hasSum_log_one_add hε0
  have hlow := le_hasSum h 0 (fun n _ => by positivity)
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, mul_one, pow_one] at hlow
  have hpos : 0 < ε + 2 := by linarith
  have key : ε + ε ^ 2 / 3 ≤ (1 + ε) * (2 * (ε / (ε + 2))) := by
    rw [← sub_nonneg]
    have : (1 + ε) * (2 * (ε / (ε + 2))) - (ε + ε ^ 2 / 3) = ε ^ 2 * (1 - ε) / (3 * (ε + 2)) := by
      field_simp
      ring
    rw [this]
    have : 0 ≤ 1 - ε := by linarith
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hlow (show 0 ≤ 1 + ε by linarith)]

/-! ### The one-sided Bernstein exponential bound -/

/-- Auxiliary function `g(u) = u²/2 - (1 - u/3)(eᵘ - 1 - u)`. -/
private noncomputable def gFun (u : ℝ) : ℝ := u ^ 2 / 2 - (1 - u / 3) * (Real.exp u - 1 - u)

/-- Its derivative `h = g'`. -/
private noncomputable def hFun (u : ℝ) : ℝ := u + (Real.exp u - 1 - u) / 3 - (1 - u / 3) * (Real.exp u - 1)

private lemma hasDerivAt_hFun (u : ℝ) : HasDerivAt hFun ((1 - Real.exp u * (1 - u)) / 3) u := by
  have h1 := (((Real.hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id u)).div_const 3
  have h2 := ((hasDerivAt_id u).div_const 3).const_sub 1
  have h3 := h2.mul ((Real.hasDerivAt_exp u).sub_const 1)
  have h4 := ((hasDerivAt_id u).add h1).sub h3
  refine (h4.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp; ring
  · simp [hFun]

private lemma hasDerivAt_gFun (u : ℝ) : HasDerivAt gFun (hFun u) u := by
  have h1 := ((Real.hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id u)
  have h2 := ((hasDerivAt_id u).div_const 3).const_sub 1
  have h4 := ((hasDerivAt_pow 2 u).div_const 2).sub (h2.mul h1)
  refine (h4.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · simp [hFun]; ring
  · simp [gFun]

private lemma hFun_mono : Monotone hFun := by
  apply monotone_of_deriv_nonneg (fun u => (hasDerivAt_hFun u).differentiableAt)
  intro u
  rw [(hasDerivAt_hFun u).deriv]
  have h1 := Real.add_one_le_exp (-u)
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos u
  apply div_nonneg _ (by norm_num)
  nlinarith

private lemma gFun_nonneg (u : ℝ) : 0 ≤ gFun u := by
  have hdiff : Differentiable ℝ gFun := fun u => (hasDerivAt_gFun u).differentiableAt
  have g0 : gFun 0 = 0 := by simp [gFun]
  have h0 : hFun 0 = 0 := by simp [hFun]
  rcases le_total u 0 with hu | hu
  · have hanti : AntitoneOn gFun (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Iic] at hx
      rw [(hasDerivAt_gFun x).deriv]
      have := hFun_mono (le_of_lt (Set.mem_Iio.mp hx))
      linarith
    have := hanti (Set.mem_Iic.mpr hu) (Set.mem_Iic.mpr le_rfl) hu
    linarith
  · have hmono : MonotoneOn gFun (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_gFun x).deriv]
      have := hFun_mono (le_of_lt (Set.mem_Ioi.mp hx))
      linarith
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
    linarith

/-- The scalar one-sided Bernstein exponential bound, permitting arbitrarily negative
`x ≤ L`: `exp(θx) ≤ 1+θx+((θ²/2)/(1-θL/3))x²`.
Source: Tropp 2015, Lemma 6.6.2; scalar Taylor comparison in operator rederivations
`eq:scalarbernstein`. Reused by `matrix-bernstein` and `matrix-freedman` (partial). -/
theorem exp_mul_le_one_add_mul_add_sq_mul_of_le {L θ x : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3) (hx : x ≤ L) :
    Real.exp (θ * x) ≤ 1 + θ * x + (θ ^ 2 / 2) / (1 - θ * L / 3) * x ^ 2 := by
  have hux : θ * x ≤ θ * L := mul_le_mul_of_nonneg_left hx hθ.le
  have hpos : 0 < 1 - θ * L / 3 := by linarith
  have hpos' : 0 < 1 - θ * x / 3 := by linarith
  have hg := gFun_nonneg (θ * x)
  unfold gFun at hg
  have h1 : Real.exp (θ * x) - 1 - θ * x ≤ ((θ * x) ^ 2 / 2) / (1 - θ * x / 3) := by
    rw [le_div_iff₀ hpos']; nlinarith
  have h2 : ((θ * x) ^ 2 / 2) / (1 - θ * x / 3) ≤ ((θ * x) ^ 2 / 2) / (1 - θ * L / 3) :=
    div_le_div_of_nonneg_left (by positivity) hpos (by linarith)
  have h3 : (θ ^ 2 / 2) / (1 - θ * L / 3) * x ^ 2 = ((θ * x) ^ 2 / 2) / (1 - θ * L / 3) := by
    ring
  linarith

end NLAlib
