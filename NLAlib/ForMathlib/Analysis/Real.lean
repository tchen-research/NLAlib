import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Elementary real inequalities

General inequalities about `Real.sqrt`, `Real.log` and `Real.exp` that are not about NLAlib's
objects; candidates for upstreaming to `Mathlib/Analysis/SpecialFunctions/`.

* `sqrt_sum_sq_le_sum_abs`: `√(∑ xᵢ²) ≤ ∑ |xᵢ|`;
* `abs_mul_log_le_sq_add_one`: `|s log s| ≤ s² + 1` for `s ≥ 0`;
* `abs_add_mul_log_add_le`: `|(a + δ) log (a + δ)| ≤ |a log a| + a + 2` for `a ≥ 0`, `0 < δ ≤ 1`;
* `abs_mul_exp_le_exp_two_mul_add_one`: `|u eᵘ| ≤ e^{2u} + 1`;
* `log_one_add_le_sub_sq_div_two_add_pow_three_div_three`: `log(1 + ε) ≤ ε − ε²/2 + ε³/3` for
  `ε ≥ 0`;
* `log_one_sub_le_neg_sub_sq_div_two`: `log(1 − ε) ≤ −ε − ε²/2` for `0 ≤ ε < 1`.

Used by the Gaussian concentration files (atlas `gaussian-log-sobolev`,
`gaussian-concentration`) and by the Johnson–Lindenstrauss tail (atlas `jl-distributional`,
`chi-square-lower-tail`).
-/

namespace NLAlib

/-- `√(∑ xᵢ²) ≤ ∑ |xᵢ|`. Atlas: `gaussian-concentration` (helper). Ported from Prove2me solution
`GaussianMatrix.gaussian_lipschitz_entropy_bound`. -/
theorem sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (∑ i, x i ^ 2) ≤ ∑ i, |x i| := by
  have h0 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [Real.sqrt_le_left h0]
  have : ∑ i, x i ^ 2 = ∑ i, |x i| ^ 2 := by simp [sq_abs]
  rw [this]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

/-- `|s log s| ≤ s² + 1` for `s ≥ 0`. Atlas: `gaussian-log-sobolev` (helper). Ported from
Prove2me solution `GaussianMatrix.gaussian_logsobolev_bounded_below`. -/
theorem abs_mul_log_le_sq_add_one (s : ℝ) (hs : 0 ≤ s) : |s * Real.log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with h | hs'
  · subst h; simp
  rcases le_or_gt s 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt s hs' h1
    rw [mul_comm]; nlinarith [sq_nonneg s]
  · have hl : 0 ≤ Real.log s := Real.log_nonneg h1.le
    have hl2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs'
    rw [abs_of_nonneg (mul_nonneg hs hl)]
    nlinarith

/-- `|(a + δ) log (a + δ)| ≤ |a log a| + a + 2` for `a ≥ 0` and `0 < δ ≤ 1`. Atlas:
`gaussian-log-sobolev` (helper). Ported from Prove2me solution
`GaussianMatrix.gaussian_logsobolev`. -/
theorem abs_add_mul_log_add_le (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    |(a + δ) * Real.log (a + δ)| ≤ |a * Real.log a| + a + 2 := by
  set b := a + δ with hb
  have hbpos : 0 < b := by positivity
  -- convexity: a log a ≥ a log b + a - b
  have hconv : a * Real.log b + a - b ≤ a * Real.log a := by
    rcases ha.eq_or_lt with h0 | hpos
    · subst h0; simp; linarith
    · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hpos hbpos)
      rw [Real.log_div hpos.ne' hbpos.ne', inv_div] at h1
      have h2 : a * (1 - b / a) ≤ a * (Real.log a - Real.log b) :=
        mul_le_mul_of_nonneg_left h1 ha
      rw [mul_sub, mul_div_cancel₀ _ hpos.ne'] at h2
      linarith
  rcases le_or_gt 1 b with hb1 | hb1
  · have hlog0 : 0 ≤ Real.log b := Real.log_nonneg hb1
    have hlogb : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hbpos
    rw [abs_of_nonneg (mul_nonneg hbpos.le hlog0)]
    have : b * Real.log b ≤ a * Real.log a + δ * (Real.log b + 1) := by
      have : b * Real.log b = a * Real.log b + δ * Real.log b := by rw [hb]; ring
      linarith
    have h3 : δ * (Real.log b + 1) ≤ Real.log b + 1 := by nlinarith
    have h4 := le_abs_self (a * Real.log a)
    linarith
  · have hlog0 : Real.log b ≤ 0 := Real.log_nonpos hbpos.le hb1.le
    have hl := Real.one_sub_inv_le_log_of_pos hbpos
    have : b * (1 - b⁻¹) ≤ b * Real.log b := mul_le_mul_of_nonneg_left hl hbpos.le
    rw [mul_sub, mul_inv_cancel₀ hbpos.ne', mul_one] at this
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hbpos.le hlog0)]
    have := abs_nonneg (a * Real.log a)
    linarith

/-- `|u e^u| ≤ e^{2u} + 1`. Atlas: `gaussian-concentration` (helper). Ported from Prove2me
solution `GaussianMatrix.gaussian_lipschitz_entropy_bound`. -/
theorem abs_mul_exp_le_exp_two_mul_add_one (u : ℝ) :
    |u * Real.exp u| ≤ Real.exp (2 * u) + 1 := by
  have e2 : Real.exp (2 * u) = Real.exp u * Real.exp u := by rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos u
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg (mul_nonneg h hpos.le), e2]
    have := Real.add_one_le_exp u
    nlinarith
  · rw [abs_of_nonpos (by nlinarith)]
    have := Real.add_one_le_exp (-u)
    have e : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_right this hpos.le
    nlinarith [Real.exp_pos (2 * u)]

/-- `log(1 + ε) ≤ ε − ε²/2 + ε³/3` for `ε ≥ 0` (the third Taylor polynomial of `log(1 + ·)` is
an upper bound on `[0, ∞)`). Proof: the difference has derivative `ε³/(1 + ε) ≥ 0` and vanishes
at `0`. Used in Dasgupta–Gupta 2003, proof of Lem 2.2. Atlas: `jl-distributional` (helper). -/
theorem log_one_add_le_sub_sq_div_two_add_pow_three_div_three {ε : ℝ} (hε : 0 ≤ ε) :
    Real.log (1 + ε) ≤ ε - ε ^ 2 / 2 + ε ^ 3 / 3 := by
  let f : ℝ → ℝ := fun t => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt f (1 - t + t ^ 2 - 1 / (1 + t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
    have hlog := h1.log (by linarith)
    have hp : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2 + t ^ 3 / 3) (1 - t + t ^ 2) t := by
      have := (((hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 3 t).div_const 3))
      exact this.congr_deriv (by norm_num)
    exact hp.sub hlog
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hderiv t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := ht
      rw [(hderiv t ht0.le).deriv]
      have : 1 - t + t ^ 2 - 1 / (1 + t) = t ^ 3 / (1 + t) := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hε) hε
  simp [f] at this
  linarith

/-- `log(1 − ε) ≤ −ε − ε²/2` for `0 ≤ ε < 1`: the first two terms of the series
`−log(1 − ε) = ∑ εⁿ/n` (all terms nonnegative). Used in Dasgupta–Gupta 2003, proof of Lem 2.2,
and Laurent–Massart 2000, Lem 1. Atlas: `jl-distributional`, `chi-square-lower-tail`
(helper). -/
theorem log_one_sub_le_neg_sub_sq_div_two {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Real.log (1 - ε) ≤ -ε - ε ^ 2 / 2 := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := ε) (by rwa [abs_of_nonneg hε0])
  have := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) h
  simp [Finset.sum_range_succ] at this
  linarith

end NLAlib
