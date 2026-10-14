import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Polynomial approximation of the exponential on a half-line

Every degree has exact best uniform error one half for `exp (-x)` on `x ≥ 0`.
Finite uniform error forces a polynomial to be constant. This is the polynomial
subcase of Trefethen, ATAP, Theorem 25.2, separated from rational asymptotics.
-/

noncomputable section
open Polynomial Filter
open scoped Topology
namespace NLAlib

/-- A polynomial with finite uniform error against the decaying exponential on
the positive half-line is constant. Source: ATAP, Theorem 25.2, polynomial subcase. -/
theorem degree_le_zero_of_uniform_exp_neg_error {p : ℝ[X]} {E : ℝ}
    (hE : ∀ x : ℝ, 0 ≤ x → |Real.exp (-x) - p.eval x| ≤ E) : p.degree ≤ 0 := by
  apply (p.isBoundedUnder_abs_atTop_iff).mp
  refine ⟨E + 1, eventually_map.mpr ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have h := abs_le.mp (hE x hx)
  have hpos := Real.exp_pos (-x)
  have hle : Real.exp (-x) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every polynomial approximation of `exp (-x)` on the positive half-line has
uniform error at least one half, independently of its degree.
Source: Trefethen, ATAP, Theorem 25.2.
atlas: exp-rational-halfline (partial) -/
theorem one_half_le_uniform_exp_neg_error {p : ℝ[X]} {E : ℝ}
    (hE : ∀ x : ℝ, 0 ≤ x → |Real.exp (-x) - p.eval x| ≤ E) : 1 / 2 ≤ E := by
  have hp := p.eq_C_of_degree_le_zero (degree_le_zero_of_uniform_exp_neg_error hE)
  have h0 := hE 0 le_rfl
  rw [hp] at h0
  simp only [eval_C, neg_zero, Real.exp_zero] at h0
  have hlim : Tendsto (fun x : ℝ => |Real.exp (-x) - p.coeff 0|) atTop
      (𝓝 |p.coeff 0|) := by
    have h := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).sub_const (p.coeff 0)
    simpa using h.abs
  have hc : |p.coeff 0| ≤ E := le_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hb := hE x hx
    rw [hp, eval_C] at hb
    exact hb)
  have h0' := (abs_le.mp h0).2
  have hc' := (abs_le.mp hc).2
  linarith

/-- The constant polynomial one half attains error one half against `exp (-x)`
on the positive half-line. Source: ATAP, Theorem 25.2. -/
theorem abs_exp_neg_sub_one_half_le {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-x) - 1 / 2| ≤ 1 / 2 := by
  have hpos := Real.exp_pos (-x)
  have hle : Real.exp (-x) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The best uniform polynomial error for the exponential on a half-line is
exactly one half at every degree, expressed as the least attainable uniform bound.
This includes degree zero; it is independent of the excluded Halphen asymptotic.
Source: Trefethen, ATAP, Theorem 25.2.
atlas: exp-rational-halfline (partial) -/
theorem isLeast_uniform_polynomial_exp_neg_error (n : ℕ) :
    IsLeast {E : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
      ∀ x : ℝ, 0 ≤ x → |Real.exp (-x) - p.eval x| ≤ E} (1 / 2) := by
  refine ⟨⟨C (1 / 2), ?_, ?_⟩, ?_⟩
  · exact degree_C_le.trans (by exact_mod_cast Nat.zero_le n)
  · simpa only [eval_C] using fun x hx => abs_exp_neg_sub_one_half_le hx
  · rintro E ⟨p, _, hE⟩
    exact one_half_le_uniform_exp_neg_error hE

/-- Every polynomial approximation of `exp x` on the negative half-line has
uniform error at least one half. This is the reflected orientation of the
half-line polynomial clause in ATAP, Theorem 25.2.
atlas: exp-rational-halfline (partial) -/
theorem one_half_le_uniform_exp_error_negative_halfLine {p : ℝ[X]} {E : ℝ}
    (hE : ∀ x : ℝ, x ≤ 0 → |Real.exp x - p.eval x| ≤ E) : 1/2 ≤ E := by
  apply one_half_le_uniform_exp_neg_error (p := p.comp (-X))
  intro x hx
  simpa only [eval_comp, eval_neg, eval_X] using hE (-x) (neg_nonpos.mpr hx)

/-- The best uniform polynomial error for `exp x` on the negative half-line is
exactly one half at every degree, in the original atlas orientation. The
constant one half attains the bound.
Source: Trefethen, ATAP, Theorem 25.2, reflected polynomial subcase.
atlas: exp-rational-halfline (partial) -/
theorem isLeast_uniform_polynomial_exp_error_negative_halfLine (n : ℕ) :
    IsLeast {E : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
      ∀ x : ℝ, x ≤ 0 → |Real.exp x - p.eval x| ≤ E} (1/2) := by
  refine ⟨⟨C (1/2), degree_C_le.trans (by exact_mod_cast Nat.zero_le n), ?_⟩, ?_⟩
  · intro x hx
    simpa only [neg_neg, eval_C] using abs_exp_neg_sub_one_half_le (neg_nonneg.mpr hx)
  · rintro E ⟨p, _, hE⟩
    exact one_half_le_uniform_exp_error_negative_halfLine hE

end NLAlib
