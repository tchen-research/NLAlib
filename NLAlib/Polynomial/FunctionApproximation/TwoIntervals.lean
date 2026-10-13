import NLAlib.Polynomial.FunctionApproximation.Approximation

/-!
# Residual polynomials on two intervals

Quadratic folding turns two intervals of equal length into a positive interval,
where the existing Chebyshev residual applies. Realises `two-interval-minimax`.
-/

noncomputable section

open Polynomial Set Real

namespace NLAlib

/-- Two disjoint intervals of equal length fold into the positive interval
`[-bc,-ad]` under `x²-(b+c)x`.
Source: Greenbaum (1997), §3.1; operator derivations §3, helper for
`two-interval-minimax`. -/
theorem quadratic_mem_Icc_of_mem_two_intervals {a b c d x : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hlen : d - c = b - a)
    (hx : x ∈ Icc a b ∪ Icc c d) :
    x ^ 2 - (b + c) * x ∈ Icc (-(b * c)) (-(a * d)) := by
  have hends : a + d = b + c := by linarith
  have hupper : -(a * d) - (x ^ 2 - (b + c) * x) = (x - a) * (d - x) := by
    rw [← hends]
    ring
  rcases hx with hx | hx
  · constructor
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx.2)
        (sub_nonpos.mpr (hx.2.trans hbc.le))]
    · have hp := mul_nonneg (sub_nonneg.mpr hx.1)
        (sub_nonneg.mpr (hx.2.trans (hbc.le.trans hcd.le)))
      rw [← hupper] at hp
      linarith
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr (hbc.le.trans hx.1))
        (sub_nonneg.mpr hx.1)]
    · have hp := mul_nonneg (sub_nonneg.mpr (hab.le.trans (hbc.le.trans hx.1)))
        (sub_nonneg.mpr hx.2)
      rw [← hupper] at hp
      linarith

/-- A Chebyshev residual composed with quadratic folding has degree at most `2k`,
equals one at zero, and is exponentially small on two equal-length intervals.
Source: Greenbaum (1997), §3.1; Liesen–Strakoš (2013), §5.6;
operator derivations §3. No optimality assertion is added.
atlas: two-interval-minimax -/
theorem exists_degree_le_abs_eval_le_on_two_intervals {a b c d : ℝ}
    (hab : a < b) (hb : b < 0) (hc : 0 < c) (hcd : c < d)
    (hlen : d - c = b - a) (k : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ (2 * k : ℕ) ∧ p.eval 0 = 1 ∧
      ∀ x ∈ Icc a b ∪ Icc c d,
        |p.eval x| ≤ 2 * ((√|a * d| - √|b * c|) / (√|a * d| + √|b * c|)) ^ k := by
  have ha : a < 0 := hab.trans hb
  have hd : 0 < d := hc.trans hcd
  have hbc : b < c := hb.trans hc
  have hα : 0 < -(b * c) := neg_pos.mpr (mul_neg_of_neg_of_pos hb hc)
  have hβ : -(b * c) < -(a * d) := by
    have hprod := mul_pos (sub_pos.mpr hab) (sub_pos.mpr (hab.trans hbc))
    nlinarith
  let H : ℝ[X] := X ^ 2 - C (b + c) * X
  let p := (chebyshevResidual (-(b * c)) (-(a * d)) k).comp H
  refine ⟨p, ?_, ?_, ?_⟩
  · apply degree_le_of_natDegree_le
    have hH : H.natDegree ≤ 2 := by dsimp [H]; compute_degree
    have hr := natDegree_le_of_degree_le
      (degree_chebyshevResidual_le (-(b * c)) (-(a * d)) k)
    exact natDegree_comp_le.trans (by nlinarith)
  · simpa [p, H] using (eval_chebyshevResidual_zero (q := k) hα hβ)
  · intro x hx
    have hmem := quadratic_mem_Icc_of_mem_two_intervals hab hbc hcd hlen hx
    have hbound := abs_eval_chebyshevResidual_le_two_mul_pow k hα hβ hmem
    simpa [p, H, abs_of_neg (mul_neg_of_neg_of_pos ha hd),
      abs_of_neg (mul_neg_of_neg_of_pos hb hc)] using hbound

end NLAlib
