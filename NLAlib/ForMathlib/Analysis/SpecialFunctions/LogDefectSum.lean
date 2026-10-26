import NLAlib.ForMathlib.Analysis.SpecialFunctions.LogDefect

/-!
# Finite sums of logarithmic defects

A positive family whose total logarithmic defect is at most `eps ≤ 1 / 6`
has squared distance at most `6 * eps` from the constant family one.
For a family with sum equal to its cardinality, the defect bound follows from
the product lower bound `exp (-eps) ≤ ∏ i, x i`.

No nonemptiness assumption or separate hypothesis `0 ≤ eps` is needed.
-/

noncomputable section

open scoped BigOperators

namespace Real

/-- The logarithmic defect of a positive real number is nonnegative. -/
theorem logDefect_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ logDefect x := by
  have hlog := log_le_sub_one_of_pos hx
  unfold logDefect
  linarith

/-- A small total logarithmic defect controls the squared distance of a positive
finite family from the constant family one. -/
theorem sum_sq_sub_one_le_six_mul_of_sum_logDefect_le
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (eps : ℝ)
    (hx : ∀ i, 0 < x i) (heps : eps ≤ 1 / 6)
    (hdef : ∑ i, logDefect (x i) ≤ eps) :
    ∑ i, (x i - 1) ^ 2 ≤ 6 * eps := by
  have hnonneg : ∀ i, 0 ≤ logDefect (x i) := fun i => logDefect_nonneg (hx i)
  have hsingle : ∀ i, logDefect (x i) ≤ 1 / 6 := by
    intro i
    exact ((Finset.single_le_sum (fun j _ => hnonneg j)
      (Finset.mem_univ i)).trans hdef).trans heps
  calc
    (∑ i, (x i - 1) ^ 2) ≤ ∑ i, 6 * logDefect (x i) :=
      Finset.sum_le_sum fun i _ => sq_sub_one_le_six_mul_logDefect (hx i) (hsingle i)
    _ = 6 * ∑ i, logDefect (x i) := (Finset.mul_sum _ _ _).symm
    _ ≤ 6 * eps := mul_le_mul_of_nonneg_left hdef (by norm_num)

/-- For a positive finite family with sum equal to its cardinality, a product
lower bound by `exp (-eps)`, with `eps ≤ 1 / 6`, implies a quadratic bound on
its distance from the constant family one. -/
theorem sum_sq_sub_one_le_six_mul_of_exp_neg_le_prod
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (eps : ℝ)
    (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = (Fintype.card ι : ℝ))
    (heps : eps ≤ 1 / 6) (hprod : exp (-eps) ≤ ∏ i, x i) :
    ∑ i, (x i - 1) ^ 2 ≤ 6 * eps := by
  have hlog : log (∏ i, x i) = ∑ i, log (x i) :=
    log_prod (fun i _ => ne_of_gt (hx i))
  have hlog_lower : -eps ≤ ∑ i, log (x i) := by
    have h := log_le_log (exp_pos (-eps)) hprod
    rwa [log_exp, hlog] at h
  apply sum_sq_sub_one_le_six_mul_of_sum_logDefect_le x eps hx heps
  have hdef : (∑ i, logDefect (x i)) =
      (∑ i, x i) - (Fintype.card ι : ℝ) - ∑ i, log (x i) := by
    unfold logDefect
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
  rw [hdef, hsum]
  linarith

end Real
