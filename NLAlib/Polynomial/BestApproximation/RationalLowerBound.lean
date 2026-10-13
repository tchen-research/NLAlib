import NLAlib.Polynomial.BestApproximation.RationalExistence
import NLAlib.Polynomial.BestApproximation.AlternationLowerBound
import NLAlib.ForMathlib.Topology.Order.IntermediateValue

/-!
# Rational alternation lower bounds

An improved competitor would make the continuous rational difference alternate in sign.
The resulting interior zeros force its degree-bounded cross numerator to vanish.
Source: ATAP, Exercise 24.5; focused rederivations, Theorem `thm:rational`.
-/

noncomputable section

open Polynomial Set

namespace NLAlib

private local instance : DecidableEq (RatFunc ℝ) := Classical.decEq _

/-- The numerator of the difference from a baseline rational function has degree at most
the baseline's exact tangent degree. The zero baseline uses the competitor numerator.
Source: ATAP, Chapter 24, the defect-adjusted cross-numerator bound. -/
theorem degree_rational_difference_numerator_le {s : Set ℝ} {m n : ℕ}
    (r u : RatFunc ℝ) (hu : IsPoleFreeRationalApproximation s m n u) :
    (if r = 0 then u.num else u.num * r.denom - r.num * u.denom).degree ≤
      rationalAlternationDegree m n r := by
  classical
  by_cases hr0 : r = 0
  · simp only [hr0, if_pos, rationalAlternationDegree]
    exact hu.1
  · simp only [rationalAlternationDegree, if_neg hr0]
    apply (degree_sub_le _ _).trans
    apply max_le
    · calc
        (u.num * r.denom).degree ≤ u.num.degree + r.denom.degree := degree_mul_le _ _
        _ ≤ (m : WithBot ℕ) + r.denom.natDegree := add_le_add hu.1 degree_le_natDegree
        _ ≤ ↑(max (m + r.denom.natDegree) (n + r.num.natDegree)) := by
          norm_cast; exact le_max_left _ _
    · calc
        (r.num * u.denom).degree ≤ r.num.degree + u.denom.degree := degree_mul_le _ _
        _ ≤ (r.num.natDegree : WithBot ℕ) + n := add_le_add degree_le_natDegree hu.2.1
        _ ≤ ↑(max (m + r.denom.natDegree) (n + r.num.natDegree)) := by
          norm_cast; omega

/-- Vanishing of the difference cross numerator is equality of rational functions.
Source: the fraction identity used in the rational alternation theorem. -/
theorem ratFunc_eq_of_difference_numerator_eq_zero (r u : RatFunc ℝ)
    (hzero : (if r = 0 then u.num else u.num * r.denom - r.num * u.denom) = 0) : u = r := by
  classical
  by_cases hr0 : r = 0
  · rw [if_pos hr0] at hzero
    exact (RatFunc.num_eq_zero_iff.mp hzero).trans hr0.symm
  · rw [if_neg hr0] at hzero
    have heq := (RatFunc.num_mul_eq_mul_denom_iff (RatFunc.denom_ne_zero r)).mp
      (sub_eq_zero.mp hzero)
    exact heq.trans (RatFunc.num_div_denom r)

/-- The difference cross numerator vanishes at every point where two pole-free rational
functions agree. Source: the fraction identity used in rational root-counting. -/
theorem difference_numerator_eval_eq_zero_of_rationalContinuousMap_eq {s : Set ℝ}
    (r u : RatFunc ℝ) (hr : ∀ x ∈ s, r.denom.eval x ≠ 0)
    (hu : ∀ x ∈ s, u.denom.eval x ≠ 0) (x : s)
    (heq : rationalContinuousMap s u hu x = rationalContinuousMap s r hr x) :
    (if r = 0 then u.num else u.num * r.denom - r.num * u.denom).eval (x : ℝ) = 0 := by
  classical
  by_cases hr0 : r = 0
  · rw [if_pos hr0]
    have hval : u.num.eval (x : ℝ) / u.denom.eval (x : ℝ) = 0 := by
      simpa [rationalContinuousMap, hr0] using heq
    exact (div_eq_zero_iff).mp hval |>.resolve_right (hu x x.property)
  · rw [if_neg hr0, eval_sub, eval_mul, eval_mul]
    change u.num.eval (x : ℝ) / u.denom.eval (x : ℝ) =
      r.num.eval (x : ℝ) / r.denom.eval (x : ℝ) at heq
    exact sub_eq_zero.mpr ((div_eq_div_iff (hu x x.property) (hr x x.property)).mp heq)

/-- Alternating baseline errors of magnitude at least `ε` force every rational competitor
of the same type to have magnitude at least `ε` at one sample. Source: ATAP, Exercise 24.5.
The sample count is the exact defect-adjusted count, and the zero baseline is included.
atlas: rational-equioscillation (partial) -/
theorem exists_abs_sub_rationalContinuousMap_ge_of_alternation {a b : ℝ}
    (hab : a < b) {m n : ℕ} (f : C(Icc a b, ℝ)) (r : RatFunc ℝ)
    (hr : IsPoleFreeRationalApproximation (Icc a b) m n r)
    {v : Fin (rationalAlternationDegree m n r + 2) → Icc a b}
    (hv : StrictMono (fun i => (v i : ℝ)))
    (hsign : ∀ i : Fin (rationalAlternationDegree m n r + 1),
      (f (v i.castSucc) - rationalContinuousMap (Icc a b) r hr.2.2 (v i.castSucc)) *
        (f (v i.succ) - rationalContinuousMap (Icc a b) r hr.2.2 (v i.succ)) < 0)
    {ε : ℝ} (hε : ∀ i, ε ≤ |f (v i) - rationalContinuousMap (Icc a b) r hr.2.2 (v i)|)
    (u : RatFunc ℝ) (hu : IsPoleFreeRationalApproximation (Icc a b) m n u) :
    ∃ i, ε ≤ |f (v i) - rationalContinuousMap (Icc a b) u hu.2.2 (v i)| := by
  classical
  let : Fact (a ≤ b) := ⟨hab.le⟩
  by_contra! hbeat
  let g := rationalContinuousMap (Icc a b) u hu.2.2 - rationalContinuousMap (Icc a b) r hr.2.2
  let gg : C(ℝ, ℝ) := ContinuousMap.IccExtendCM g
  have hgv : ∀ i, gg (v i) = g (v i) := fun i =>
    ContinuousMap.IccExtendCM_of_mem (v i).property
  have hgsign : ∀ i : Fin (rationalAlternationDegree m n r + 1),
      gg (v i.castSucc) * gg (v i.succ) < 0 := by
    intro i
    have hi := mul_sub_mul_sub_neg_of_abs_lt (hsign i)
      ((hbeat i.castSucc).trans_le (hε i.castSucc))
      ((hbeat i.succ).trans_le (hε i.succ))
    simpa only [hgv, g, ContinuousMap.sub_apply, sub_sub_sub_cancel_left] using hi
  obtain ⟨c, hc, hczero⟩ := exists_strictMono_eq_zero_of_mul_neg hv
    gg.continuous.continuousOn hgsign
  let H := if r = 0 then u.num else u.num * r.denom - r.num * u.denom
  have hH : H.degree ≤ rationalAlternationDegree m n r :=
    degree_rational_difference_numerator_le r u hu
  have hHzero : H = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      (s := Finset.univ) (v := c) hc.injective.injOn
    · rw [Finset.card_univ, Fintype.card_fin]
      exact hH.trans_lt (by exact_mod_cast Nat.lt_succ_self (rationalAlternationDegree m n r))
    · intro i _
      have hcI : c i ∈ Icc a b :=
        ⟨(v i.castSucc).property.1.trans (hczero i).1.1.le,
          (hczero i).1.2.le.trans (v i.succ).property.2⟩
      have hzero := (hczero i).2
      rw [ContinuousMap.IccExtendCM_of_mem hcI] at hzero
      have heq : rationalContinuousMap (Icc a b) u hu.2.2 ⟨c i, hcI⟩ =
          rationalContinuousMap (Icc a b) r hr.2.2 ⟨c i, hcI⟩ := sub_eq_zero.mp hzero
      exact difference_numerator_eval_eq_zero_of_rationalContinuousMap_eq r u hr.2.2 hu.2.2 _ heq
  have hur := ratFunc_eq_of_difference_numerator_eq_zero r u hHzero
  subst u
  exact not_lt_of_ge (hε 0) (hbeat 0)

/-- The rational alternation certificate is a lower bound on best type-`(m,n)` error.
Source: ATAP, Exercise 24.5.
atlas: rational-equioscillation (partial) -/
theorem le_rationalMinimaxError_of_alternation {a b : ℝ} (hab : a < b) {m n : ℕ}
    (f : C(Icc a b, ℝ)) (r : RatFunc ℝ)
    (hr : IsPoleFreeRationalApproximation (Icc a b) m n r)
    {v : Fin (rationalAlternationDegree m n r + 2) → Icc a b}
    (hv : StrictMono (fun i => (v i : ℝ)))
    (hsign : ∀ i : Fin (rationalAlternationDegree m n r + 1),
      (f (v i.castSucc) - rationalContinuousMap (Icc a b) r hr.2.2 (v i.castSucc)) *
        (f (v i.succ) - rationalContinuousMap (Icc a b) r hr.2.2 (v i.succ)) < 0)
    {ε : ℝ} (hε : ∀ i, ε ≤ |f (v i) - rationalContinuousMap (Icc a b) r hr.2.2 (v i)|) :
    ε ≤ rationalMinimaxError m n f := by
  obtain ⟨u, hu, hbest⟩ := exists_norm_sub_eq_rationalMinimaxError hab m n f
  obtain ⟨i, hi⟩ := exists_abs_sub_rationalContinuousMap_ge_of_alternation hab f r hr hv hsign hε u hu
  exact hi.trans (by
    simpa [hbest] using (f - rationalContinuousMap (Icc a b) u hu.2.2).norm_coe_le_norm (v i))

end NLAlib
