import NLAlib.Polynomial.BestApproximation.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

/-!
# Signed Lebesgue polynomials on interpolation gaps

The signs of the actual Lagrange cardinals are constant on every open node gap.
Counting the negative factors gives the catalogue's finite gap polynomial.
-/

noncomputable section
open Polynomial Finset Real Set
namespace NLAlib

private theorem abs_prod_eq_neg_one_pow_filter_mul {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    |∏ k ∈ s, f k| = (-1 : ℝ) ^ (s.filter (fun k => f k < 0)).card * ∏ k ∈ s, f k := by
  have hterm : ∀ k, |f k| = (if f k < 0 then (-1 : ℝ) else 1) * f k := by
    intro k
    split_ifs with hk
    · rw [abs_of_neg hk]; ring
    · rw [abs_of_nonneg (le_of_not_gt hk), one_mul]
  rw [abs_prod]
  simp_rw [hterm]
  rw [prod_mul_distrib, prod_ite]
  simp only [prod_const, one_pow, mul_one]

/-- The actual Lagrange cardinal is the finite product of node-difference ratios.
Source: Lagrange's cardinal formula; helper for node derivatives and interval peaks. -/
theorem eval_lagrange_basis_eq_prod_div {m : ℕ} (v : Fin m → ℝ) (j : Fin m) (x : ℝ) :
    (Lagrange.basis univ v j).eval x =
      ∏ k ∈ univ.erase j, (x - v k) / (v j - v k) := by
  simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  apply prod_congr rfl
  intro k _
  rw [div_eq_mul_inv, mul_comm]

/-- The actual Lagrange cardinal has the specified fixed sign on an ordered
grid's open gap.
Source: cardinal products; focused reroutes, interval peak polynomial. -/
theorem interpolationGapSign_mul_eval_basis_eq_abs {n : ℕ}
    {v : Fin (n + 2) → ℝ} (hv : StrictMono v) (i : Fin (n + 1)) (j : Fin (n + 2))
    {x : ℝ} (hx : x ∈ Ioo (v i.castSucc) (v i.succ)) :
    interpolationGapSign n i j * (Lagrange.basis univ v j).eval x =
      |(Lagrange.basis univ v j).eval x| := by
  have hleft (k : Fin (n + 2)) (hk : k.val ≤ i.val) : v k < x :=
    lt_of_le_of_lt (hv.monotone (by exact hk)) hx.1
  have hright (k : Fin (n + 2)) (hk : i.val < k.val) : x < v k :=
    lt_of_lt_of_le hx.2 (hv.monotone (by change i.val + 1 ≤ k.val; omega))
  rw [eval_lagrange_basis_eq_prod_div]
  rw [abs_prod_eq_neg_one_pow_filter_mul]
  congr 1
  unfold interpolationGapSign
  split_ifs with hji
  · have hfilter : (univ.erase j).filter (fun k => (x - v k) / (v j - v k) < 0) =
        Finset.Ioc j i.castSucc := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Ioc]
      by_cases hkj : k = j
      · subst k
        simp
      · by_cases hki : k.val ≤ i.val
        · have hnum : 0 < x - v k := sub_pos.mpr (hleft k hki)
          by_cases hjk : j < k
          · have hden : v j - v k < 0 := sub_neg.mpr (hv hjk)
            have hneg := div_neg_of_pos_of_neg hnum hden
            simp only [hneg]
            exact ⟨fun _ => ⟨hjk, hki⟩, fun _ => ⟨hkj, trivial⟩⟩
          · have hkj' : k < j := lt_of_le_of_ne (le_of_not_gt hjk) hkj
            have hpos := div_pos hnum (sub_pos.mpr (hv hkj'))
            have hnot : ¬ (x - v k) / (v j - v k) < 0 := not_lt_of_ge hpos.le
            simp only [hnot, hjk, false_and, and_false]
        · have hnum : x - v k < 0 := sub_neg.mpr (hright k (by omega))
          have hjk : j < k := by change j.val < k.val; omega
          have hpos := div_pos_of_neg_of_neg hnum (sub_neg.mpr (hv hjk))
          have hnot : ¬ (x - v k) / (v j - v k) < 0 := not_lt_of_ge hpos.le
          have hkI : ¬ k ≤ i.castSucc := by exact hki
          simp only [hnot, hkI, and_false]
    rw [hfilter, Fin.card_Ioc]
    rfl
  · have hij : i.val < j.val := by omega
    have hfilter : (univ.erase j).filter (fun k => (x - v k) / (v j - v k) < 0) =
        Finset.Ioo i.castSucc j := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Ioo]
      by_cases hkj : k = j
      · subst k
        simp
      · by_cases hki : k.val ≤ i.val
        · have hnum : 0 < x - v k := sub_pos.mpr (hleft k hki)
          have hkj' : k < j := by change k.val < j.val; omega
          have hpos := div_pos hnum (sub_pos.mpr (hv hkj'))
          have hnot : ¬ (x - v k) / (v j - v k) < 0 := not_lt_of_ge hpos.le
          have hkI : ¬ i.castSucc < k := by change ¬ i.val < k.val; omega
          simp only [hnot, hkI, false_and, and_false]
        · have hnum : x - v k < 0 := sub_neg.mpr (hright k (by omega))
          by_cases hkj' : k < j
          · have hneg := div_neg_of_neg_of_pos hnum (sub_pos.mpr (hv hkj'))
            have hkI : i.castSucc < k := by change i.val < k.val; omega
            simp only [hneg]
            exact ⟨fun _ => ⟨hkI, hkj'⟩, fun _ => ⟨hkj, trivial⟩⟩
          · have hjk : j < k := lt_of_le_of_ne (le_of_not_gt hkj') (Ne.symm hkj)
            have hpos := div_pos_of_neg_of_neg hnum (sub_neg.mpr (hv hjk))
            have hnot : ¬ (x - v k) / (v j - v k) < 0 := not_lt_of_ge hpos.le
            simp only [hnot, hkj', and_false]
    rw [hfilter, Fin.card_Ioo]
    rfl

/-- The actual finite gap polynomial equals the Lebesgue function throughout
the open gap of a canonical ordered node configuration.
Source: signed Lagrange cardinals; focused reroutes, interval peak polynomial. -/
theorem eval_interpolationGapPolynomial_eq_lebesgueFunction {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ)) :
    (interpolationGapPolynomial n t i).eval x = lebesgueFunction (canonicalIntervalNodes n t) x := by
  simp only [interpolationGapPolynomial, Lagrange.interpolate_apply, eval_finsetSum, eval_mul,
    eval_C, lebesgueFunction]
  apply sum_congr rfl
  intro j _
  exact interpolationGapSign_mul_eval_basis_eq_abs ht i j hx

/-- Every cardinal is nonzero inside an ordered grid gap.
Source: its finite product of nonzero node differences; interval peak argument. -/
theorem eval_basis_ne_zero_on_gap {n : ℕ} {v : Fin (n + 2) → ℝ} (hv : StrictMono v)
    (i : Fin (n + 1)) (j : Fin (n + 2)) {x : ℝ} (hx : x ∈ Ioo (v i.castSucc) (v i.succ)) :
    (Lagrange.basis univ v j).eval x ≠ 0 := by
  rw [eval_lagrange_basis_eq_prod_div]
  apply prod_ne_zero_iff.mpr
  intro k hk
  have hkj : k ≠ j := (mem_erase.mp hk).1
  apply div_ne_zero
  · apply sub_ne_zero.mpr
    by_cases hki : k.val ≤ i.val
    · exact (lt_of_le_of_lt (hv.monotone (show k ≤ i.castSucc from hki)) hx.1).ne'
    · exact (lt_of_lt_of_le hx.2 (hv.monotone (show i.succ ≤ k by change i.val + 1 ≤ k.val; omega))).ne
  · exact sub_ne_zero.mpr (fun h => hkj (hv.injective h.symm))

/-- With at least one interior node, every gap has a negative cardinal.
Source: alternating cardinal-product signs; focused reroutes, strict interval peaks. -/
theorem exists_negative_eval_basis_on_gap {n : ℕ} (hn : 0 < n)
    {v : Fin (n + 2) → ℝ} (hv : StrictMono v) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo (v i.castSucc) (v i.succ)) :
    ∃ j : Fin (n + 2), (Lagrange.basis univ v j).eval x < 0 := by
  have hsign : ∃ j : Fin (n + 2), interpolationGapSign n i j = -1 := by
    by_cases hi : i.val = 0
    · refine ⟨⟨2, by omega⟩, ?_⟩
      simp [interpolationGapSign, hi]
    · refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
      have hle : i.val - 1 ≤ i.val := by omega
      have hsub : i.val - (i.val - 1) = 1 := by omega
      simp only [interpolationGapSign, hle, if_true, hsub, pow_one]
  obtain ⟨j, hj⟩ := hsign
  refine ⟨j, ?_⟩
  have heq := interpolationGapSign_mul_eval_basis_eq_abs hv i j hx
  rw [hj, neg_one_mul] at heq
  have hne := eval_basis_ne_zero_on_gap hv i j hx
  have ha : 0 < |(Lagrange.basis univ v j).eval x| := abs_pos.mpr hne
  linarith

/-- The actual Lebesgue function is strictly above one in every open gap
when there are at least three interpolation nodes.
Source: partition of unity and a negative cardinal; focused reroutes. -/
theorem one_lt_lebesgueFunction_on_gap {n : ℕ} (hn : 0 < n)
    {v : Fin (n + 2) → ℝ} (hv : StrictMono v) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo (v i.castSucc) (v i.succ)) : 1 < lebesgueFunction v x := by
  obtain ⟨j, hj⟩ := exists_negative_eval_basis_on_gap hn hv i hx
  have hsum : (∑ k : Fin (n + 2), (Lagrange.basis univ v k).eval x) = 1 := by
    rw [← eval_finsetSum, Lagrange.sum_basis hv.injective.injOn (by simp), eval_one]
  rw [← hsum, lebesgueFunction]
  apply sum_lt_sum (fun k _ => le_abs_self _) ⟨j, mem_univ j, ?_⟩
  rw [abs_of_neg hj]
  linarith

/-- The gap polynomial takes its prescribed signs at the actual canonical nodes.
Source: interpolation at distinct nodes; focused reroutes. -/
theorem eval_interpolationGapPolynomial_node {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (interpolationGapPolynomial n t i).eval (canonicalIntervalNodes n t j) =
      interpolationGapSign n i j := by
  exact Lagrange.eval_interpolate_at_node _ (ht.injective.injOn) (mem_univ j)

/-- Both endpoints of a gap have gap-polynomial value one.
Source: prescribed nodal signs; focused reroutes. -/
theorem eval_interpolationGapPolynomial_gap_endpoints {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    (interpolationGapPolynomial n t i).eval (canonicalIntervalNodes n t i.castSucc) = 1 ∧
      (interpolationGapPolynomial n t i).eval (canonicalIntervalNodes n t i.succ) = 1 := by
  simp only [eval_interpolationGapPolynomial_node ht, interpolationGapSign, Fin.val_castSucc,
    Fin.val_succ, le_refl, if_true, Nat.sub_self, pow_zero, Nat.not_succ_le_self,
    if_false, Nat.add_sub_cancel_left]
  norm_num

/-- The actual gap polynomial is strictly greater than one inside its own gap.
Source: signed cardinal identity; focused reroutes, strict interval peaks. -/
theorem one_lt_eval_interpolationGapPolynomial {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ)) :
    1 < (interpolationGapPolynomial n t i).eval x := by
  rw [eval_interpolationGapPolynomial_eq_lebesgueFunction ht i hx]
  exact one_lt_lebesgueFunction_on_gap hn ht i hx

/-- The actual gap polynomial is nonconstant for every positive interior dimension.
Source: endpoint value one and strictly larger interior values; focused reroutes. -/
theorem derivative_interpolationGapPolynomial_ne_zero {n : ℕ} (hn : 0 < n)
    {t : Fin n → ℝ} (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    (interpolationGapPolynomial n t i).derivative ≠ 0 := by
  intro hc
  let a := canonicalIntervalNodes n t i.castSucc
  let b := canonicalIntervalNodes n t i.succ
  have hab : a < b := ht (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
  have hmid : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  have hval := one_lt_eval_interpolationGapPolynomial hn ht i hmid
  have ha := (eval_interpolationGapPolynomial_gap_endpoints ht i).1
  rw [eq_C_of_derivative_eq_zero hc, eval_C] at hval ha
  linarith

end NLAlib
