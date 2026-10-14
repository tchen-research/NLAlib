import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Products of moments of one nonnegative finite variable

Weighted Chebyshev bounds products of power moments by the moment at the
sum of the exponents. This gives the spectral interpolation needed for
cyclic words with rank-one matrix insertions without fractional exponents.
-/

noncomputable section

namespace NLAlib

variable {ι : Type*} [Fintype ι]

/-- Two nonnegative weighted power moments are bounded by their joint
moment times the total weight. The weights need not sum to one. -/
theorem sum_mul_pow_mul_sum_mul_pow_le (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (a b : ℕ) :
    (∑ i, w i * x i ^ a) * (∑ i, w i * x i ^ b) ≤
      (∑ i, w i) * ∑ i, w i * x i ^ (a + b) := by
  classical
  have hpoint (i j : ι) :
      w i * w j * (x i ^ a * x j ^ b + x j ^ a * x i ^ b) ≤
        w i * w j * (x i ^ (a + b) + x j ^ (a + b)) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw i) (hw j))
    rw [pow_add, pow_add]
    rcases le_total (x i) (x j) with hij | hji
    · have ha := pow_le_pow_left₀ (hx i) hij a
      have hb := pow_le_pow_left₀ (hx i) hij b
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
    · have ha := pow_le_pow_left₀ (hx j) hji a
      have hb := pow_le_pow_left₀ (hx j) hji b
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpoint i j
  have hL : (∑ i, ∑ j, w i * w j * (x i ^ a * x j ^ b + x j ^ a * x i ^ b)) =
      2 * ((∑ i, w i * x i ^ a) * (∑ i, w i * x i ^ b)) := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [show (∑ i, ∑ j, w i * w j * (x j ^ a * x i ^ b)) =
      ∑ j, ∑ i, w i * w j * (x j ^ a * x i ^ b) from Finset.sum_comm]
    simp_rw [show ∀ i j, w i * w j * (x i ^ a * x j ^ b) =
      (w i * x i ^ a) * (w j * x j ^ b) by intros; ring,
      show ∀ i j, w j * w i * (x i ^ a * x j ^ b) =
      (w i * x i ^ a) * (w j * x j ^ b) by intros; ring]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hR : (∑ i, ∑ j, w i * w j * (x i ^ (a + b) + x j ^ (a + b))) =
      2 * ((∑ i, w i) * ∑ i, w i * x i ^ (a + b)) := by
    simp only [mul_add, Finset.sum_add_distrib]
    simp_rw [show ∀ i j, w i * w j * x i ^ (a + b) =
      (w i * x i ^ (a + b)) * w j by intros; ring,
      show ∀ i j, w i * w j * x j ^ (a + b) =
      w i * (w j * x j ^ (a + b)) by intros; ring]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hL, hR] at hsum
  linarith

/-- A nonempty product of weighted natural moments is bounded by the
moment at the sum of the exponents, times the appropriate total weight. -/
theorem prod_list_sum_mul_pow_le (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (ks : List ℕ) (hne : ks ≠ []) :
    (ks.map fun k => ∑ i, w i * x i ^ k).prod ≤
      (∑ i, w i) ^ (ks.length - 1) * ∑ i, w i * x i ^ ks.sum := by
  induction ks with
  | nil => exact (hne rfl).elim
  | cons k ks ih =>
    cases ks with
    | nil => simp
    | cons l ls =>
      have htail := ih (by simp)
      have hm (n : ℕ) : 0 ≤ ∑ i, w i * x i ^ n :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (pow_nonneg (hx i) n)
      simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons,
        Nat.add_sub_cancel] at *
      calc
        _ ≤ (∑ i, w i * x i ^ k) *
            ((∑ i, w i) ^ ls.length * ∑ i, w i * x i ^ (l + ls.sum)) :=
          mul_le_mul_of_nonneg_left htail (hm k)
        _ = (∑ i, w i) ^ ls.length *
            ((∑ i, w i * x i ^ k) * ∑ i, w i * x i ^ (l + ls.sum)) := by ring
        _ ≤ (∑ i, w i) ^ ls.length *
            ((∑ i, w i) * ∑ i, w i * x i ^ (k + (l + ls.sum))) :=
          mul_le_mul_of_nonneg_left (sum_mul_pow_mul_sum_mul_pow_le w x hw hx _ _)
            (pow_nonneg (Finset.sum_nonneg fun i _ => hw i) _)
        _ = _ := by rw [pow_succ]; ring

end NLAlib
