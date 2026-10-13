import NLAlib.Polynomial.BestApproximation.NodeSimplex
import NLAlib.Polynomial.BestApproximation.InterpolationProjection
import NLAlib.ForMathlib.LinearAlgebra.LagrangeBounds

/-!
# Quantitative boundary control of interpolation peaks

Finite cardinal products relate each small-gap peak to a far-gap peak. The
resulting uniform gap lower bound proves compactness at bounded peak differences.
Helpers for `lebesgue-constant-lower-bound`.
-/

noncomputable section

open Set Finset Polynomial

namespace NLAlib

/-- Every strictly ordered canonical node lies in the unit interval.
Source: the fixed endpoint ordering; helper for `lebesgue-constant-lower-bound`. -/
theorem canonicalIntervalNodes_mem_Icc {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (j : Fin (n + 2)) :
    canonicalIntervalNodes n t j ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · simpa using ht.monotone (Fin.zero_le j)
  · simpa using ht.monotone (Fin.le_last j)

/-- A small canonical gap controls the Lebesgue function by its value at any far point.
Source: focused reroutes, quantitative boundary estimate, with
`C=2^n(n+1)^(n+1)` for `n` interior nodes. -/
theorem lebesgueFunction_le_gap_mul_of_far {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) {x y : ℝ}
    (hx : x ∈ Icc (canonicalIntervalNodes n t i.castSucc) (canonicalIntervalNodes n t i.succ))
    (hy : ∀ j, 1 / ((n : ℝ) + 1) ≤ |y - canonicalIntervalNodes n t j|) :
    lebesgueFunction (canonicalIntervalNodes n t) x ≤
      (2 ^ n * ((n : ℝ) + 1) ^ (n + 1) *
        (canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc)) *
      lebesgueFunction (canonicalIntervalNodes n t) y := by
  let v := canonicalIntervalNodes n t
  let δ := v i.succ - v i.castSucc
  have hi : v i.castSucc < v i.succ := ht Fin.castSucc_lt_succ
  have hδ : 0 ≤ δ := sub_nonneg.mpr hi.le
  have hxI : x ∈ Icc (-1 : ℝ) 1 :=
    ⟨(canonicalIntervalNodes_mem_Icc ht i.castSucc).1.trans hx.1,
      hx.2.trans (canonicalIntervalNodes_mem_Icc ht i.succ).2⟩
  have hxa : |x - v i.castSucc| ≤ δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    dsimp [δ]
    linarith [hx.2]
  have hxb : |x - v i.succ| ≤ δ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
    dsimp [δ]
    linarith [hx.1]
  have hxB (j : Fin (n + 2)) : |x - v j| ≤ 2 := by
    have hj := canonicalIntervalNodes_mem_Icc ht j
    exact abs_le.mpr ⟨by linarith [hxI.1, hj.2], by linarith [hxI.2, hj.1]⟩
  have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hfactor : δ * (2 : ℝ) ^ n / (1 / ((n : ℝ) + 1)) ^ (n + 1) =
      2 ^ n * ((n : ℝ) + 1) ^ (n + 1) * δ := by
    rw [one_div, inv_pow, div_inv_eq_mul]
    ring
  unfold lebesgueFunction
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  have h := abs_eval_lagrange_basis_le_gap_mul univ v
    (a := i.castSucc) (b := i.succ) (j := j) (x := x) (y := y)
    (δ := δ) (B := 2) (r := 1 / ((n : ℝ) + 1)) (mem_univ _) (mem_univ _)
    (ne_of_lt Fin.castSucc_lt_succ) (mem_univ _) hδ (by norm_num) hr hxa hxb
    (fun j _ => hxB j) (fun j _ => hy j)
  simpa only [card_univ, Fintype.card_fin, Nat.add_sub_cancel,
    show n + 2 - 1 = n + 1 by omega, hfactor, v, δ] using h

/-- The lengths of the canonical node gaps telescope to two.
Source: finite telescoping; helper for `lebesgue-constant-lower-bound`. -/
theorem sum_canonicalIntervalNodes_gaps (n : ℕ) (t : Fin n → ℝ) :
    (∑ i : Fin (n + 1), (canonicalIntervalNodes n t i.succ -
      canonicalIntervalNodes n t i.castSucc)) = 2 := by
  have h0 := Fin.sum_univ_succ (canonicalIntervalNodes n t)
  have h1 := Fin.sum_univ_castSucc (canonicalIntervalNodes n t)
  rw [sum_sub_distrib]
  simp only [canonicalIntervalNodes_zero, canonicalIntervalNodes_last] at h0 h1
  linarith

/-- Some canonical gap midpoint is at least `1/(n+1)` from every node.
Source: a largest gap has length at least the average gap; helper for
`lebesgue-constant-lower-bound`. -/
theorem exists_gap_midpoint_far {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) :
    ∃ i : Fin (n + 1), ∃ y ∈ Icc (canonicalIntervalNodes n t i.castSucc)
      (canonicalIntervalNodes n t i.succ),
      ∀ j, 1 / ((n : ℝ) + 1) ≤ |y - canonicalIntervalNodes n t j| := by
  let v := canonicalIntervalNodes n t
  let gap : Fin (n + 1) → ℝ := fun i => v i.succ - v i.castSucc
  obtain ⟨i, _, hmax⟩ := exists_max_image univ gap univ_nonempty
  have hsum : (2 : ℝ) ≤ ((n : ℝ) + 1) * gap i := by
    calc
      _ = ∑ j, gap j := (sum_canonicalIntervalNodes_gaps n t).symm
      _ ≤ ∑ _j : Fin (n + 1), gap i := sum_le_sum (fun j _ => hmax j (mem_univ j))
      _ = _ := by simp
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hfar : 1 / ((n : ℝ) + 1) ≤ gap i / 2 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [hsum]
  have hi : v i.castSucc < v i.succ := ht Fin.castSucc_lt_succ
  let y : ℝ := (v i.castSucc + v i.succ) / 2
  refine ⟨i, y, ⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩, ?_⟩
  intro j
  rcases le_or_gt j i.castSucc with hj | hj
  · have hvj : v j ≤ v i.castSucc := ht.monotone hj
    have hdist : gap i / 2 ≤ |y - v j| := by
      rw [abs_of_nonneg (by dsimp [y]; linarith)]
      dsimp [gap, y]
      linarith
    exact hfar.trans hdist
  · have hij : i.succ ≤ j := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
      omega
    have hvj : v i.succ ≤ v j := ht.monotone hij
    have hdist : gap i / 2 ≤ |y - v j| := by
      rw [abs_of_nonpos (by dsimp [y]; linarith)]
      dsimp [gap, y]
      linarith
    exact hfar.trans hdist

/-- Every canonical gap peak is at least one.
Source: the cardinal partition of unity; helper for `lebesgue-constant-lower-bound`. -/
theorem one_le_interpolationGapPeak {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    1 ≤ interpolationGapPeak n t i := by
  have hi : canonicalIntervalNodes n t i.castSucc ≤ canonicalIntervalNodes n t i.succ :=
    (ht Fin.castSucc_lt_succ).le
  exact (one_le_lebesgueFunction _ ht.injective (canonicalIntervalNodes n t i.castSucc)).trans
    (lebesgueFunction_le_lebesgueConstant _ (left_mem_Icc.mpr hi))

/-- A single far-gap peak controls every small-gap peak with the explicit cardinal constant.
Source: focused reroutes, quantitative boundary estimate. -/
theorem exists_gap_peak_ratio {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) :
    ∃ l : Fin (n + 1), ∀ i : Fin (n + 1), interpolationGapPeak n t i ≤
      (2 ^ n * ((n : ℝ) + 1) ^ (n + 1) *
        (canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc)) *
      interpolationGapPeak n t l := by
  obtain ⟨l, y, hy, hfar⟩ := exists_gap_midpoint_far ht
  refine ⟨l, fun i => ?_⟩
  have hcoef : 0 ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (n + 1) *
      (canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc) := by
    have hi := ht (Fin.castSucc_lt_succ (i := i))
    positivity
  have hpeak : 0 ≤ interpolationGapPeak n t l := norm_nonneg _
  apply lebesgueConstant_le_of_forall _ (mul_nonneg hcoef hpeak)
  intro x hx
  exact (lebesgueFunction_le_gap_mul_of_far ht i hx hfar).trans
    (mul_le_mul_of_nonneg_left (lebesgueFunction_le_lebesgueConstant _ hy) hcoef)

/-- Bounded first-gap differences bound every pairwise peak difference by `2R`.
Source: the supremum norm on the finite peak-difference vector; boundary helper. -/
theorem interpolationGapPeak_sub_le_of_norm_difference_le {n : ℕ} {t : Fin n → ℝ}
    {R : ℝ} (hR : 0 ≤ R) (hbound : ‖interpolationPeakDifference n t‖ ≤ R)
    (i j : Fin (n + 1)) :
    interpolationGapPeak n t i - interpolationGapPeak n t j ≤ 2 * R := by
  have hfirst (k : Fin (n + 1)) : |interpolationGapPeak n t k - interpolationGapPeak n t 0| ≤ R := by
    refine Fin.cases (by simpa using hR) (fun l => ?_) k
    exact (norm_le_pi_norm (interpolationPeakDifference n t) l).trans hbound
  have hi := (abs_le.mp (hfirst i)).2
  have hj := (abs_le.mp (hfirst j)).1
  linarith

/-- Bounded peak differences keep every node gap quantitatively away from collision.
Source: focused reroutes, properness estimate, in first-gap difference coordinates.
The denominator is `2^n(n+1)^(n+1)(2R+1)` for `n` interior nodes. -/
theorem canonicalIntervalNodes_gap_ge_of_norm_difference_le {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ‖interpolationPeakDifference n t‖ ≤ R) (i : Fin (n + 1)) :
    1 / (2 ^ n * ((n : ℝ) + 1) ^ (n + 1) * (2 * R + 1)) ≤
      canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc := by
  obtain ⟨l, hratio⟩ := exists_gap_peak_ratio ht
  let C : ℝ := 2 ^ n * ((n : ℝ) + 1) ^ (n + 1)
  let δ : ℝ := canonicalIntervalNodes n t i.succ - canonicalIntervalNodes n t i.castSucc
  let q : ℝ := C * δ
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < δ := sub_pos.mpr (ht Fin.castSucc_lt_succ)
  have hq : 0 ≤ q := (mul_pos hC hδ).le
  have hpeak := one_le_interpolationGapPeak ht i
  have hdiff := interpolationGapPeak_sub_le_of_norm_difference_le hR hbound l i
  have hrat : interpolationGapPeak n t i ≤ q * interpolationGapPeak n t l := hratio i
  have hscaled : interpolationGapPeak n t i ≤ q * (interpolationGapPeak n t i + 2 * R) :=
    hrat.trans (mul_le_mul_of_nonneg_left (by linarith :
      interpolationGapPeak n t l ≤ interpolationGapPeak n t i + 2 * R) hq)
  have hprod : 1 ≤ q * (2 * R + 1) := by
    by_cases hqone : 1 ≤ q
    · exact hqone.trans (by nlinarith [mul_nonneg hq hR])
    · have hlow := mul_le_mul_of_nonneg_left hpeak (show 0 ≤ 1 - q by linarith)
      nlinarith [hlow, hscaled]
  apply (div_le_iff₀ (show 0 < C * (2 * R + 1) by positivity)).mpr
  change 1 ≤ δ * (C * (2 * R + 1))
  simpa only [q, mul_assoc, mul_comm, mul_left_comm] using hprod

end NLAlib
