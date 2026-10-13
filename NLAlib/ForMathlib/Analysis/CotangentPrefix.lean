import NLAlib.ForMathlib.Analysis.CotangentIntegral
import Mathlib.Algebra.BigOperators.Intervals

/-! # Finite cotangent prefixes for Chebyshev-root samples

Reflection and convexity locate the smallest extremum sample at the central
index, without locating the actual interpolation gap maxima.
-/
noncomputable section
open Real Set Finset
namespace NLAlib

/-- The half-index cotangent prefix on the root sampling grid.
Source: focused reroutes, equation `polyretry:sample-C`. -/
def rootCotangentPrefix (N r : ℕ) : ℝ :=
  ∑ j ∈ range r, Real.cot (((j : ℝ) + 1 / 2) * π / (2 * N))

/-- The cotangent prefix expression for the `k`th root-grid extremum sample.
Source: focused reroutes, equation `polyretry:sample-C`. -/
def rootCotangentSample (N k : ℕ) : ℝ :=
  (rootCotangentPrefix N (N - k) + rootCotangentPrefix N k - rootCotangentPrefix N (2 * k)) / N

/-- Cotangent changes sign under reflection around pi.
Source: the elementary sine and cosine reflection identities. -/
theorem cot_pi_sub (x : ℝ) : Real.cot (π - x) = -Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, cos_pi_sub, sin_pi_sub, neg_div]

/-- Cotangent at the complementary half-quadrant angle is tangent.
Source: the elementary sine and cosine complement identities. -/
theorem cot_pi_div_two_sub (x : ℝ) : Real.cot (π / 2 - x) = tan x := by
  rw [Real.cot_eq_cos_div_sin, tan_eq_sin_div_cos, cos_pi_div_two_sub, sin_pi_div_two_sub]

/-- Cotangent minus tangent is twice the doubled-angle cotangent in the open half quadrant.
Source: focused reroutes, the central cotangent sample calculation. -/
theorem cot_sub_tan_eq_two_mul_cot_two_mul {x : ℝ} (hx : 0 < x) (hxπ : x < π / 2) :
    Real.cot x - tan x = 2 * Real.cot (2 * x) := by
  have hs : sin x ≠ 0 := (sin_pos_of_pos_of_lt_pi hx (by linarith [pi_pos])).ne'
  have hc : cos x ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hxπ⟩).ne'
  rw [Real.cot_eq_cos_div_sin, tan_eq_sin_div_cos, Real.cot_eq_cos_div_sin, sin_two_mul, cos_two_mul]
  field_simp [hs, hc]
  nlinarith [sin_sq_add_cos_sq x]

/-- Reflecting a complete half-index cotangent period reverses its signs.
Source: focused reroutes, finite cotangent-prefix reflection. -/
theorem cot_half_index_reflect {N j : ℕ} (hN : 0 < N) (hj : j < 2 * N) :
    Real.cot ((((2 * N - 1 - j : ℕ) : ℝ) + 1 / 2) * π / (2 * N)) =
      -Real.cot (((j : ℝ) + 1 / 2) * π / (2 * N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (((2 * N - 1 - j : ℕ) : ℝ) + 1 / 2) * π / (2 * N) =
      π - ((j : ℝ) + 1 / 2) * π / (2 * N) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  rw [heq, cot_pi_sub]

/-- A full cotangent prefix period sums to zero.
Source: focused reroutes, finite cotangent-prefix reflection. -/
theorem rootCotangentPrefix_two_mul_eq_zero {N : ℕ} (hN : 0 < N) :
    rootCotangentPrefix N (2 * N) = 0 := by
  let f := fun j : ℕ => Real.cot (((j : ℝ) + 1 / 2) * π / (2 * N))
  have hr := sum_range_reflect f (2 * N)
  have heq : (∑ j ∈ range (2 * N), f (2 * N - 1 - j)) = -∑ j ∈ range (2 * N), f j := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    exact cot_half_index_reflect hN (mem_range.mp hj)
  rw [heq] at hr
  change (∑ j ∈ range (2 * N), f j) = 0
  linarith

/-- A cotangent prefix reflected around a full period has the same value.
Source: focused reroutes, the finite identity `C_(N+r)=C_(N−r)`. -/
theorem rootCotangentPrefix_reflect {N r : ℕ} (hN : 0 < N) (hr : r ≤ 2 * N) :
    rootCotangentPrefix N (2 * N - r) = rootCotangentPrefix N r := by
  let f := fun j : ℕ => Real.cot (((j : ℝ) + 1 / 2) * π / (2 * N))
  have hsum := sum_Ico_reflect f 0 (m := r) (n := 2 * N - 1) (by omega)
  simp only [Nat.Ico_zero_eq_range, show 2 * N - 1 + 1 = 2 * N by omega, Nat.sub_zero] at hsum
  have heq : (∑ j ∈ range r, f (2 * N - 1 - j)) = -rootCotangentPrefix N r := by
    change (∑ j ∈ range r, f (2 * N - 1 - j)) = -∑ j ∈ range r, f j
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    exact cot_half_index_reflect hN ((mem_range.mp hj).trans_le hr)
  rw [heq, sum_Ico_eq_sub f (Nat.sub_le _ _)] at hsum
  change -rootCotangentPrefix N r = rootCotangentPrefix N (2 * N) - rootCotangentPrefix N (2 * N - r) at hsum
  rw [rootCotangentPrefix_two_mul_eq_zero hN] at hsum
  linarith

/-- Reflection of an interior sample index preserves its cotangent-prefix expression.
Source: focused reroutes, root-grid sample reflection. -/
theorem rootCotangentSample_reflect {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    rootCotangentSample N (N - k) = rootCotangentSample N k := by
  unfold rootCotangentSample
  rw [Nat.sub_sub_self hk, Nat.mul_sub_left_distrib,
    rootCotangentPrefix_reflect hN (Nat.mul_le_mul_left 2 hk)]
  ring

/-- Prefix values change by the next half-index cotangent.
Source: the defining finite prefix sum. -/
theorem rootCotangentPrefix_succ (N r : ℕ) :
    rootCotangentPrefix N (r + 1) = rootCotangentPrefix N r +
      Real.cot (((r : ℝ) + 1 / 2) * π / (2 * N)) := by
  exact sum_range_succ _ _

/-- Adjacent sample expressions have the finite midpoint-convexity difference.
Source: focused reroutes, the difference after equation `polyretry:sample-C`. -/
theorem rootCotangentSample_sub_succ {N k : ℕ} (hN : 0 < N) (hk : k < N / 2) :
    (N : ℝ) * (rootCotangentSample N (k + 1) - rootCotangentSample N k) =
      2 * Real.cot (((2 * k : ℕ) + 1 : ℝ) * π / (2 * N)) -
        Real.cot ((((2 * k : ℕ) : ℝ) + 1 / 2) * π / (2 * N)) -
        Real.cot ((((2 * k + 1 : ℕ) : ℝ) + 1 / 2) * π / (2 * N)) := by
  have hkN : k + 1 ≤ N := by omega
  have hkNR : (k : ℝ) + 1 ≤ N := by exact_mod_cast hkN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let u := ((k : ℝ) + 1 / 2) * π / (2 * N)
  have hu : 0 < u := by dsimp [u]; positivity
  have huπ : u < π / 2 := by dsimp [u]; rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
  have href : Real.cot ((((N - (k + 1) : ℕ) : ℝ) + 1 / 2) * π / (2 * N)) = tan u := by
    have heq : (((N - (k + 1) : ℕ) : ℝ) + 1 / 2) * π / (2 * N) = π / 2 - u := by
      rw [Nat.cast_sub hkN]
      push_cast
      dsimp [u]
      field_simp
      ring
    rw [heq, cot_pi_div_two_sub]
  have hpair := cot_sub_tan_eq_two_mul_cot_two_mul hu huπ
  unfold rootCotangentSample
  rw [show N - k = (N - (k + 1)) + 1 by omega, rootCotangentPrefix_succ,
    rootCotangentPrefix_succ, show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
    rootCotangentPrefix_succ, rootCotangentPrefix_succ, href]
  dsimp [u] at hpair
  have harg : 2 * (((k : ℝ) + 1 / 2) * π / (2 * N)) = ((2 * k : ℕ) + 1 : ℝ) * π / (2 * N) := by push_cast; ring
  rw [harg] at hpair
  rw [mul_sub, mul_div_cancel₀ _ hNR.ne', mul_div_cancel₀ _ hNR.ne']
  linear_combination hpair

/-- An adjacent root sample does not increase on the first half of the grid.
Source: focused reroutes, cotangent midpoint convexity. -/
theorem rootCotangentSample_succ_le {N k : ℕ} (hN : 0 < N) (hk : k < N / 2) :
    rootCotangentSample N (k + 1) ≤ rootCotangentSample N k := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hkR : 2 * (k : ℝ) + 2 ≤ N := by exact_mod_cast (show 2 * k + 2 ≤ N by omega)
  let a := (2 * (k : ℝ) + 1 / 2) * π / (2 * N)
  let b := (2 * (k : ℝ) + 3 / 2) * π / (2 * N)
  have ha : a ∈ Ioc 0 (π / 2) := by
    dsimp [a]
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [pi_pos]
  have hb : b ∈ Ioc 0 (π / 2) := by
    dsimp [b]
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [pi_pos]
  have hconv := convexOn_cot.2 ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hmid : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b = (2 * (k : ℝ) + 1) * π / (2 * N) := by
    dsimp [a, b]
    ring
  rw [hmid] at hconv
  simp only [smul_eq_mul] at hconv
  have hd := rootCotangentSample_sub_succ hN hk
  push_cast at hd
  have hbarg : (2 * (k : ℝ) + 1 + 1 / 2) * π / (2 * N) = b := by dsimp [b]; ring
  rw [hbarg] at hd
  change (N : ℝ) * (rootCotangentSample N (k + 1) - rootCotangentSample N k) =
    2 * Real.cot ((2 * (k : ℝ) + 1) * π / (2 * N)) - Real.cot a - Real.cot b at hd
  have hn : (N : ℝ) * (rootCotangentSample N (k + 1) - rootCotangentSample N k) ≤ 0 := by
    rw [hd]
    nlinarith
  have hs : rootCotangentSample N (k + 1) - rootCotangentSample N k ≤ 0 :=
    le_of_mul_le_mul_left (by simpa only [mul_zero] using hn) hNR
  exact sub_nonpos.mp hs

/-- The central cotangent-prefix sample is smallest among all interior indices.
Source: focused reroutes, sample symmetry and midpoint convexity. -/
theorem rootCotangentSample_center_le {N k : ℕ} (hN : 2 ≤ N) (hk0 : 1 ≤ k) (hkN : k < N) :
    rootCotangentSample N (N / 2) ≤ rootCotangentSample N k := by
  have hpos : 0 < N := by omega
  have hanti : AntitoneOn (rootCotangentSample N) (Set.Icc 1 (N / 2) : Set ℕ) := by
    apply antitoneOn_of_succ_le (ordConnected_Icc : (Set.Icc 1 (N / 2) : Set ℕ).OrdConnected)
    intro j hjmax hj hjs
    have hjupper := hjs.2
    change j + 1 ≤ N / 2 at hjupper
    exact rootCotangentSample_succ_le hpos (by omega)
  by_cases hk : k ≤ N / 2
  · exact hanti ⟨hk0, hk⟩ ⟨by omega, le_rfl⟩ hk
  · have hr0 : 1 ≤ N - k := by omega
    have hrN : N - k ≤ N / 2 := by omega
    have h := hanti ⟨hr0, hrN⟩ ⟨by omega, le_rfl⟩ hrN
    rw [rootCotangentSample_reflect hpos hkN.le] at h
    exact h

/-- Complementary half-index cotangents are tangent terms.
Source: focused reroutes, the finite central-sample identity. -/
theorem cot_half_index_complement {N j : ℕ} (hN : 0 < N) (hj : j < N) :
    Real.cot ((((N - 1 - j : ℕ) : ℝ) + 1 / 2) * π / (2 * N)) =
      tan (((j : ℝ) + 1 / 2) * π / (2 * N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (((N - 1 - j : ℕ) : ℝ) + 1 / 2) * π / (2 * N) =
      π / 2 - ((j : ℝ) + 1 / 2) * π / (2 * N) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  rw [heq, cot_pi_div_two_sub]

/-- The last `r` terms of a half-period prefix sum to its first `r` tangent terms.
Source: focused reroutes, finite cotangent-complement reflection. -/
theorem rootCotangentPrefix_sub_complement {N r : ℕ} (hN : 0 < N) (hr : r ≤ N) :
    rootCotangentPrefix N N - rootCotangentPrefix N (N - r) =
      ∑ j ∈ range r, tan (((j : ℝ) + 1 / 2) * π / (2 * N)) := by
  let f := fun j : ℕ => Real.cot (((j : ℝ) + 1 / 2) * π / (2 * N))
  have hsum := sum_Ico_reflect f 0 (m := r) (n := N - 1) (by omega)
  simp only [Nat.Ico_zero_eq_range, show N - 1 + 1 = N by omega, Nat.sub_zero] at hsum
  rw [sum_Ico_eq_sub f (Nat.sub_le _ _)] at hsum
  refine hsum.symm.trans ?_
  apply sum_congr rfl
  intro j hj
  exact cot_half_index_complement hN ((mem_range.mp hj).trans_le hr)

/-- The central cotangent-prefix sample has the finite double-angle sum and the
odd tangent correction. Source: focused reroutes, equation `polyretry:central-cot`. -/
theorem rootCotangentSample_center_eq {N : ℕ} (hN : 2 ≤ N) :
    rootCotangentSample N (N / 2) =
      (2 / (N : ℝ)) * ∑ j ∈ range (N / 2), Real.cot (((j : ℝ) + 1 / 2) * π / N) +
        (if Odd N then (1 / (N : ℝ)) * tan (π / (4 * N)) else 0) := by
  let m := N / 2
  have hpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hpos
  have hmN : m ≤ N := by dsimp [m]; omega
  have htail := rootCotangentPrefix_sub_complement hpos hmN
  have hpairs : rootCotangentPrefix N m - (∑ j ∈ range m, tan (((j : ℝ) + 1 / 2) * π / (2 * N))) =
      2 * ∑ j ∈ range m, Real.cot (((j : ℝ) + 1 / 2) * π / N) := by
    unfold rootCotangentPrefix
    rw [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjN : j + 1 ≤ N := by dsimp [m] at hj; have hj' := mem_range.mp hj; omega
    have hjNR : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
    have hu : 0 < ((j : ℝ) + 1 / 2) * π / (2 * N) := by positivity
    have huπ : ((j : ℝ) + 1 / 2) * π / (2 * N) < π / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [pi_pos]
    rw [cot_sub_tan_eq_two_mul_cot_two_mul hu huπ]
    congr 2
    ring
  have hlast : rootCotangentPrefix N N - rootCotangentPrefix N (2 * m) =
      if Odd N then tan (π / (4 * N)) else 0 := by
    by_cases hNO : Odd N
    · have hNm : N = 2 * m + 1 := by have ho := Nat.odd_iff.mp hNO; dsimp [m]; omega
      have hidx : 2 * m = N - 1 := by omega
      rw [hNm, rootCotangentPrefix_succ]
      rw [← hNm, hidx, add_sub_cancel_left, if_pos hNO]
      have href := cot_half_index_complement hpos (show 0 < N from hpos)
      simp only [Nat.sub_zero, Nat.cast_zero, zero_add] at href
      convert href using 1
      congr 1
      ring
    · have hNm : N = 2 * m := by have he := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hNO); dsimp [m]; omega
      rw [← hNm, sub_self, if_neg hNO]
  have hnum : rootCotangentPrefix N (N - m) + rootCotangentPrefix N m - rootCotangentPrefix N (2 * m) =
      2 * (∑ j ∈ range m, Real.cot (((j : ℝ) + 1 / 2) * π / N)) +
        (if Odd N then tan (π / (4 * N)) else 0) := by
    linarith
  change (rootCotangentPrefix N (N - m) + rootCotangentPrefix N m - rootCotangentPrefix N (2 * m)) / N = _
  rw [hnum, add_div]
  split_ifs <;> ring

end NLAlib
