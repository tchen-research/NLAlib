import NLAlib.Polynomial.EvenChebyshevFilter
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Logarithmic overlap and finite Lanczos filter means

The scalar argument is separate from the matrix spectral theorem. It keeps the
source's exact numerical constant and does not take an inverse Gaussian overlap
moment: the only overlap parameter is the logarithm of total energy divided by
one fixed top coordinate.
-/

noncomputable section
open Polynomial
namespace NLAlib

/-- Raising the even filter suppresses the part outside its transition interval.
Source: manuscript `rt:lanczos`, the large spectral-error terms. -/
theorem one_sub_mul_eval_evenChebyshevFilter_pow_sq_le {x : ℝ}
    (hx : x ∈ Set.Icc 0 1) (k : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (1 - x) * ((evenChebyshevFilter k).eval x ^ ℓ) ^ 2 ≤
      (2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) * ((evenChebyshevFilter k).eval x ^ ℓ) ^ 2 +
      (2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) * (1 / 2 : ℝ) ^ ℓ := by
  let C := ((2 * k + 1 : ℕ) : ℝ) ^ 2
  let u := (evenChebyshevFilter k).eval x ^ 2
  have hC : 0 < C := by dsimp only [C]; positivity
  have hu : 0 ≤ u := sq_nonneg _
  have hw : (1 - x) * u ≤ 1 / C := by
    simpa only [u, C, one_div] using one_sub_mul_eval_evenChebyshevFilter_sq_le hx k
  have he : ((evenChebyshevFilter k).eval x ^ ℓ) ^ 2 = u ^ ℓ := by
    dsimp only [u]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [he]
  change (1 - x) * u ^ ℓ ≤ 2 / C * u ^ ℓ + 2 / C * (1 / 2 : ℝ) ^ ℓ
  by_cases hs : 1 - x ≤ 2 / C
  · have ht := mul_le_mul_of_nonneg_right hs (pow_nonneg hu ℓ)
    have hz : 0 ≤ 2 / C * (1 / 2 : ℝ) ^ ℓ := by positivity
    linarith
  · have hs' : 0 < 1 - x := lt_trans (by positivity : (0 : ℝ) < 2 / C) (lt_of_not_ge hs)
    have huHalf : u ≤ (1 / 2 : ℝ) := by
      have ht := mul_le_mul_of_nonneg_right (le_of_not_ge hs) hu
      have hh : 2 / C * u ≤ 1 / C := ht.trans hw
      apply (mul_le_mul_iff_right₀ hC).mp
      have := mul_le_mul_of_nonneg_left hh hC.le
      field_simp [hC.ne'] at this ⊢
      linarith
    have hPow := pow_le_pow_left₀ hu huHalf (ℓ - 1)
    have hBound : (1 - x) * u ^ ℓ ≤ 2 / C * (1 / 2 : ℝ) ^ ℓ := by
      rw [show ℓ = 1 + (ℓ - 1) by omega, pow_add, pow_one, ← mul_assoc]
      have ht := mul_le_mul hw hPow (pow_nonneg hu _) (by positivity : (0 : ℝ) ≤ 1 / C)
      refine ht.trans_eq ?_
      rw [pow_add, pow_one]
      ring
    exact hBound.trans (le_add_of_nonneg_left (mul_nonneg (by positivity) (pow_nonneg hu ℓ)))

/-- Finite spectral filter means have relative error at most `4/(2k+1)^2`
once `ℓ log 2` dominates the logarithmic inverse top-coordinate overlap.
Source: manuscript `rt:lanczos`; no random variable or inverse-overlap expectation.
atlas: random-start-power (partial) -/
theorem one_sub_filter_mean_le_four_div_sq {ι : Type*} [Fintype ι]
    (d g : ι → ℝ) (i₀ : ι) (hd : ∀ i, d i ∈ Set.Icc 0 1) (hd₀ : d i₀ = 1)
    (hg : g i₀ ≠ 0) (k : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hLog : Real.log ((∑ i, g i ^ 2) / (g i₀) ^ 2) ≤ (ℓ : ℝ) * Real.log 2) :
    1 - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) /
      (∑ i, ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) ≤
        4 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  classical
  let D := ∑ i, ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2
  let G := ∑ i, g i ^ 2
  let H := (g i₀) ^ 2
  let δ := 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)
  have hH : 0 < H := sq_pos_of_ne_zero hg
  have hHD : H ≤ D := by
    have h := Finset.single_le_sum (f := fun i =>
      ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i₀)
    simpa only [hd₀, eval_evenChebyshevFilter_one, one_pow, one_mul] using h
  have hHG : H ≤ G := Finset.single_le_sum (fun i _ => sq_nonneg (g i)) (Finset.mem_univ i₀)
  have hD : 0 < D := hH.trans_le hHD
  have hG : 0 < G := hH.trans_le hHG
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hRatio : G / H ≤ (2 : ℝ) ^ ℓ := by
    apply (Real.log_le_log_iff (div_pos hG hH) (by positivity)).mp
    rw [Real.log_pow]
    exact hLog
  have hEnergy : (1 / 2 : ℝ) ^ ℓ * G ≤ H := by
    have ht := (div_le_iff₀ hH).mp hRatio
    have h2 : (2 : ℝ) ^ ℓ ≠ 0 := by positivity
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 ^ ℓ)).mp
    calc
      (2 : ℝ) ^ ℓ * ((1 / 2 : ℝ) ^ ℓ * G) = G := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
      _ ≤ (2 : ℝ) ^ ℓ * H := ht
  have hNum : D - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) ≤
      δ * D + δ * (1 / 2 : ℝ) ^ ℓ * G := by
    dsimp only [D, G]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right
      (one_sub_mul_eval_evenChebyshevFilter_pow_sq_le (hd i) k hℓ) (sq_nonneg (g i))
    dsimp only [δ]
    nlinarith
  have hNum' : D - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) ≤
      2 * δ * D := by
    have h1 := mul_le_mul_of_nonneg_left hEnergy hδ
    have h2 := mul_le_mul_of_nonneg_left hHD hδ
    nlinarith
  have hResult : 1 - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) / D ≤
      2 * δ := by
    rw [show 1 - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) / D =
      (D - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2)) / D by
        rw [sub_div, div_self hD.ne']]
    apply (div_le_iff₀ hD).mpr
    nlinarith [hNum']
  dsimp only [δ, D] at hResult
  convert hResult using 1
  ring

/-- There is a genuine degree-bounded polynomial whose finite Rayleigh mean has
the source's gap-free squared logarithmic rate. Source: manuscript `rt:lanczos`.
The polynomial may depend on the vector; no measurable choice is required.
atlas: random-start-power (partial) -/
theorem exists_polynomial_filter_mean_le_log_sq {ι : Type*} [Fintype ι]
    (d g : ι → ℝ) (i₀ : ι) (hd : ∀ i, d i ∈ Set.Icc 0 1) (hd₀ : d i₀ = 1)
    (hg : g i₀ ≠ 0) {q : ℕ} (hq : 2 ≤ q) :
    ∃ p : ℝ[X], p.natDegree ≤ q - 1 ∧ p.eval 1 = 1 ∧
      1 - (∑ i, d i * p.eval (d i) ^ 2 * g i ^ 2) /
        (∑ i, p.eval (d i) ^ 2 * g i ^ 2) ≤
          4 * (1 + Real.log ((∑ i, g i ^ 2) / (g i₀) ^ 2) / Real.log 2) ^ 2 /
            ((q - 1 : ℕ) : ℝ) ^ 2 := by
  classical
  let L := Real.log ((∑ i, g i ^ 2) / (g i₀) ^ 2)
  let ℓ := max 1 ⌈L / Real.log 2⌉₊
  let k := (q - 1) / ℓ
  have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hHead : 0 < (g i₀) ^ 2 := sq_pos_of_ne_zero hg
  have hEnergy : (g i₀) ^ 2 ≤ ∑ i, g i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
  have hL : 0 ≤ L := Real.log_nonneg ((le_div_iff₀ hHead).mpr (by simpa only [one_mul] using hEnergy))
  have hℓ : 1 ≤ ℓ := le_max_left _ _
  have hℓ0 : 0 < ℓ := by omega
  have hLog : L ≤ (ℓ : ℝ) * Real.log 2 := by
    have hc := Nat.le_ceil (L / Real.log 2)
    have hm : (⌈L / Real.log 2⌉₊ : ℝ) ≤ ℓ := by exact_mod_cast (le_max_right 1 _)
    exact (div_le_iff₀ hh).mp (hc.trans hm)
  have hℓUpper : (ℓ : ℝ) ≤ 1 + L / Real.log 2 := by
    dsimp only [ℓ]
    rw [Nat.cast_max]
    apply max_le
    · linarith [div_nonneg hL hh.le]
    · have h := Nat.ceil_lt_add_one (div_nonneg hL hh.le)
      linarith
  have hDegree : ℓ * k ≤ q - 1 := by
    dsimp only [k]
    exact Nat.mul_div_le _ _
  have hWidth : q - 1 ≤ ℓ * (2 * k + 1) := by
    have ht : q - 1 < (k + 1) * ℓ :=
      (Nat.div_lt_iff_lt_mul hℓ0).mp (Nat.lt_succ_self k)
    have hu : (k + 1) * ℓ ≤ (2 * k + 1) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
    exact ht.le.trans (hu.trans_eq (Nat.mul_comm _ _))
  let p := evenChebyshevFilter k ^ ℓ
  refine ⟨p, (natDegree_pow_le_of_le ℓ (natDegree_evenChebyshevFilter_le k)).trans hDegree,
    by simp only [p, eval_pow, eval_evenChebyshevFilter_one, one_pow], ?_⟩
  have h := one_sub_filter_mean_le_four_div_sq d g i₀ hd hd₀ hg k hℓ hLog
  simp only [p, eval_pow]
  refine h.trans ?_
  have hm : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q - 1)
  have hC : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hw : ((q - 1 : ℕ) : ℝ) ≤ (ℓ : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hWidth
  have hs := pow_le_pow_left₀ hm.le hw 2
  rw [mul_pow] at hs
  calc
    4 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * (ℓ : ℝ) ^ 2 / ((q - 1 : ℕ) : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hC) (sq_pos_of_pos hm)).mpr
      nlinarith
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_left₀ (Nat.cast_nonneg ℓ) hℓUpper 2

end NLAlib
