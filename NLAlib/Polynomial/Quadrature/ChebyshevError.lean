import NLAlib.Polynomial.Quadrature.Basic
import NLAlib.Polynomial.Chebyshev.Integral
import NLAlib.Polynomial.Chebyshev.ChebyshevAliasing
import NLAlib.Polynomial.FunctionApproximation.AnalyticApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import NLAlib.ForMathlib.Analysis.EvenGeometricSeries

/-! # Chebyshev-coordinate quadrature errors

The actual integrated Clenshaw–Curtis interpolant folds frequencies, and the
Lebesgue moments give the scalar `32/15` error bound above the cutoff.
-/
noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory Finset Set
namespace NLAlib

/-- Frequency folding on the endpoint grid preserves parity.
Source: Trefethen, ATAP, aliasing identity used in Theorems 19.3–19.5. -/
theorem even_chebyshevAliasIndex_iff {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Even (chebyshevAliasIndex n k) ↔ Even k := by
  have hmod : (k % (2 * n)) % 2 = k % 2 := Nat.mod_mod_of_dvd k (by omega)
  have heven : Even (k % (2 * n)) ↔ Even k := by rw [Nat.even_iff, Nat.even_iff, hmod]
  have hlt : k % (2 * n) < 2 * n := Nat.mod_lt k (by omega)
  unfold chebyshevAliasIndex
  rcases le_or_gt (k % (2 * n)) n with h | h
  · rw [min_eq_left (by omega)]
    exact heven
  · rw [min_eq_right (by omega), Nat.even_sub hlt.le]
    simpa using heven

/-- Clenshaw–Curtis integrates a Chebyshev frequency to the moment of its folded
frequency. Source: Trefethen, ATAP, Chapter 19, finite aliasing proof.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem clenshawCurtisRule_eval_T {n : ℕ} (hn : 0 < n) (k : ℕ) :
    clenshawCurtisRule n (T ℝ k).eval = chebyshevMoment (chebyshevAliasIndex n k) := by
  rw [clenshawCurtisRule]
  have h := interpolate_eval_T_node_eq_T_alias hn k
  change (∫ x in (-1 : ℝ)..1, (Lagrange.interpolate (range (n + 1)) (node n)
    (fun j => (T ℝ k).eval (node n j))).eval x) = _
  rw [h, integral_eval_T]
  rfl

/-- Every Lebesgue Chebyshev moment has absolute value at most two.
Source: Trefethen, ATAP, Theorem 19.2; quadrature-error helper. -/
theorem abs_chebyshevMoment_le_two (k : ℕ) : |chebyshevMoment k| ≤ 2 := by
  unfold chebyshevMoment
  by_cases hk : Even k
  · rw [if_pos hk]
    by_cases hk0 : k = 0
    · subst k
      norm_num
    have hk2 : 2 ≤ k := by have h := Nat.one_lt_of_ne_zero_of_even hk0 hk; omega
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hden : 1 - (k : ℝ) ^ 2 ≤ 0 := by nlinarith
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonpos hden]
    apply (div_le_iff₀ (by nlinarith : 0 < -(1 - (k : ℝ) ^ 2))).mpr
    nlinarith
  · simp [hk]

/-- Starting at degree four, the Lebesgue moments are at most `2/15` in modulus.
Source: Trefethen, ATAP, Theorems 19.3–19.4, sharp scalar-moment estimate. -/
theorem abs_chebyshevMoment_le_two_div_fifteen {k : ℕ} (hk : 4 ≤ k) :
    |chebyshevMoment k| ≤ 2 / 15 := by
  unfold chebyshevMoment
  split_ifs
  · have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hden : 1 - (k : ℝ) ^ 2 ≤ 0 := by nlinarith
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonpos hden]
    apply (div_le_iff₀ (by nlinarith : 0 < -(1 - (k : ℝ) ^ 2))).mpr
    nlinarith
  · norm_num

/-- All odd Chebyshev frequencies have zero Clenshaw–Curtis error.
Source: Trefethen, ATAP, Theorems 19.3–19.4; parity-preserving aliasing.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem integral_eval_T_sub_clenshawCurtisRule_eq_zero_of_odd {n k : ℕ}
    (hn : 0 < n) (hk : Odd k) :
    (∫ x in (-1 : ℝ)..1, (T ℝ k).eval x) - clenshawCurtisRule n (T ℝ k).eval = 0 := by
  have hke : ¬ Even k := by rw [Nat.even_iff]; obtain ⟨j, rfl⟩ := hk; omega
  rw [integral_eval_T, clenshawCurtisRule_eval_T hn, chebyshevMoment,
    if_neg hke, if_neg (fun h => hke ((even_chebyshevAliasIndex_iff hn k).mp h)), sub_self]

/-- Above an endpoint-grid cutoff at least two, a single even Chebyshev frequency
has Clenshaw–Curtis error at most `32/15`. Source: Trefethen, ATAP, Theorem 19.3.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_eval_T_sub_clenshawCurtisRule_le {n k : ℕ}
    (hn : 2 ≤ n) (hk : n < k) (hke : Even k) :
    |(∫ x in (-1 : ℝ)..1, (T ℝ k).eval x) - clenshawCurtisRule n (T ℝ k).eval| ≤ 32 / 15 := by
  have hk4 : 4 ≤ k := by
    have he := Nat.even_iff.mp hke
    omega
  rw [clenshawCurtisRule_eval_T (by omega), integral_eval_T]
  change |chebyshevMoment k - chebyshevMoment (chebyshevAliasIndex n k)| ≤ _
  have h := abs_sub (chebyshevMoment k) (chebyshevMoment (chebyshevAliasIndex n k))
  have h1 := abs_chebyshevMoment_le_two_div_fifteen hk4
  have h2 := abs_chebyshevMoment_le_two (chebyshevAliasIndex n k)
  linarith

/-- An absolutely convergent Chebyshev expansion integrates term by term against
Lebesgue measure. Source: Trefethen, ATAP, Theorem 19.2 and dominated convergence.
This general coefficient form is used by the sharp quadrature tail bounds. -/
theorem hasSum_mul_chebyshevMoment_of_hasSum {c : ℕ → ℝ} {f : ℝ → ℝ}
    (hs : Summable (fun k => |c k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k => c k * (T ℝ k).eval x) (f x)) :
    HasSum (fun k => c k * chebyshevMoment k) (∫ x in (-1 : ℝ)..1, f x) := by
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (-1 : ℝ)) (b := 1) (μ := volume)
    (F := fun k x => c k * (T ℝ k).eval x) (f := f) (fun k _ => |c k|)
    (fun k => (continuous_const.mul (T ℝ k).continuous).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall (fun x hx => by
      have hI : x ∈ Icc (-1 : ℝ) 1 := by
        have hxI : x ∈ Set.Ioc (-1 : ℝ) 1 := by simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
        exact Set.Ioc_subset_Icc_self hxI
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_eval_T_real_le_one _ (abs_le.mpr hI))))
    (Filter.Eventually.of_forall (fun x hx => hs))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun x hx => hf x (by
      have hxI : x ∈ Set.Ioc (-1 : ℝ) 1 := by simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
      exact Set.Ioc_subset_Icc_self hxI)))
  simpa only [intervalIntegral.integral_const_mul, integral_eval_T, chebyshevMoment] using h

/-- Integrating the actual endpoint-grid interpolant term by term gives the folded
moment series. Source: Trefethen, ATAP, Chapter 19; finite interpolation and aliasing. -/
theorem hasSum_mul_chebyshevMoment_alias_of_hasSum {c : ℕ → ℝ} {f : ℝ → ℝ}
    (hs : Summable (fun k => |c k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k => c k * (T ℝ k).eval x) (f x))
    {n : ℕ} (hn : 0 < n) :
    HasSum (fun k => c k * chebyshevMoment (chebyshevAliasIndex n k)) (clenshawCurtisRule n f) := by
  let P := Lagrange.interpolate (range (n + 1)) (node n) (f ∘ node n)
  have hP (x : ℝ) : HasSum (fun k => c k * (T ℝ (chebyshevAliasIndex n k)).eval x) (P.eval x) := by
    have hj : ∀ j ∈ range (n + 1), HasSum (fun k =>
        c k * (T ℝ k).eval (node n j) * (Lagrange.basis (range (n + 1)) (node n) j).eval x)
      (f (node n j) * (Lagrange.basis (range (n + 1)) (node n) j).eval x) := by
      intro j hj
      exact (hf (node n j) node_mem_Icc).mul_right _
    have hsum := hasSum_sum hj
    convert hsum using 1
    · funext k
      rw [← interpolate_eval_T_node_eq_T_alias hn k]
      simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    · simp only [P, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, Function.comp_apply]
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (-1 : ℝ)) (b := 1) (μ := volume)
    (F := fun k x => c k * (T ℝ (chebyshevAliasIndex n k)).eval x) (f := P.eval) (fun k _ => |c k|)
    (fun k => (continuous_const.mul (T ℝ (chebyshevAliasIndex n k)).continuous).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall (fun x hx => by
      have hI : x ∈ Icc (-1 : ℝ) 1 := by
        have hxI : x ∈ Set.Ioc (-1 : ℝ) 1 := by simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
        exact Set.Ioc_subset_Icc_self hxI
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_eval_T_real_le_one _ (abs_le.mpr hI))))
    (Filter.Eventually.of_forall (fun x hx => hs))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun x hx => hP x))
  simpa only [intervalIntegral.integral_const_mul, integral_eval_T, chebyshevMoment,
    clenshawCurtisRule, P] using h

/-- Clenshaw–Curtis error is bounded by `32/15` times the absolute even Chebyshev
coefficient tail beyond the grid cutoff. Source: Trefethen, ATAP, Theorem 19.3;
finite aliasing plus the exact Lebesgue moments.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_sub_clenshawCurtisRule_le_even_tail {c : ℕ → ℝ} {f : ℝ → ℝ}
    (hs : Summable (fun k => |c k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k => c k * (T ℝ k).eval x) (f x))
    {n : ℕ} (hn : 2 ≤ n) :
    |(∫ x in (-1 : ℝ)..1, f x) - clenshawCurtisRule n f| ≤
      (32 / 15 : ℝ) * ∑' k, if n < k ∧ Even k then |c k| else 0 := by
  let u := fun k => c k * (chebyshevMoment k - chebyshevMoment (chebyshevAliasIndex n k))
  let tail := fun k => if n < k ∧ Even k then |c k| else 0
  have he : HasSum u ((∫ x in (-1 : ℝ)..1, f x) - clenshawCurtisRule n f) := by
    have h := (hasSum_mul_chebyshevMoment_of_hasSum hs hf).sub
      (hasSum_mul_chebyshevMoment_alias_of_hasSum hs hf (by omega : 0 < n))
    convert h using 1 <;> try rfl
    funext k
    dsimp [u]
    ring
  have ht : Summable tail := hs.of_nonneg_of_le (by intro k; dsimp [tail]; split_ifs <;> positivity)
    (by intro k; dsimp [tail]; split_ifs <;> simp)
  have hb (k : ℕ) : ‖u k‖ ≤ (32 / 15 : ℝ) * tail k := by
    by_cases hkn : n < k
    · by_cases hk : Even k
      · dsimp [u, tail]
        rw [if_pos ⟨hkn, hk⟩, abs_mul]
        have h := abs_integral_eval_T_sub_clenshawCurtisRule_le hn hkn hk
        rw [clenshawCurtisRule_eval_T (by omega), integral_eval_T] at h
        change |chebyshevMoment k - chebyshevMoment (chebyshevAliasIndex n k)| ≤ 32 / 15 at h
        calc |c k| * |chebyshevMoment k - chebyshevMoment (chebyshevAliasIndex n k)| ≤
            |c k| * (32 / 15) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
          _ = _ := mul_comm _ _
      · have hka : ¬ Even (chebyshevAliasIndex n k) :=
          fun h => hk ((even_chebyshevAliasIndex_iff (by omega) k).mp h)
        simp [u, tail, chebyshevMoment, hk, hka]
    · have halias : chebyshevAliasIndex n k = k := by
        unfold chebyshevAliasIndex
        rw [Nat.mod_eq_of_lt (by omega), min_eq_left (by omega)]
      simp [u, tail, hkn, halias]
  have hnorm : Summable (fun k => ‖u k‖) := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb
    (ht.mul_left (32 / 15 : ℝ))
  have hnormle := norm_tsum_le_tsum_norm hnorm
  rw [he.tsum_eq, Real.norm_eq_abs] at hnormle
  refine hnormle.trans ?_
  calc (∑' k, ‖u k‖) ≤ ∑' k, (32 / 15 : ℝ) * tail k :=
      Summable.tsum_le_tsum hb hnorm (ht.mul_left (32 / 15 : ℝ))
    _ = _ := by rw [tsum_mul_left]

/-- Geometric Chebyshev coefficient decay gives the sharp analytic Clenshaw–Curtis
constant. Source: Trefethen, ATAP, Theorem 19.3. The hypotheses describe an actual
absolutely convergent expansion; open-ellipse holomorphy supplies these hypotheses.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_sub_clenshawCurtisRule_le_geometric {c : ℕ → ℝ} {f : ℝ → ℝ}
    (hs : Summable (fun k => |c k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k => c k * (T ℝ k).eval x) (f x))
    {q M : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hM : 0 ≤ M)
    (hc : ∀ k, 0 < k → |c k| ≤ 2 * M * q ^ k) {n : ℕ} (hn : 2 ≤ n) :
    |(∫ x in (-1 : ℝ)..1, f x) - clenshawCurtisRule n f| ≤
      (64 / 15 : ℝ) * M * q ^ (n + 1) / (1 - q ^ 2) := by
  have htail := tsum_even_abs_tail_le_of_geometric hs hq0 hq1 hM hc n
  refine (abs_integral_sub_clenshawCurtisRule_le_even_tail hs hf hn).trans ?_
  have h := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 32 / 15)
  convert h using 1
  ring
/-- The actual Clenshaw–Curtis rule has error at most
`(64/15)Mρ^(1−n)/(ρ²−1)` under open-ellipse holomorphy and boundedness.
Source: Trefethen, ATAP, Theorem 19.3. No continuity on the ellipse boundary is required.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_re_sub_clenshawCurtisRule_le_of_open_ellipse
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) {n : ℕ} (hn : 2 ≤ n) :
    |(∫ x in (-1 : ℝ)..1, (F x).re) - clenshawCurtisRule n (fun x => (F x).re)| ≤
      (64 / 15 : ℝ) * M / (ρ ^ (n - 1) * (ρ ^ 2 - 1)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans
    (abs_chebyshevAnalyticCoeff_zero_le_of_open_ellipse hρ hFd hM)
  have hρ0 : 0 < ρ := by linarith
  have hq0 : 0 < ρ⁻¹ := inv_pos.mpr hρ0
  have hq1 : ρ⁻¹ < 1 := (inv_lt_one₀ hρ0).mpr hρ
  have hc (k : ℕ) (hk : 0 < k) : |chebyshevAnalyticCoeff F k| ≤ 2 * M * (ρ⁻¹) ^ k := by
    have h := abs_chebyshevAnalyticCoeff_le_of_open_ellipse hρ hFd hM hk
    simpa only [div_eq_mul_inv, inv_pow] using h
  have hs : Summable (fun k => |chebyshevAnalyticCoeff F k|) := by
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) ?_
      ((summable_geometric_of_lt_one hq0.le hq1).mul_left (2 * M))
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h := abs_chebyshevAnalyticCoeff_zero_le_of_open_ellipse hρ hFd hM
      simpa only [pow_zero, mul_one] using h.trans (by linarith : M ≤ 2 * M)
    · exact hc k hk
  have h := abs_integral_sub_clenshawCurtisRule_le_geometric hs
    (fun x hx => hasSum_chebyshevAnalyticCoeff_mul_eval_T_of_open_ellipse hρ hFd hM hx)
    hq0 hq1 hM0 hc hn
  have hpow : n + 1 = (n - 1) + 2 := by omega
  have heq : (64 / 15 : ℝ) * M * (ρ⁻¹) ^ (n + 1) / (1 - (ρ⁻¹) ^ 2) =
      (64 / 15 : ℝ) * M / (ρ ^ (n - 1) * (ρ ^ 2 - 1)) := by
    rw [hpow, pow_add]
    simp only [inv_pow]
    have hsq : ρ ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp [ne_of_gt hρ0, hsq]
  exact h.trans_eq heq

end NLAlib
