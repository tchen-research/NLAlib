import NLAlib.Polynomial.Quadrature.FoldedCoefficientBounds
import NLAlib.Polynomial.Quadrature.BvThreshold
import NLAlib.Polynomial.FunctionApproximation.ChebyshevDifferentiable

/-! # Explicit eventual Clenshaw–Curtis BV bound

Finite folded-moment blocks give the stronger inverse-power error rate, and
the finite-product BV envelope gives an explicit eventual threshold.
-/
noncomputable section
open Set MeasureTheory Polynomial Polynomial.Chebyshev Finset
namespace NLAlib

/-- An actual absolutely convergent Chebyshev expansion whose coefficients obey
`|c k|≤A/k^p` beyond the cutoff has Clenshaw–Curtis error at most `7A/n^p`.
Source: focused quadrature reroute, finite alias-block estimate. -/
theorem abs_integral_sub_clenshawCurtisRule_le_power_envelope
    {c : ℕ → ℝ} {f : ℝ → ℝ} (hcS : Summable (fun k => |c k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k => c k * (T ℝ k).eval x) (f x))
    {n p : ℕ} (hn : 2 ≤ n) (hp : 2 ≤ p) {A : ℝ} (hA : 0 ≤ A)
    (hc : ∀ k, n < k → |c k| ≤ A / (k : ℝ) ^ p) :
    |(∫ x in (-1 : ℝ)..1, f x) - clenshawCurtisRule n f| ≤ 7 * A / (n : ℝ) ^ p := by
  let u := fun k => c k * (chebyshevMoment k - chebyshevMoment (chebyshevAliasIndex n k))
  have he : HasSum u ((∫ x in (-1 : ℝ)..1, f x) - clenshawCurtisRule n f) := by
    have h := (hasSum_mul_chebyshevMoment_of_hasSum hcS hf).sub
      (hasSum_mul_chebyshevMoment_alias_of_hasSum hcS hf (by omega : 0 < n))
    convert h using 1 <;> try rfl
    funext k
    dsimp [u]
    ring
  have hu (k : ℕ) : ‖u k‖ ≤ 4 * |c k| := by
    rw [Real.norm_eq_abs, show u k = c k * (chebyshevMoment k - chebyshevMoment (chebyshevAliasIndex n k)) by rfl,
      abs_mul]
    have hdiff : |chebyshevMoment k - chebyshevMoment (chebyshevAliasIndex n k)| ≤ 4 := by
      have h := abs_sub (chebyshevMoment k) (chebyshevMoment (chebyshevAliasIndex n k))
      have h1 := abs_chebyshevMoment_le_two k
      have h2 := abs_chebyshevMoment_le_two (chebyshevAliasIndex n k)
      linarith
    have h := mul_le_mul_of_nonneg_left hdiff (abs_nonneg (c k))
    simpa only [mul_comm] using h
  have huS : Summable (fun k => ‖u k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hu (hcS.mul_left 4)
  have hinj : Function.Injective (fun j : ℕ => 2 * j) := by intro a b h; dsimp only at h; omega
  have hsup : Function.support (fun k => ‖u k‖) ⊆ Set.range (fun j : ℕ => 2 * j) := by
    intro k hk
    have hkE : Even k := by
      by_contra hkE
      have hka : ¬ Even (chebyshevAliasIndex n k) :=
        fun h => hkE ((even_chebyshevAliasIndex_iff (by omega) k).mp h)
      have hz : u k = 0 := by simp [u, chebyshevMoment, hkE, hka]
      exact hk (by simp [hz])
    obtain ⟨j, hj⟩ := hkE
    exact ⟨j, by dsimp only; omega⟩
  let a := fun j : ℕ => if n < 2 * j then |c (2 * j)| * |chebyshevMoment (2 * j)| else 0
  let b := fun j : ℕ => if n < 2 * j then
    |c (2 * j)| * |chebyshevMoment (chebyshevAliasIndex n (2 * j))| else 0
  have hs (v : ℕ → ℕ) (hv : Function.Injective v) (m : ℕ → ℝ) (hm : ∀ k, |m k| ≤ 2) :
      Summable (fun j => if n < v j then |c (v j)| * |m (v j)| else 0) := by
    refine Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) ?_
      ((hcS.comp_injective hv).mul_left 2)
    intro j
    split_ifs
    · have h := mul_le_mul_of_nonneg_left (hm (v j)) (abs_nonneg (c (v j)))
      simpa only [Function.comp_def, mul_comm] using h
    · dsimp only [Function.comp_def]; positivity
  have haS : Summable a := hs _ hinj chebyshevMoment abs_chebyshevMoment_le_two
  have hbS : Summable b := hs _ hinj (fun k => chebyshevMoment (chebyshevAliasIndex n k))
    (fun k => abs_chebyshevMoment_le_two _)
  have hbound (j : ℕ) : ‖u (2 * j)‖ ≤ a j + b j := by
    by_cases hk : n < 2 * j
    · dsimp [u, a, b]
      rw [if_pos hk, if_pos hk, abs_mul, ← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
    · have halias : chebyshevAliasIndex n (2 * j) = 2 * j := by
        unfold chebyshevAliasIndex
        rw [Nat.mod_eq_of_lt (by omega), min_eq_left (by omega)]
      simp [u, a, b, hk, halias]
  have hsum := (huS.comp_injective hinj).tsum_le_tsum hbound (haS.add hbS)
  rw [haS.tsum_add hbS] at hsum
  have hnorm := norm_tsum_le_tsum_norm huS
  rw [he.tsum_eq, Real.norm_eq_abs, ← hinj.tsum_eq hsup] at hnorm
  have ha := tsum_abs_mul_chebyshevMoment_even_tail_le hcS (show 0 < n by omega) hA hc
  have hb := tsum_abs_mul_chebyshevMoment_alias_even_tail_le hcS hn hp hA hc
  exact (hnorm.trans hsum).trans ((add_le_add ha hb).trans_eq (by ring))

/-- Under the full AC/BV chain, Clenshaw–Curtis has the stronger finite-product
rate `14V/[π(1−ν(ν+1)/(2(n+1)))n^(ν+1)]`.
Source: focused quadrature reroute, explicit eventual-bound theorem. -/
theorem abs_integral_sub_clenshawCurtisRule_le_stronger_rate_of_bv
    {ν n : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hν : 0 < ν) (hnν : ν ≤ n) (hn2 : 2 ≤ n)
    (hs : (ν : ℝ) * (ν + 1) / 2 < n + 1)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    |(∫ x in (-1 : ℝ)..1, F 0 x) - clenshawCurtisRule n (F 0)| ≤
      14 * V / (Real.pi * (1 - ((ν : ℝ) * (ν + 1) / 2) / (n + 1)) * (n : ℝ) ^ (ν + 1)) := by
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg.trans hV
  have hd : 0 < 1 - ((ν : ℝ) * (ν + 1) / 2) / (n + 1) :=
    sub_pos.mpr ((div_lt_one (by positivity)).mpr hs)
  have hcS := summable_abs_chebyshevCoeff_of_bv hν hAC hderiv hBV hV
  have hf : ContinuousOn (F 0) (Icc (-1 : ℝ) 1) := by simpa using (hAC 0 hν).continuousOn
  have hc (k : ℕ) (hk : n < k) := abs_le_power_envelope_of_descFactorial hV0 hnν hk hs
    (abs_chebyshevCoeff_le_descFactorial hAC hderiv hBV hV (show ν + 1 ≤ k by omega))
  have h := abs_integral_sub_clenshawCurtisRule_le_power_envelope hcS
    (fun x hx => hasSum_chebyshevCoeff_mul_eval_T hf hcS hx) hn2 (show 2 ≤ ν + 1 by omega)
    (show 0 ≤ 2 * V / (Real.pi * (1 - ((ν : ℝ) * (ν + 1) / 2) / (n + 1))) by positivity) hc
  refine h.trans_eq ?_
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- At the explicit integer threshold, the actual Clenshaw–Curtis rule has the
corrected Gauss BV constant, including zero variation.
Source: Trefethen, ATAP, Theorem 19.5, official 2013-edition errata to (19.12), and focused
quadrature reroute, explicit eventual-bound theorem.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_sub_clenshawCurtisRule_le_eventual_of_bv
    {ν n : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hν : 0 < ν) (hn : quadratureBvThreshold ν ≤ n)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    |(∫ x in (-1 : ℝ)..1, F 0 x) - clenshawCurtisRule n (F 0)| ≤
      32 * V / (15 * Real.pi * ν * (2 * (n : ℝ) + 1 - ν) ^ ν) := by
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg.trans hV
  have hνR : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hp : (1 : ℝ) ≤ 2 ^ ν := one_le_pow₀ (by norm_num)
  have ht := mul_pow_le_sub_of_quadratureBvThreshold_le hn
  have hb : (105 / 16 : ℝ) ≤ (105 / 16 : ℝ) * ν * 2 ^ ν := by
    have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg ν : (0 : ℝ) ≤ ν)
    nlinarith
  have hn2 : 2 ≤ n := by
    have hs0 : 0 ≤ (ν : ℝ) * (ν + 1) / 2 := by positivity
    exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have hnν : ν ≤ n := by
    exact_mod_cast (show (ν : ℝ) ≤ n by nlinarith)
  have hs : (ν : ℝ) * (ν + 1) / 2 < n + 1 := by linarith
  exact (abs_integral_sub_clenshawCurtisRule_le_stronger_rate_of_bv hν hnν hn2 hs hAC hderiv hBV hV).trans
    (bv_stronger_rate_le_eventual_of_quadratureBvThreshold_le (by omega) hn hV0)

end NLAlib
