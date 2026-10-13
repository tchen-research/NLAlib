import NLAlib.Polynomial.Chebyshev.Growth

/-!
# Even second-kind Chebyshev filters

The normalized even second-kind polynomial is contracted from the variable
`sqrt(x)` to a polynomial in `x`. Its weighted squared bound is the
deterministic filter used in the logarithmic random-start Lanczos argument.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- Even second-kind Chebyshev polynomials have no odd coefficients.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3; parity of `U_{2k}`. -/
theorem coeff_U_two_mul_eq_zero_of_not_two_dvd (k j : ℕ) (hj : ¬ 2 ∣ j) :
    (U ℝ (2 * k : ℕ)).coeff j = 0 := by
  have he : (U ℝ (2 * k : ℕ)).comp (-X) = U ℝ (2 * k : ℕ) := by
    apply Polynomial.funext
    intro x
    simp only [eval_comp, eval_neg, eval_X, U_eval_neg]
    have hEven : Even ((2 * k : ℕ) : ℤ) := by
      exact ⟨(k : ℤ), by push_cast; ring⟩
    rw [Int.negOnePow_even _ hEven]
    simp
  have hCoeff := congrArg (fun p : ℝ[X] => p.coeff j) he
  have hOdd : Odd j := Nat.not_even_iff_odd.mp (by
    simpa only [even_iff_two_dvd] using hj)
  rw [show (-X : ℝ[X]) = C (-1) * X by simp,
    comp_C_mul_X_coeff, hOdd.neg_one_pow] at hCoeff
  linarith

/-- Expanding the contracted even polynomial recovers the `U_{2k}`.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3; polynomiality in the squared variable. -/
theorem expand_contract_U_two_mul (k : ℕ) :
    expand ℝ 2 (contract 2 (U ℝ (2 * k : ℕ))) = U ℝ (2 * k : ℕ) := by
  ext j
  rw [coeff_expand (by norm_num : 0 < 2)]
  by_cases hj : 2 ∣ j
  · rw [if_pos hj, coeff_contract (by norm_num : (2 : ℕ) ≠ 0),
      Nat.div_mul_cancel hj]
  · rw [if_neg hj, coeff_U_two_mul_eq_zero_of_not_two_dvd k j hj]

/-- The source's filter `b_k(x)=U_{2k}(sqrt(x))/(2k+1)`, as a polynomial.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3. Helper for `random-start-power`. -/
def evenChebyshevFilter (k : ℕ) : ℝ[X] :=
  C (((2 * k + 1 : ℕ) : ℝ)⁻¹) * contract 2 (U ℝ (2 * k : ℕ))

/-- The even second-kind filter has degree at most `k`.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3 (the even Chebyshev filter). -/
theorem natDegree_evenChebyshevFilter_le (k : ℕ) :
    (evenChebyshevFilter k).natDegree ≤ k := by
  apply (natDegree_mul_le ..).trans
  simp only [natDegree_C, zero_add]
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  apply coeff_eq_zero_of_natDegree_lt
  rw [natDegree_U_natCast]
  omega

/-- Evaluation of the polynomial equals its square-root expression.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3; valid throughout the nonnegative axis. -/
theorem eval_evenChebyshevFilter {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (evenChebyshevFilter k).eval x =
      (U ℝ (2 * k : ℕ)).eval (Real.sqrt x) / ((2 * k + 1 : ℕ) : ℝ) := by
  have h := congrArg (fun p : ℝ[X] => p.eval (Real.sqrt x)) (expand_contract_U_two_mul k)
  rw [expand_eq_comp_X_pow, eval_comp, eval_pow, eval_X, Real.sq_sqrt hx] at h
  simp only [evenChebyshevFilter, eval_mul, eval_C]
  rw [h]
  ring

/-- The filter is normalized at the top of the spectral interval.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3 (the even Chebyshev filter). -/
theorem eval_evenChebyshevFilter_one (k : ℕ) : (evenChebyshevFilter k).eval 1 = 1 := by
  rw [eval_evenChebyshevFilter (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [Real.sqrt_one, U_eval_one]
  push_cast
  apply div_self
  positivity

/-- The even second-kind filter has absolute value at most one on `[0,1]`.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3 (the even Chebyshev filter). -/
theorem abs_eval_evenChebyshevFilter_le_one {x : ℝ} (hx : x ∈ Set.Icc 0 1) (k : ℕ) :
    |(evenChebyshevFilter k).eval x| ≤ 1 := by
  have hs : |Real.sqrt x| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg x)]
    exact (Real.sqrt_le_one).mpr hx.2
  have h := abs_eval_U_real_le hs (2 * k)
  rw [eval_evenChebyshevFilter hx.1, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ))]
  apply (div_le_one (by positivity : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ))).mpr
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The sine identity gives the weighted squared second-kind bound on `[-1,1]`.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3; `sin(θ) U_j(cos θ)=sin((j+1)θ)`. -/
theorem one_sub_sq_mul_eval_U_sq_le_one {x : ℝ} (hx : |x| ≤ 1) (j : ℕ) :
    (1 - x ^ 2) * (U ℝ j).eval x ^ 2 ≤ 1 := by
  have hx' := abs_le.mp hx
  have hc := Real.cos_arccos hx'.1 hx'.2
  have h := U_real_cos (Real.arccos x) (j : ℤ)
  rw [hc] at h
  have hsq := congrArg (fun y : ℝ => y ^ 2) h
  rw [mul_pow] at hsq
  have hTrig := Real.sin_sq_add_cos_sq (Real.arccos x)
  rw [hc] at hTrig
  have hSin := Real.sin_sq_le_one (((j : ℤ) + 1) * Real.arccos x)
  nlinarith

/-- The weighted square of the normalized polynomial is at most `(2k+1)⁻²`.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3 (the deterministic filter bound).
atlas: random-start-power (partial) -/
theorem one_sub_mul_eval_evenChebyshevFilter_sq_le {x : ℝ}
    (hx : x ∈ Set.Icc 0 1) (k : ℕ) :
    (1 - x) * (evenChebyshevFilter k).eval x ^ 2 ≤
      (((2 * k + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hs : |Real.sqrt x| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg x)]
    exact (Real.sqrt_le_one).mpr hx.2
  have h := one_sub_sq_mul_eval_U_sq_le_one hs (2 * k)
  rw [Real.sq_sqrt hx.1] at h
  rw [eval_evenChebyshevFilter hx.1, div_pow, ← mul_div_assoc]
  exact (div_le_div_of_nonneg_right h (sq_nonneg _)).trans_eq (one_div _)

/-! ### Powers of the even Chebyshev filter -/

/-- **Growth of a power of the even Chebyshev filter**: raising `evenChebyshevFilter k` to the
power `ℓ` suppresses `(1 − x)` outside its transition interval,
`(1 − x) f_k(x)^{2ℓ} ≤ (2/(2k+1)²) f_k(x)^{2ℓ} + (2/(2k+1)²) 2^{−ℓ}` on `[0, 1]`.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3. Helper for `random-start-power`
(random-start Lanczos). -/
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

end NLAlib
