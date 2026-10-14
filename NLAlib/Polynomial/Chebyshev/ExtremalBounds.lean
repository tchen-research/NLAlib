import NLAlib.Polynomial.BestApproximation.Minimax

/-!
# Absolute exterior derivative and leading-coefficient bounds

Apply Mathlib's one-sided extremal theorem to a polynomial and its negative,
and scale by the uniform bound. These are the remaining derivative and leading
coefficient clauses of `chebyshev-extremal`. Source: Rivlin (1990), §2.7.
-/

noncomputable section
open Polynomial Polynomial.Chebyshev
namespace NLAlib

/-- A uniformly unit-bounded polynomial's every exterior derivative is
dominated in absolute value by the corresponding Chebyshev derivative.
Source: Rivlin (1990), §2.7; Mathlib's one-sided extremal theorem.
atlas: chebyshev-extremal (partial) -/
theorem abs_eval_iterate_derivative_le_of_forall_abs_le_one {q k : ℕ}
    {p : ℝ[X]} {x : ℝ} (hdeg : p.degree ≤ q)
    (hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |p.eval t| ≤ 1) (hx : 1 ≤ x) :
    |(derivative^[k] p).eval x| ≤ (derivative^[k] (T ℝ q)).eval x := by
  have h1 := eval_iterate_derivative_le_of_forall_abs_le_one (k := k) hx hdeg hb
  have h2 := eval_iterate_derivative_le_of_forall_abs_le_one (k := k) (P := -p) hx
    (by simpa only [degree_neg] using hdeg) (fun t ht => by simpa using hb t ht)
  rw [iterate_derivative_neg, eval_neg] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- Scaling the uniform bound scales every absolute exterior derivative bound.
Zero uniform bound and derivative orders above the degree are included.
Source: Rivlin (1990), §2.7.
atlas: chebyshev-extremal (partial) -/
theorem abs_eval_iterate_derivative_le_mul_of_forall_abs_le {q k : ℕ}
    {p : ℝ[X]} {M x : ℝ} (hdeg : p.degree ≤ q)
    (hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |p.eval t| ≤ M) (hx : 1 ≤ x) :
    |(derivative^[k] p).eval x| ≤ M * (derivative^[k] (T ℝ q)).eval x := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb 0 ⟨by norm_num, by norm_num⟩)
  by_cases hM : M = 0
  · have hp := eq_zero_of_forall_abs_eval_le_of_nonpos (le_of_eq hM) hb
    simp [hp, hM]
  · have hMpos := lt_of_le_of_ne hM0 (Ne.symm hM)
    have hd : (C M⁻¹ * p).degree ≤ q := by
      exact ((congrArg degree (C_mul' _ _)).trans_le (degree_smul_le _ _)).trans hdeg
    have hnorm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(C M⁻¹ * p).eval t| ≤ 1 := by
      intro t ht
      rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hMpos),
        inv_mul_le_iff₀ hMpos, mul_one]
      exact hb t ht
    have h := abs_eval_iterate_derivative_le_of_forall_abs_le_one (k := k) hd hnorm hx
    rw [iterate_derivative_C_mul, eval_mul, eval_C, abs_mul,
      abs_of_pos (inv_pos.mpr hMpos), inv_mul_le_iff₀ hMpos] at h
    exact h

/-- The leading coefficient's absolute value has the sharp degree-budget bound,
also at degree zero. Source: Rivlin (1990), §2.1; Mathlib's leading-coefficient theorem.
atlas: chebyshev-extremal (partial) -/
theorem abs_leadingCoeff_le_of_forall_abs_le_one {q : ℕ} {p : ℝ[X]}
    (hdeg : p.degree ≤ q) (hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |p.eval t| ≤ 1) :
    |p.leadingCoeff| ≤ (2 : ℝ) ^ (q - 1) := by
  have h1 := leadingCoeff_le_of_forall_abs_le_one hdeg hb
  have h2 := leadingCoeff_le_of_forall_abs_le_one (P := -p)
    (by simpa only [degree_neg] using hdeg) (fun t ht => by simpa using hb t ht)
  rw [leadingCoeff_neg] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- Scaling the uniform bound scales the sharp absolute leading-coefficient
bound, including degree zero and a zero uniform bound.
Source: Rivlin (1990), §2.1.
atlas: chebyshev-extremal (partial) -/
theorem abs_leadingCoeff_le_mul_of_forall_abs_le {q : ℕ} {p : ℝ[X]} {M : ℝ}
    (hdeg : p.degree ≤ q) (hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |p.eval t| ≤ M) :
    |p.leadingCoeff| ≤ M * (2 : ℝ) ^ (q - 1) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb 0 ⟨by norm_num, by norm_num⟩)
  by_cases hM : M = 0
  · have hp := eq_zero_of_forall_abs_eval_le_of_nonpos (le_of_eq hM) hb
    simp [hp, hM]
  · have hMpos := lt_of_le_of_ne hM0 (Ne.symm hM)
    have hd : (C M⁻¹ * p).degree ≤ q := by
      exact ((congrArg degree (C_mul' _ _)).trans_le (degree_smul_le _ _)).trans hdeg
    have hnorm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(C M⁻¹ * p).eval t| ≤ 1 := by
      intro t ht
      rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hMpos),
        inv_mul_le_iff₀ hMpos, mul_one]
      exact hb t ht
    have h := abs_leadingCoeff_le_of_forall_abs_le_one hd hnorm
    rw [leadingCoeff_mul, leadingCoeff_C, abs_mul,
      abs_of_pos (inv_pos.mpr hMpos), inv_mul_le_iff₀ hMpos] at h
    exact h

/-- The coefficient at the degree budget has the same sharp absolute bound;
when the polynomial's degree is smaller that coefficient is zero.
Source: Rivlin (1990), §2.1.
atlas: chebyshev-extremal (partial) -/
theorem abs_coeff_le_mul_of_forall_abs_le {q : ℕ} {p : ℝ[X]} {M : ℝ}
    (hdeg : p.degree ≤ q) (hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |p.eval t| ≤ M) :
    |p.coeff q| ≤ M * (2 : ℝ) ^ (q - 1) := by
  by_cases hq : p.natDegree = q
  · have h := abs_leadingCoeff_le_mul_of_forall_abs_le (q := q) hdeg hb
    simpa only [← hq, coeff_natDegree] using h
  · have hpq : p.natDegree < q := lt_of_le_of_ne (natDegree_le_iff_degree_le.mpr hdeg) hq
    rw [coeff_eq_zero_of_natDegree_lt hpq, abs_zero]
    exact mul_nonneg ((abs_nonneg _).trans (hb 0 ⟨by norm_num, by norm_num⟩)) (by positivity)

end NLAlib
