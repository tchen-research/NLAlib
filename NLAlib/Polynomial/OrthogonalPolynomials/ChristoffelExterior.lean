import NLAlib.Polynomial.OrthogonalPolynomials.ChristoffelKernel
import NLAlib.Polynomial.OrthogonalPolynomials.JacobiLocation

/-!
# Real nonvanishing for Christoffel kernel polynomials

The real diagonal reproducing kernel is strictly positive. Thus a real
Christoffel quotient cannot vanish at its modification point whenever its
original denominator is nonzero. Exterior support intervals supply that
denominator condition, including terminal atomic polynomials.
Source: Gautschi (2004), Lemma 1.56; operator re-derivations AQ12–AQ15.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set
namespace NLAlib

/-- A canonical monic measure polynomial is nonzero at every real point
strictly outside a closed support interval, including finite-support termination.
Source: Gautschi (2004), real zero location and Lemma 1.56.
atlas: kernel-polynomials-christoffel (partial) -/
theorem eval_monicOrthogonalPolynomial_ne_zero_of_outside_support_interval
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b z : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    (hz : z < a ∨ b < z) :
    (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).eval z ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn z).mp hzero
  have hloc := gaussNodes_mem_Icc hμ hs hn i
  rw [hi] at hloc
  rcases hz with hz | hz <;> linarith [hloc.1, hloc.2]

/-- The real diagonal reproducing kernel is strictly positive whenever its
included squared norms are positive. The constant summand proves strictness,
independently of whether higher polynomials vanish at the evaluation point. -/
theorem eval_monicOrthogonalKernelPolynomial_self_pos
    (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ)
    (hh : ∀ k ≤ n, 0 < orthogonalPolynomialNorm L k) (z : ℝ) :
    0 < (monicOrthogonalKernelPolynomial L (n+1) z).eval z := by
  simp only [monicOrthogonalKernelPolynomial, eval_finsetSum, eval_mul, eval_C]
  have hterm (k : ℕ) (hk : k ∈ range (n+1)) :
      0 ≤ (monicOrthogonalPolynomial L k).eval z / orthogonalPolynomialNorm L k *
        (monicOrthogonalPolynomial L k).eval z := by
    have hkn : k ≤ n := by have := mem_range.mp hk; omega
    rw [div_mul_eq_mul_div, ← pow_two]
    exact div_nonneg (sq_nonneg _) (hh k hkn).le
  have hzero : 0 < (monicOrthogonalPolynomial L 0).eval z / orthogonalPolynomialNorm L 0 *
      (monicOrthogonalPolynomial L 0).eval z := by
    simp only [monicOrthogonalPolynomial_zero, eval_one, mul_one]
    exact div_pos zero_lt_one (hh 0 (Nat.zero_le n))
  exact hzero.trans_le (single_le_sum hterm (by simp))

/-- For a positive real measure, a real Christoffel quotient does not vanish
at its modification point when its original degree-`n` value is nonzero.
The false arbitrary-complex nonvanishing assertion is not used.
Source: Gautschi (2004), Lemma 1.56, real reproducing-kernel proof.
atlas: kernel-polynomials-christoffel (partial) -/
theorem eval_christoffelPolynomial_ne_zero_of_real
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ}
    (hn : (n+1 : ℕ∞) ≤ μ.support.encard) {z : ℝ}
    (hz : (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).eval z ≠ 0) :
    (christoffelPolynomial (polynomialIntegral μ hμ) z n).eval z ≠ 0 := by
  have hL (k : ℕ) (hk : k ≤ n+1) : hankelMomentDet (polynomialIntegral μ hμ) k ≠ 0 :=
    hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hk : (k : ℕ∞) ≤ n+1).trans hn)
  have hh (k : ℕ) (hk : k ≤ n) : 0 < orthogonalPolynomialNorm (polynomialIntegral μ hμ) k :=
    orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
      ((by exact_mod_cast (show k+1 ≤ n+1 by omega) : (k+1:ℕ∞) ≤ n+1).trans hn)
  rw [christoffelPolynomial_eq_C_mul_monicOrthogonalKernelPolynomial _ n hL hz,
    eval_mul, eval_C]
  exact mul_ne_zero (div_ne_zero (hh n le_rfl).ne' hz)
    (eval_monicOrthogonalKernelPolynomial_self_pos _ n hh z).ne'

/-- Exterior real modification points make both the original denominator and
the transformed polynomial value nonzero. The limiting terminal modified
degree is allowed when the original support has exactly `n+1` points.
Source: Gautschi (2004), Lemma 1.56; corrected operator re-derivations.
atlas: kernel-polynomials-christoffel (partial) -/
theorem eval_christoffelPolynomial_ne_zero_of_outside_support_interval
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b z : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n+1 : ℕ∞) ≤ μ.support.encard)
    (hz : z < a ∨ b < z) :
    (christoffelPolynomial (polynomialIntegral μ hμ) z n).eval z ≠ 0 := by
  apply eval_christoffelPolynomial_ne_zero_of_real hμ hn
  exact eval_monicOrthogonalPolynomial_ne_zero_of_outside_support_interval hμ hs
    ((by exact_mod_cast Nat.le_succ n : (n:ℕ∞) ≤ n+1).trans hn) hz

end NLAlib
