import NLAlib.Polynomial.Quadrature.GaussMeasure
import Mathlib.Analysis.Complex.Basic

/-! # Complex polynomial exactness of real Gauss rules

A real finite-moment rule extends to complex coefficients by integrating the
finite monomial expansion. This is bilinear scalar extension, with no
conjugation or complex measure.
-/

noncomputable section

open Polynomial MeasureTheory Finset

namespace NLAlib

/-- Finite real polynomial moments integrate complex polynomial evaluations
on the same real variable. -/
theorem HasPolynomialMoments.integrable_complex_eval {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (p : ℂ[X]) :
    Integrable (fun x : ℝ => p.eval (x : ℂ)) μ := by
  rw [p.as_sum_range' (p.natDegree + 1) (Nat.lt_succ_self _)]
  simp only [eval_finsetSum, eval_monomial]
  apply integrable_finsetSum
  intro i _
  have hm : Integrable (fun x : ℝ => (x : ℂ) ^ i) μ := by
    have h : Integrable (fun x : ℝ => ((x ^ i : ℝ) : ℂ)) μ :=
      ((hasPolynomialMoments_iff_integrable_pow μ).mp hμ i).ofReal
    simpa only [Complex.ofReal_pow] using h
  exact hm.const_mul _

/-- A real polynomial-exact rule is exact for the same degree range with
complex coefficients. -/
theorem integral_complex_eval_eq_sum_of_real_exact {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {ι : Type*} [Fintype ι] (v w : ι → ℝ) (m : ℕ)
    (hexact : ∀ p : ℝ[X], p.degree < m → (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i))
    {p : ℂ[X]} (hp : p.degree < m) :
    (∫ x : ℝ, p.eval (x : ℂ) ∂μ) = ∑ i, (w i : ℂ) * p.eval (v i : ℂ) := by
  let c : Fin m → ℂ := fun j => p.coeff j.val
  have heq : p = ∑ j : Fin m, monomial j.val (c j) := eq_sum_monomial_fin_of_degree_lt hp
  have hint (j : Fin m) : Integrable (fun x : ℝ => (x : ℂ) ^ j.val) μ := by
    have h : Integrable (fun x : ℝ => ((x ^ j.val : ℝ) : ℂ)) μ :=
      ((hasPolynomialMoments_iff_integrable_pow μ).mp hμ j.val).ofReal
    simpa only [Complex.ofReal_pow] using h
  have hmom (j : Fin m) : (∫ x : ℝ, (x : ℂ) ^ j.val ∂μ) =
      ∑ i, (w i : ℂ) * (v i : ℂ) ^ j.val := by
    have h := hexact (X ^ j.val) (by rw [degree_X_pow]; exact_mod_cast j.isLt)
    simp only [eval_pow, eval_X] at h
    have h' := congrArg Complex.ofReal h
    rw [← integral_complex_ofReal] at h'
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] using h'
  calc
    (∫ x : ℝ, p.eval (x : ℂ) ∂μ) = ∑ j : Fin m, c j * (∫ x : ℝ, (x : ℂ) ^ j.val ∂μ) := by
      rw [heq]
      simp only [eval_finsetSum, eval_monomial]
      rw [integral_finsetSum _ (fun j _ => (hint j).const_mul (c j))]
      simp only [integral_const_mul]
    _ = ∑ i, (w i : ℂ) * p.eval (v i : ℂ) := by
      simp only [hmom, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [heq]
      simp only [eval_finsetSum, eval_monomial, mul_sum]
      apply sum_congr rfl
      intro j _
      ring

/-- The actual real moment Gauss rule integrates every complex polynomial
below degree twice its node count. -/
theorem integral_complex_eval_eq_sum_gaussWeights_mul_eval {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {p : ℂ[X]} (hp : p.degree < (2 * n : ℕ)) :
    (∫ x : ℝ, p.eval (x : ℂ) ∂μ) =
      ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) * p.eval (gaussNodes μ hμ n i : ℂ) :=
  integral_complex_eval_eq_sum_of_real_exact hμ _ _ (2 * n)
    (fun _ hd => integral_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn hd) hp

end NLAlib
