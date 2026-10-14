import NLAlib.Polynomial.Quadrature.RadauJacobiRemainder
import NLAlib.Polynomial.Quadrature.LobattoJacobiRemainder

/-! # Reversed derivative signs for the actual endpoint rules

Nonpositive odd derivatives give the left Radau upper and right Radau lower
bounds. Nonpositive even derivatives give the Lobatto lower bound. Together
with the nonnegative derivative bounds, this is the full sign orientation API.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset Set
open scoped Matrix

namespace NLAlib

/-- A nonpositive odd derivative makes the actual left Radau matrix rule an upper
bound, including terminal exactness. Source: Gautschi (2004), Theorem 3.7; (AQ9).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_le_mass_mul_cfc_leftRadauJacobiMatrix_of_iteratedDeriv_nonpos
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a c : ℝ}
    (hac : a < c) (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c))
    (hDneg : ∀ x ∈ Ioo a c, iteratedDeriv (2 * q + 1) f x ≤ 0) :
    (∫ x, f x ∂μ) ≤ (polynomialIntegral μ hμ) 1 *
      cfc f (leftRadauJacobiMatrix (polynomialIntegral μ hμ) q a) 0 0 := by
  obtain ⟨e, v, hv, hvi, hav, hev, ξ, hξ, herr⟩ :=
    exists_integral_sub_leftRadauJacobiRule_eq_iteratedDeriv_mul hμ hac hμac q hs hf hf' hD
  have hw : 0 ≤ ∫ x, (x - a) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hμac] with x hx
    exact mul_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg _)
  have hE := mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (hDneg ξ hξ) (Nat.cast_nonneg (2 * q + 1).factorial)) hw
  rw [← herr] at hE
  exact sub_nonpos.mp hE

/-- A nonpositive odd derivative makes the actual right Radau matrix rule a lower
bound, including terminal exactness. Source: Gautschi (2004), Theorem 3.7; (AQ10).
atlas: gauss-radau-lobatto (partial) -/
theorem mass_mul_cfc_rightRadauJacobiMatrix_le_integral_of_iteratedDeriv_nonpos
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a c : ℝ}
    (hac : a < c) (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c))
    (hDneg : ∀ x ∈ Ioo a c, iteratedDeriv (2 * q + 1) f x ≤ 0) :
    (polynomialIntegral μ hμ) 1 * cfc f (rightRadauJacobiMatrix (polynomialIntegral μ hμ) q c) 0 0 ≤
      ∫ x, f x ∂μ := by
  obtain ⟨e, v, hv, hvi, hcv, hev, ξ, hξ, herr⟩ :=
    exists_integral_sub_rightRadauJacobiRule_eq_iteratedDeriv_mul hμ hac hμac q hs hf hf' hD
  have hw : (∫ x, (x - c) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hμac] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _)
  have hE := mul_nonneg_of_nonpos_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (hDneg ξ hξ) (Nat.cast_nonneg (2 * q + 1).factorial)) hw
  rw [← herr] at hE
  exact sub_nonneg.mp hE

/-- A nonpositive even derivative makes the actual constructed Lobatto matrix
rule a lower bound. Source: Gautschi (2004), Theorem 3.7; (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem mass_mul_cfc_lobattoJacobiMatrix_le_integral_of_iteratedDeriv_nonpos
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a c : ℝ}
    (hac : a < c) (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (hJa : (orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) (q + 1) - a • 1).PosDef)
    (hJc : (c • 1 - orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) (q + 1)).PosDef)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 2, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 2) f) (Ioo a c))
    (hDneg : ∀ x ∈ Ioo a c, iteratedDeriv (2 * q + 2) f x ≤ 0) :
    (polynomialIntegral μ hμ) 1 * cfc f (lobattoJacobiMatrix (polynomialIntegral μ hμ) q a c) 0 0 ≤
      ∫ x, f x ∂μ := by
  obtain ⟨e, v, hv, hvi, hev, ξ, hξ, herr⟩ :=
    exists_integral_sub_lobattoJacobiRule_eq_iteratedDeriv_mul hμ hac hμac q hs hJa hJc hf hf' hD
  have hw : (∫ x, (x - a) * (x - c) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hμac] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2)) (sq_nonneg _)
  have hE := mul_nonneg_of_nonpos_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (hDneg ξ hξ) (Nat.cast_nonneg (2 * q + 2).factorial)) hw
  rw [← herr] at hE
  exact sub_nonneg.mp hE

end NLAlib
