import NLAlib.Polynomial.Quadrature.EndpointMeasureRemainder

/-! # The derivative signs of Radau and Lobatto bounds

For a nonnegative odd derivative, the left Radau rule is a lower bound and the right
Radau rule is an upper bound. A nonnegative even derivative gives a Lobatto upper bound.
The conclusions follow from the signed nodal factors in the integral remainders.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- A nonnegative derivative of order `2q+1` gives a left Radau lower bound.
Source: Gautschi (2004), Theorems 3.3 and 3.7; operator derivations (AQ9).
atlas: gauss-radau-lobatto (partial) -/
theorem endpoint_quadrature_le_integral_of_iteratedDeriv_nonneg
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ}
    (v : Fin q → ℝ) (w : Fin (q + 1) → ℝ) (hv : Function.Injective v)
    (hva : ∀ i, v i ∈ Ioo a b)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (endpointNodeFamily a v i))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a b))
    (hDpos : ∀ x ∈ Ioo a b, 0 ≤ iteratedDeriv (2 * q + 1) f x) :
    ∑ i, w i * f (endpointNodeFamily a v i) ≤ ∫ x, f x ∂μ := by
  obtain ⟨ξ, hξ, he⟩ := exists_integral_sub_endpoint_quadrature_eq_iteratedDeriv_mul
    hab hμ (Or.inl rfl) v w hv hva hexact hf hf' hD
  have hW : 0 ≤ ∫ x, (x - a) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hμ] with x hx
    exact mul_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg _)
  have hE := mul_nonneg
    (div_nonneg (hDpos ξ hξ) (Nat.cast_nonneg (2 * q + 1).factorial)) hW
  rw [← he] at hE
  exact sub_nonneg.mp hE

/-- A nonnegative derivative of order `2q+1` gives a right Radau upper bound.
Source: Gautschi (2004), Theorems 3.3 and 3.7; operator derivations (AQ10).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_le_endpoint_quadrature_of_iteratedDeriv_nonneg
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ}
    (v : Fin q → ℝ) (w : Fin (q + 1) → ℝ) (hv : Function.Injective v)
    (hva : ∀ i, v i ∈ Ioo a b)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (endpointNodeFamily b v i))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a b))
    (hDpos : ∀ x ∈ Ioo a b, 0 ≤ iteratedDeriv (2 * q + 1) f x) :
    (∫ x, f x ∂μ) ≤ ∑ i, w i * f (endpointNodeFamily b v i) := by
  obtain ⟨ξ, hξ, he⟩ := exists_integral_sub_endpoint_quadrature_eq_iteratedDeriv_mul
    hab hμ (Or.inr rfl) v w hv hva hexact hf hf' hD
  have hW : (∫ x, (x - b) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hμ] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _)
  have hE := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (hDpos ξ hξ) (Nat.cast_nonneg (2 * q + 1).factorial)) hW
  rw [← he] at hE
  exact sub_nonpos.mp hE

/-- A nonnegative derivative of order `2q+2` gives a Lobatto upper bound.
Source: Gautschi (2004), Theorem 3.7; operator derivations (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_le_twoEndpoint_quadrature_of_iteratedDeriv_nonneg
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ}
    (v : Fin q → ℝ) (w : Fin (q + 2) → ℝ) (hv : Function.Injective v)
    (hva : ∀ i, v i ∈ Ioo a b)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 2 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (twoEndpointNodeFamily a b v i))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 2, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 2) f) (Ioo a b))
    (hDpos : ∀ x ∈ Ioo a b, 0 ≤ iteratedDeriv (2 * q + 2) f x) :
    (∫ x, f x ∂μ) ≤ ∑ i, w i * f (twoEndpointNodeFamily a b v i) := by
  obtain ⟨ξ, hξ, he⟩ := exists_integral_sub_twoEndpoint_quadrature_eq_iteratedDeriv_mul
    hab hμ v w hv hva hexact hf hf' hD
  have hW : (∫ x, (x - a) * (x - b) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hμ] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2)) (sq_nonneg _)
  have hE := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (hDpos ξ hξ) (Nat.cast_nonneg (2 * q + 2).factorial)) hW
  rw [← he] at hE
  exact sub_nonpos.mp hE

end NLAlib
