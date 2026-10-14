import NLAlib.Polynomial.Quadrature.EndpointJacobiWeights
import NLAlib.Polynomial.Quadrature.EndpointRuleRemainder
import NLAlib.Matrix.Structured.JacobiBorderSpectrum

/-! # Derivative remainder of the actual Lobatto Schur matrix rule

The constructed matrix proves interval node location, both prescribed endpoint nodes,
and simplicity. Reindexing its actual spectral rule then applies the finite endpoint
Hermite integral remainder without assuming an endpoint rule or its exactness.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset Set
open scoped Matrix MatrixOrder

namespace NLAlib

/-- The actual Lobatto matrix constructed from the moment Jacobi block has the classical
single-interior-point derivative remainder. The positive definite endpoint shifts are
the exact border hypotheses; the moment system may terminate at its displayed order.
Source: focused mathematical reroutes, Section 3 (BL7)–(BL11); operator derivations (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_integral_sub_lobattoJacobiRule_eq_iteratedDeriv_mul
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a c : ℝ}
    (hac : a < c) (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (hJa : (orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) (q + 1) - a • 1).PosDef)
    (hJc : (c • 1 - orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) (q + 1)).PosDef)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 2, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 2) f) (Ioo a c)) :
    let L := polynomialIntegral μ hμ
    ∃ e : Equiv.Perm (Fin (q + 2)), ∃ v : Fin q → ℝ,
      Function.Injective v ∧ (∀ i, v i ∈ Ioo a c) ∧
        (∀ i, lobattoNodes L q a c (e i) = twoEndpointNodeFamily a c v i) ∧ ∃ ξ ∈ Ioo a c,
          (∫ x, f x ∂μ) - L 1 * cfc f (lobattoJacobiMatrix L q a c) 0 0 =
            iteratedDeriv (2 * q + 2) f ξ / (2 * q + 2).factorial *
              ∫ x, (x - a) * (x - c) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ := by
  dsimp only
  let L := polynomialIntegral μ hμ
  let J := orthogonalPolynomialJacobiMatrix L (q + 1)
  let e : Fin (q + 1) → ℝ := Pi.single (Fin.last q) 1
  have he : e ≠ 0 := by intro hz; have := congrFun hz (Fin.last q); simp [e] at this
  obtain ⟨ha, hc, hsa, hsc⟩ := finLobattoSchurBorder_bounds_and_endpoints hac hJa hJc he
  change a • 1 ≤ lobattoJacobiMatrix L q a c at ha
  change lobattoJacobiMatrix L q a c ≤ c • 1 at hc
  change a ∈ spectrum ℝ (lobattoJacobiMatrix L q a c) at hsa
  change c ∈ spectrum ℝ (lobattoJacobiMatrix L q a c) at hsc
  have hH := isHermitian_lobattoJacobiMatrix L q a c
  have hnode : ∀ i, lobattoNodes L q a c i ∈ Icc a c := hH.eigenvalues_mem_Icc_of_order ha hc
  have hna : a ∈ Set.range (lobattoNodes L q a c) := by
    simpa only [lobattoNodes, hH, hH.spectrum_real_eq_range_eigenvalues] using hsa
  have hnc : c ∈ Set.range (lobattoNodes L q a c) := by
    simpa only [lobattoNodes, hH, hH.spectrum_real_eq_range_eigenvalues] using hsc
  have hni := (lobattoNodes_injective_and_weights_pos hμ q hs a c hac hJa hJc).1
  obtain ⟨e', v, hv, hvi, hev, ξ, hξ, herr⟩ := exists_integral_sub_rule_eq_iteratedDeriv_mul_twoEndpoint
    hac hμac (lobattoNodes L q a c) (lobattoWeights L q a c) hni hnode hna hnc
    (fun p hp => integral_eval_eq_sum_lobattoWeights_mul_eval hμ q hs a c hp) hf hf' hD
  have hsum := mass_mul_cfc_lobattoJacobiMatrix_eq_sum L q a c f
  rw [← hsum] at herr
  exact ⟨e', v, hv, hvi, hev, ξ, hξ, herr⟩

/-- A nonnegative even derivative makes the actual constructed Lobatto matrix rule
an upper bound on the measure integral. Source: Gautschi (2004), Theorem 3.7; (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_le_mass_mul_cfc_lobattoJacobiMatrix_of_iteratedDeriv_nonneg
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a c : ℝ}
    (hac : a < c) (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (hJa : (orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) (q + 1) - a • 1).PosDef)
    (hJc : (c • 1 - orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) (q + 1)).PosDef)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 2, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 2) f) (Ioo a c))
    (hDpos : ∀ x ∈ Ioo a c, 0 ≤ iteratedDeriv (2 * q + 2) f x) :
    (∫ x, f x ∂μ) ≤ (polynomialIntegral μ hμ) 1 *
      cfc f (lobattoJacobiMatrix (polynomialIntegral μ hμ) q a c) 0 0 := by
  obtain ⟨e, v, hv, hvi, hev, ξ, hξ, herr⟩ :=
    exists_integral_sub_lobattoJacobiRule_eq_iteratedDeriv_mul hμ hac hμac q hs hJa hJc hf hf' hD
  have hw : (∫ x, (x - a) * (x - c) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hμac] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2)) (sq_nonneg _)
  have hE := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (hDpos ξ hξ) (Nat.cast_nonneg (2 * q + 2).factorial)) hw
  rw [← herr] at hE
  exact sub_nonpos.mp hE

end NLAlib
