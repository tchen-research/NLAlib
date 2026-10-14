import NLAlib.Polynomial.Quadrature.EndpointJacobiLocation
import NLAlib.Polynomial.Quadrature.RadauRuleRemainder

/-! # Derivative remainders of the actual Radau matrix rules

Original interval support provides the endpoint matrix bounds, designated nodes,
and polynomial exactness. The terminal boundary branch is exact for every function.
Thus the original open-interval smoothness assumptions suffice for both actual rules.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset Set
open scoped Matrix MatrixOrder

namespace NLAlib

/-- The actual left Radau Schur matrix has the single-point odd-derivative remainder,
including original finite-support termination and an opposite endpoint node.
Source: operator derivations (AQ9); focused reroutes, Section 3 (BL4)–(BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_integral_sub_leftRadauJacobiRule_eq_iteratedDeriv_mul
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a c : ℝ}
    (hac : a < c) (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c)) :
    let L := polynomialIntegral μ hμ
    ∃ e : Equiv.Perm (Fin (q + 1)), ∃ v : Fin q → ℝ,
      Function.Injective v ∧ (∀ i, v i ∈ Icc a c) ∧ (∀ i, a ≠ v i) ∧
        (∀ i, leftRadauNodes L q a (e i) = endpointNodeFamily a v i) ∧ ∃ ξ ∈ Ioo a c,
          (∫ x, f x ∂μ) - L 1 * cfc f (leftRadauJacobiMatrix L q a) 0 0 =
            iteratedDeriv (2 * q + 1) f ξ / (2 * q + 1).factorial *
              ∫ x, (x - a) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ := by
  dsimp only
  let L := polynomialIntegral μ hμ
  obtain ⟨ha, ham, hmc, hc, hsa, hsc⟩ := radauJacobiMatrices_bounds_and_endpoints hμ hμac q hs
  have hH := isHermitian_leftRadauJacobiMatrix L q a
  have hn : ∀ i, leftRadauNodes L q a i ∈ Icc a c := hH.eigenvalues_mem_Icc_of_order ha (ham.trans (hmc.trans hc))
  have hna : a ∈ Set.range (leftRadauNodes L q a) := by
    change a ∈ spectrum ℝ (leftRadauJacobiMatrix L q a) at hsa
    simpa only [leftRadauNodes, hH, hH.spectrum_real_eq_range_eigenvalues] using hsa
  have hni := (radauNodes_injective_and_weights_pos hμ q hs a c).1
  obtain ⟨e, v, hv, hvi, hav, hev, ξ, hξ, herr⟩ :=
    exists_integral_sub_radau_degree_rule_eq_iteratedDeriv_mul hac hμac (Or.inl rfl)
      (leftRadauNodes L q a) (leftRadauWeights L q a) hni hn hna
      (fun p hp => integral_eval_eq_sum_leftRadauWeights_mul_eval hμ q hs a hp) hf hf' hD
  rw [← mass_mul_cfc_leftRadauJacobiMatrix_eq_sum L q a f] at herr
  exact ⟨e, v, hv, hvi, hav, hev, ξ, hξ, herr⟩

/-- The actual right Radau Schur matrix has the single-point odd-derivative remainder,
including the exact terminal boundary branch.
Source: operator derivations (AQ10); focused reroutes, Section 3 (BL4)–(BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_integral_sub_rightRadauJacobiRule_eq_iteratedDeriv_mul
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a c : ℝ}
    (hac : a < c) (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c)) :
    let L := polynomialIntegral μ hμ
    ∃ e : Equiv.Perm (Fin (q + 1)), ∃ v : Fin q → ℝ,
      Function.Injective v ∧ (∀ i, v i ∈ Icc a c) ∧ (∀ i, c ≠ v i) ∧
        (∀ i, rightRadauNodes L q c (e i) = endpointNodeFamily c v i) ∧ ∃ ξ ∈ Ioo a c,
          (∫ x, f x ∂μ) - L 1 * cfc f (rightRadauJacobiMatrix L q c) 0 0 =
            iteratedDeriv (2 * q + 1) f ξ / (2 * q + 1).factorial *
              ∫ x, (x - c) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ := by
  dsimp only
  let L := polynomialIntegral μ hμ
  obtain ⟨ha, ham, hmc, hc, hsa, hsc⟩ := radauJacobiMatrices_bounds_and_endpoints hμ hμac q hs
  have hH := isHermitian_rightRadauJacobiMatrix L q c
  have hn : ∀ i, rightRadauNodes L q c i ∈ Icc a c := hH.eigenvalues_mem_Icc_of_order (ha.trans (ham.trans hmc)) hc
  have hnc : c ∈ Set.range (rightRadauNodes L q c) := by
    change c ∈ spectrum ℝ (rightRadauJacobiMatrix L q c) at hsc
    simpa only [rightRadauNodes, hH, hH.spectrum_real_eq_range_eigenvalues] using hsc
  have hni := (radauNodes_injective_and_weights_pos hμ q hs a c).2.2.1
  obtain ⟨e, v, hv, hvi, hcv, hev, ξ, hξ, herr⟩ :=
    exists_integral_sub_radau_degree_rule_eq_iteratedDeriv_mul hac hμac (Or.inr rfl)
      (rightRadauNodes L q c) (rightRadauWeights L q c) hni hn hnc
      (fun p hp => integral_eval_eq_sum_rightRadauWeights_mul_eval hμ q hs c hp) hf hf' hD
  rw [← mass_mul_cfc_rightRadauJacobiMatrix_eq_sum L q c f] at herr
  exact ⟨e, v, hv, hvi, hcv, hev, ξ, hξ, herr⟩

/-- A nonnegative odd derivative makes the actual left Radau matrix rule a lower
bound, including terminal exactness. Source: Gautschi (2004), Theorem 3.7; (AQ9).
atlas: gauss-radau-lobatto (partial) -/
theorem mass_mul_cfc_leftRadauJacobiMatrix_le_integral_of_iteratedDeriv_nonneg
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a c : ℝ}
    (hac : a < c) (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c))
    (hDpos : ∀ x ∈ Ioo a c, 0 ≤ iteratedDeriv (2 * q + 1) f x) :
    (polynomialIntegral μ hμ) 1 * cfc f (leftRadauJacobiMatrix (polynomialIntegral μ hμ) q a) 0 0 ≤
      ∫ x, f x ∂μ := by
  obtain ⟨e, v, hv, hvi, hav, hev, ξ, hξ, herr⟩ :=
    exists_integral_sub_leftRadauJacobiRule_eq_iteratedDeriv_mul hμ hac hμac q hs hf hf' hD
  have hw : 0 ≤ ∫ x, (x - a) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hμac] with x hx
    exact mul_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg _)
  have hE := mul_nonneg (div_nonneg (hDpos ξ hξ) (Nat.cast_nonneg (2 * q + 1).factorial)) hw
  rw [← herr] at hE
  exact sub_nonneg.mp hE

/-- A nonnegative odd derivative makes the actual right Radau matrix rule an upper
bound, including terminal exactness. Source: Gautschi (2004), Theorem 3.7; (AQ10).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_le_mass_mul_cfc_rightRadauJacobiMatrix_of_iteratedDeriv_nonneg
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : HasPolynomialMoments μ) {a c : ℝ}
    (hac : a < c) (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c))
    (hDpos : ∀ x ∈ Ioo a c, 0 ≤ iteratedDeriv (2 * q + 1) f x) :
    (∫ x, f x ∂μ) ≤ (polynomialIntegral μ hμ) 1 *
      cfc f (rightRadauJacobiMatrix (polynomialIntegral μ hμ) q c) 0 0 := by
  obtain ⟨e, v, hv, hvi, hcv, hev, ξ, hξ, herr⟩ :=
    exists_integral_sub_rightRadauJacobiRule_eq_iteratedDeriv_mul hμ hac hμac q hs hf hf' hD
  have hw : (∫ x, (x - c) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hμac] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _)
  have hE := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (hDpos ξ hξ) (Nat.cast_nonneg (2 * q + 1).factorial)) hw
  rw [← herr] at hE
  exact sub_nonpos.mp hE

end NLAlib
