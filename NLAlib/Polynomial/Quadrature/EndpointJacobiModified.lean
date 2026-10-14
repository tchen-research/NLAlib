import NLAlib.Polynomial.Quadrature.EndpointJacobiLocation
import NLAlib.Polynomial.Quadrature.EndpointModifiedPolynomials
import NLAlib.Polynomial.Quadrature.EndpointReindex
import NLAlib.Polynomial.OrthogonalPolynomials.PolynomialDensity

/-! # Actual endpoint matrix nodes are modified orthogonal roots

The spectral rules already have their exact degree thresholds. Their remaining
nodal products are therefore the canonical monic polynomials of the positive
endpoint-modified functionals, which are the native density measures' functionals.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset Set
open scoped Matrix MatrixOrder

namespace NLAlib

/-- The actual left Radau nodes, after placing the prescribed endpoint first, are
exactly the roots of the canonical left modified polynomial. The original measure
may terminate and the other endpoint may be a remaining root.
Source: Gautschi (2004), Theorem 3.2; operator derivations (AQ7).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_leftRadauNodes_eq_endpoint_modified_roots {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {a c : ℝ} (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c)
    (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard) :
    let L := polynomialIntegral μ hμ
    ∃ e : Equiv.Perm (Fin (q + 1)), ∃ v : Fin q → ℝ,
      Function.Injective v ∧ (∀ i, v i ∈ Icc a c) ∧ (∀ i, a ≠ v i) ∧
        (∀ i, leftRadauNodes L q a (e i) = endpointNodeFamily a v i) ∧
          Lagrange.nodal univ v = monicOrthogonalPolynomial (polynomialWeightedFunctional L (X - C a)) q := by
  dsimp only
  let L := polynomialIntegral μ hμ
  obtain ⟨ha, ham, hmc, hc, hsa, _⟩ := radauJacobiMatrices_bounds_and_endpoints hμ hμac q hs
  have hH := isHermitian_leftRadauJacobiMatrix L q a
  have hn : ∀ i, leftRadauNodes L q a i ∈ Icc a c := hH.eigenvalues_mem_Icc_of_order ha (ham.trans (hmc.trans hc))
  have hna : a ∈ Set.range (leftRadauNodes L q a) := by
    change a ∈ spectrum ℝ (leftRadauJacobiMatrix L q a) at hsa
    simpa only [leftRadauNodes, hH, hH.spectrum_real_eq_range_eigenvalues] using hsa
  obtain ⟨e, v, hv, hvi, hav, hev⟩ := exists_perm_endpointNodeFamily_mem_Icc
    (leftRadauNodes L q a) (radauNodes_injective_and_weights_pos hμ q hs a c).1 hn hna
  refine ⟨e, v, hv, hvi, hav, hev, ?_⟩
  apply nodal_eq_monicOrthogonalPolynomial_of_leftEndpoint_exact hμ hμac hs v
    (leftRadauWeights L q a ∘ e) hv hav
  intro p hp
  have he := integral_eval_eq_sum_leftRadauWeights_mul_eval hμ q hs a hp
  calc _ = ∑ i, leftRadauWeights L q a i * p.eval (leftRadauNodes L q a i) := he
       _ = ∑ i, leftRadauWeights L q a (e i) * p.eval (leftRadauNodes L q a (e i)) :=
         (Equiv.sum_comp e _).symm
       _ = _ := sum_congr rfl fun i _ => by simp only [Function.comp_apply, hev i]

/-- The actual right Radau nodes are the roots of the canonical positive right
modified polynomial together with their prescribed endpoint.
Source: Gautschi (2004), Theorem 3.2; operator derivations (AQ7).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_rightRadauNodes_eq_endpoint_modified_roots {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {a c : ℝ} (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c)
    (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard) :
    let L := polynomialIntegral μ hμ
    ∃ e : Equiv.Perm (Fin (q + 1)), ∃ v : Fin q → ℝ,
      Function.Injective v ∧ (∀ i, v i ∈ Icc a c) ∧ (∀ i, c ≠ v i) ∧
        (∀ i, rightRadauNodes L q c (e i) = endpointNodeFamily c v i) ∧
          Lagrange.nodal univ v = monicOrthogonalPolynomial (polynomialWeightedFunctional L (C c - X)) q := by
  dsimp only
  let L := polynomialIntegral μ hμ
  obtain ⟨ha, ham, hmc, hc, _, hsc⟩ := radauJacobiMatrices_bounds_and_endpoints hμ hμac q hs
  have hH := isHermitian_rightRadauJacobiMatrix L q c
  have hn : ∀ i, rightRadauNodes L q c i ∈ Icc a c := hH.eigenvalues_mem_Icc_of_order (ha.trans (ham.trans hmc)) hc
  have hnc : c ∈ Set.range (rightRadauNodes L q c) := by
    change c ∈ spectrum ℝ (rightRadauJacobiMatrix L q c) at hsc
    simpa only [rightRadauNodes, hH, hH.spectrum_real_eq_range_eigenvalues] using hsc
  obtain ⟨e, v, hv, hvi, hcv, hev⟩ := exists_perm_endpointNodeFamily_mem_Icc
    (rightRadauNodes L q c) (radauNodes_injective_and_weights_pos hμ q hs a c).2.2.1 hn hnc
  refine ⟨e, v, hv, hvi, hcv, hev, ?_⟩
  apply nodal_eq_monicOrthogonalPolynomial_of_rightEndpoint_exact hμ hμac hs v
    (rightRadauWeights L q c ∘ e) hv hcv
  intro p hp
  have he := integral_eval_eq_sum_rightRadauWeights_mul_eval hμ q hs c hp
  calc _ = ∑ i, rightRadauWeights L q c i * p.eval (rightRadauNodes L q c i) := he
       _ = ∑ i, rightRadauWeights L q c (e i) * p.eval (rightRadauNodes L q c (e i)) :=
         (Equiv.sum_comp e _).symm
       _ = _ := sum_congr rfl fun i _ => by simp only [Function.comp_apply, hev i]

/-- Under the clean original support condition, the actual Lobatto interior nodes
are precisely the roots of the canonical positive two-endpoint modified polynomial.
Source: Gautschi (2004), Theorem 3.6; operator derivations (AQ8).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_lobattoNodes_eq_twoEndpoint_modified_roots {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {a c : ℝ} (hac : a < c)
    (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ) (hs : (q + 2 : ℕ∞) ≤ μ.support.encard) :
    let L := polynomialIntegral μ hμ
    ∃ e : Equiv.Perm (Fin (q + 2)), ∃ v : Fin q → ℝ,
      Function.Injective v ∧ (∀ i, v i ∈ Ioo a c) ∧
        (∀ i, lobattoNodes L q a c (e i) = twoEndpointNodeFamily a c v i) ∧
          Lagrange.nodal univ v = monicOrthogonalPolynomial
            (polynomialWeightedFunctional L ((X - C a) * (C c - X))) q := by
  dsimp only
  let L := polynomialIntegral μ hμ
  have hs' : (q + 1 : ℕ∞) ≤ μ.support.encard :=
    ((by exact_mod_cast (show q + 1 ≤ q + 2 by omega) : (q + 1 : ℕ∞) ≤ q + 2).trans hs)
  obtain ⟨ha, hc, hsa, hsc⟩ := lobattoJacobiMatrix_bounds_and_endpoints hμ hac hμac q hs
  obtain ⟨hJa, hJc⟩ := orthogonalPolynomialJacobiMatrix_endpoint_shifts_posDef hμ hμac (q + 1) (by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs)
  have hH := isHermitian_lobattoJacobiMatrix L q a c
  have hn : ∀ i, lobattoNodes L q a c i ∈ Icc a c := hH.eigenvalues_mem_Icc_of_order ha hc
  have hna : a ∈ Set.range (lobattoNodes L q a c) := by
    change a ∈ spectrum ℝ (lobattoJacobiMatrix L q a c) at hsa
    simpa only [lobattoNodes, hH, hH.spectrum_real_eq_range_eigenvalues] using hsa
  have hnc : c ∈ Set.range (lobattoNodes L q a c) := by
    change c ∈ spectrum ℝ (lobattoJacobiMatrix L q a c) at hsc
    simpa only [lobattoNodes, hH, hH.spectrum_real_eq_range_eigenvalues] using hsc
  obtain ⟨e, v, hv, hvi, hev⟩ := exists_perm_twoEndpointNodeFamily (lobattoNodes L q a c)
    (lobattoNodes_injective_and_weights_pos hμ q hs' a c hac hJa hJc).1 hac hn hna hnc
  refine ⟨e, v, hv, hvi, hev, ?_⟩
  apply nodal_eq_monicOrthogonalPolynomial_of_twoEndpoint_exact hμ hac hμac hs v
    (lobattoWeights L q a c ∘ e) hv (fun i => (hvi i).1.ne) (fun i => (hvi i).2.ne')
  intro p hp
  have he := integral_eval_eq_sum_lobattoWeights_mul_eval hμ q hs' a c hp
  calc _ = ∑ i, lobattoWeights L q a c i * p.eval (lobattoNodes L q a c i) := he
       _ = ∑ i, lobattoWeights L q a c (e i) * p.eval (lobattoNodes L q a c (e i)) :=
         (Equiv.sum_comp e _).symm
       _ = _ := sum_congr rfl fun i _ => by simp only [Function.comp_apply, hev i]

end NLAlib
