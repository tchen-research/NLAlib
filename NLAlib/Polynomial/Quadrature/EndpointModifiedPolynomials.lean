import NLAlib.Polynomial.Quadrature.EndpointWeightPositivity
import NLAlib.Polynomial.OrthogonalPolynomials.Christoffel
import NLAlib.Polynomial.OrthogonalPolynomials.PositiveMomentFunctional

/-! # Canonical modified polynomials of endpoint rules

The original degree thresholds imply nodal orthogonality for the actual endpoint
rules. Positive endpoint-weighted squared moments then identify the remaining nodal
polynomial with the canonical monic polynomial of the modified moment functional.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- A nonnegative polynomial weight preserves a nonsingular order-`q` moment system
when the original measure has at least `q+degree(weight)` support points.
The displayed degree bound also permits weights with roots at interval endpoints. -/
theorem hankelMomentDet_polynomialWeightedFunctional_ne_zero_of_le_support_encard
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {q d : ℕ}
    (hs : (q + d : ℕ∞) ≤ μ.support.encard) {w : ℝ[X]} (hw : w ≠ 0)
    (hd : w.degree ≤ d) (hnon : ∀ᵐ x ∂μ, 0 ≤ w.eval x) :
    hankelMomentDet (polynomialWeightedFunctional (polynomialIntegral μ hμ) w) q ≠ 0 := by
  apply hankelMomentDet_ne_zero_of_posDef_of_le (n := q) _ le_rfl
  apply (posDef_hankelMomentMatrix_iff_functional_sq_pos _ q).mpr
  intro p hp hp0
  have hpN : p.natDegree < q := (natDegree_lt_iff_degree_lt hp0).mpr hp
  have hprod : (w * p).degree < (q + d : ℕ) := by
    apply (degree_mul_le _ _).trans_lt
    calc w.degree + p.degree ≤ (d : ℕ) + (p.natDegree : ℕ) := add_le_add hd degree_le_natDegree
         _ < (q + d : ℕ) := by exact_mod_cast (show d + p.natDegree < q + d by omega)
  simpa only [polynomialWeightedFunctional_apply, polynomialIntegral_apply, eval_mul, eval_pow] using
    integral_eval_mul_sq_pos_of_le_support_encard hμ hs hw hp0 hprod hnon

/-- The remaining nodal polynomial of a Radau-degree rule is monic orthogonal for
the endpoint-modified functional, even when an opposite endpoint occurs at termination.
Source: Gautschi (2004), Theorem 3.2; operator derivations (AQ7).
atlas: gauss-radau-lobatto (partial) -/
theorem isMonicOrthogonalPolynomial_nodal_of_endpoint_exact
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {q : ℕ} (t : ℝ)
    (v : Fin q → ℝ) (w : Fin (q + 1) → ℝ) (hv : Function.Injective v) (htv : ∀ i, t ≠ v i)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (endpointNodeFamily t v i)) :
    IsMonicOrthogonalPolynomial (polynomialWeightedFunctional (polynomialIntegral μ hμ) (X - C t))
      q (Lagrange.nodal univ v) := by
  have hfull := (integral_eq_quadrature_iff hμ (s := univ) (⟨0, mem_univ _⟩ :
    (univ : Finset (Fin (q + 1))).Nonempty) (endpointNodeFamily_injective hv htv).injOn w q).mp (by
      simpa [show q + 1 + q = 2 * q + 1 by omega] using hexact)
  refine ⟨Lagrange.nodal_monic, by simp [Lagrange.natDegree_nodal], ?_⟩
  intro r hr
  simpa only [polynomialWeightedFunctional_apply, polynomialIntegral_apply,
    nodal_endpointNodeFamily, eval_mul, eval_sub, eval_X, eval_C, mul_assoc] using hfull.2 r hr

/-- The remaining nodal polynomial of a Lobatto-degree rule is monic orthogonal for
the positive two-endpoint modified functional.
Source: Gautschi (2004), Theorem 3.6; operator derivations (AQ8).
atlas: gauss-radau-lobatto (partial) -/
theorem isMonicOrthogonalPolynomial_nodal_of_twoEndpoint_exact
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {q : ℕ} (a b : ℝ) (hab : a ≠ b)
    (v : Fin q → ℝ) (w : Fin (q + 2) → ℝ) (hv : Function.Injective v)
    (hav : ∀ i, a ≠ v i) (hbv : ∀ i, b ≠ v i)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 2 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (twoEndpointNodeFamily a b v i)) :
    IsMonicOrthogonalPolynomial
      (polynomialWeightedFunctional (polynomialIntegral μ hμ) ((X - C a) * (C b - X)))
      q (Lagrange.nodal univ v) := by
  have hvall := endpointNodeFamily_injective (endpointNodeFamily_injective hv hbv)
    (fun i => Fin.cases hab hav i)
  have hfull := (integral_eq_quadrature_iff hμ (s := univ) (⟨0, mem_univ _⟩ :
    (univ : Finset (Fin (q + 2))).Nonempty) hvall.injOn w q).mp (by
      simpa [twoEndpointNodeFamily,
        show q + 2 + q = 2 * q + 2 by omega] using hexact)
  refine ⟨Lagrange.nodal_monic, by simp [Lagrange.natDegree_nodal], ?_⟩
  intro r hr
  have h := hfull.2 r hr
  change (∫ x, (Lagrange.nodal univ (twoEndpointNodeFamily a b v)).eval x * r.eval x ∂μ) = 0 at h
  have heq : (fun x => (((X - C a) * (C b - X)) * (Lagrange.nodal univ v * r)).eval x) =
      fun x => -((Lagrange.nodal univ (twoEndpointNodeFamily a b v)).eval x * r.eval x) := by
    funext x
    simp only [nodal_twoEndpointNodeFamily, eval_mul, eval_sub, eval_X, eval_C]
    ring
  rw [polynomialWeightedFunctional_apply, polynomialIntegral_apply, heq, integral_neg, h, neg_zero]

/-- The actual left endpoint rule's remaining node product equals the canonical
monic polynomial for the positive left endpoint modification.
Source: Gautschi (2004), Theorem 3.2; operator derivations (AQ7).
atlas: gauss-radau-lobatto (partial) -/
theorem nodal_eq_monicOrthogonalPolynomial_of_leftEndpoint_exact
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hμab : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ} (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (v : Fin q → ℝ) (w : Fin (q + 1) → ℝ) (hv : Function.Injective v) (hav : ∀ i, a ≠ v i)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (endpointNodeFamily a v i)) :
    Lagrange.nodal univ v = monicOrthogonalPolynomial
      (polynomialWeightedFunctional (polynomialIntegral μ hμ) (X - C a)) q := by
  have hnd := hankelMomentDet_polynomialWeightedFunctional_ne_zero_of_le_support_encard hμ hs
    (X_sub_C_ne_zero a) (by simp : (X - C a : ℝ[X]).degree ≤ (1 : ℕ)) (by
      filter_upwards [hμab] with x hx
      simpa only [eval_sub, eval_X, eval_C] using sub_nonneg.mpr hx.1)
  exact (isMonicOrthogonalPolynomial_nodal_of_endpoint_exact hμ a v w hv hav hexact).eq_of_hankelMomentDet_ne_zero
    (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial _ hnd) hnd

/-- The actual right endpoint rule's remaining node product equals the canonical
monic polynomial for the positive right endpoint modification.
Source: Gautschi (2004), Theorem 3.2; operator derivations (AQ7).
atlas: gauss-radau-lobatto (partial) -/
theorem nodal_eq_monicOrthogonalPolynomial_of_rightEndpoint_exact
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hμab : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ} (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (v : Fin q → ℝ) (w : Fin (q + 1) → ℝ) (hv : Function.Injective v) (hbv : ∀ i, b ≠ v i)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (endpointNodeFamily b v i)) :
    Lagrange.nodal univ v = monicOrthogonalPolynomial
      (polynomialWeightedFunctional (polynomialIntegral μ hμ) (C b - X)) q := by
  have hw0 : (C b - X : ℝ[X]) ≠ 0 := by
    rw [← neg_sub X (C b)]
    exact neg_ne_zero.mpr (X_sub_C_ne_zero b)
  have hwd : (C b - X : ℝ[X]).degree ≤ (1 : ℕ) := by
    rw [← neg_sub X (C b), degree_neg]
    simp
  have hnd := hankelMomentDet_polynomialWeightedFunctional_ne_zero_of_le_support_encard hμ hs hw0 hwd (by
    filter_upwards [hμab] with x hx
    simpa only [eval_sub, eval_X, eval_C] using sub_nonneg.mpr hx.2)
  have hp := isMonicOrthogonalPolynomial_nodal_of_endpoint_exact hμ b v w hv hbv hexact
  have hp' : IsMonicOrthogonalPolynomial
      (polynomialWeightedFunctional (polynomialIntegral μ hμ) (C b - X)) q (Lagrange.nodal univ v) := by
    refine ⟨hp.monic, hp.natDegree_eq, ?_⟩
    intro r hr
    change (polynomialIntegral μ hμ) ((C b - X) * (Lagrange.nodal univ v * r)) = 0
    rw [show (C b - X) * (Lagrange.nodal univ v * r) =
        -((X - C b) * (Lagrange.nodal univ v * r)) by ring, map_neg]
    have hz := hp.orthogonal r hr
    change (polynomialIntegral μ hμ) ((X - C b) * (Lagrange.nodal univ v * r)) = 0 at hz
    rw [hz, neg_zero]
  exact hp'.eq_of_hankelMomentDet_ne_zero (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial _ hnd) hnd

/-- The actual two-endpoint rule's remaining node product is the canonical monic
polynomial for the positive two-endpoint modified functional.
Source: Gautschi (2004), Theorem 3.6; operator derivations (AQ8).
atlas: gauss-radau-lobatto (partial) -/
theorem nodal_eq_monicOrthogonalPolynomial_of_twoEndpoint_exact
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ} (hab : a < b)
    (hμab : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ} (hs : (q + 2 : ℕ∞) ≤ μ.support.encard)
    (v : Fin q → ℝ) (w : Fin (q + 2) → ℝ) (hv : Function.Injective v)
    (hav : ∀ i, a ≠ v i) (hbv : ∀ i, b ≠ v i)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 2 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (twoEndpointNodeFamily a b v i)) :
    Lagrange.nodal univ v = monicOrthogonalPolynomial
      (polynomialWeightedFunctional (polynomialIntegral μ hμ) ((X - C a) * (C b - X))) q := by
  have hb0 : (C b - X : ℝ[X]) ≠ 0 := by
    rw [← neg_sub X (C b)]
    exact neg_ne_zero.mpr (X_sub_C_ne_zero b)
  have hwd : ((X - C a) * (C b - X) : ℝ[X]).degree ≤ (2 : ℕ) := by
    rw [← neg_sub X (C b), mul_neg, degree_neg]
    rw [degree_mul, degree_X_sub_C, degree_X_sub_C]
    norm_num
  have hnd := hankelMomentDet_polynomialWeightedFunctional_ne_zero_of_le_support_encard hμ hs
    (mul_ne_zero (X_sub_C_ne_zero a) hb0) hwd (by
      filter_upwards [hμab] with x hx
      simpa only [eval_mul, eval_sub, eval_X, eval_C] using
        mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))
  exact (isMonicOrthogonalPolynomial_nodal_of_twoEndpoint_exact hμ a b hab.ne v w hv hav hbv hexact).eq_of_hankelMomentDet_ne_zero
    (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial _ hnd) hnd

end NLAlib
