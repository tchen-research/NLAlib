import NLAlib.Polynomial.Quadrature.RadauRemainder
import NLAlib.Polynomial.Quadrature.LobattoRemainder
import NLAlib.Polynomial.Quadrature.RadauLobatto
import NLAlib.Polynomial.Quadrature.GeneralMeasure
import NLAlib.ForMathlib.MeasureTheory.IntegralMeanValue

/-! # Integral Radau and Lobatto derivative remainders

The actual endpoint Hermite interpolants and exactness of the supplied rules give the
classical integral derivative formulas. Their original nodal factors retain the correct
left/right Radau and Lobatto signs. No intermediate-point selection is measurable.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- A Radau-degree rule with one interval endpoint and distinct interior nodes has the
order-`2q+1` integral derivative remainder. The factor is `x−t`, so it is nonnegative at
the left endpoint and nonpositive at the right. The case `q=0` is included.
Source: Gautschi (2004), Theorems 3.3 and 3.7; operator derivations (AQ9)–(AQ10).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_integral_sub_endpoint_quadrature_eq_iteratedDeriv_mul
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b t : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) (ht : t = a ∨ t = b) {q : ℕ}
    (v : Fin q → ℝ) (w : Fin (q + 1) → ℝ) (hv : Function.Injective v)
    (hva : ∀ i, v i ∈ Ioo a b)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (endpointNodeFamily t v i))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a b)) :
    ∃ ξ ∈ Ioo a b,
      (∫ x, f x ∂μ) - ∑ i, w i * f (endpointNodeFamily t v i) =
        iteratedDeriv (2 * q + 1) f ξ / (2 * q + 1).factorial *
          ∫ x, (x - t) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ := by
  have htv (i : Fin q) : t ≠ v i := by
    rcases ht with rfl | rfl
    · exact (hva i).1.ne
    · exact (hva i).2.ne'
  have htmem : t ∈ Icc a b := by rcases ht with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
  let H := Lagrange.hermiteEndpointInterpolate t (f t) v (f ∘ v) (deriv f ∘ v)
  have hHnode (i : Fin (q + 1)) : H.eval (endpointNodeFamily t v i) =
      f (endpointNodeFamily t v i) := by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Lagrange.eval_hermiteEndpointInterpolate_endpoint _ _ _ _ _ htv
    · exact Lagrange.eval_hermiteEndpointInterpolate_at_node _ _ hv _ _ i
  have hHintegral : (∫ x, H.eval x ∂μ) = ∑ i, w i * f (endpointNodeFamily t v i) := by
    rw [hexact H (Lagrange.degree_hermiteEndpointInterpolate_lt _ _ hv _ _)]
    simp only [hHnode]
  have hfi : Integrable f μ := by
    refine (hf.integrableOn_compact isCompact_Icc).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [hμ] with x hx hnot
    exact (hnot hx).elim
  have hHi := integrable_eval_of_ae_mem_Icc hμ H
  let W : ℝ → ℝ := fun x => (x - t) * (Lagrange.nodal univ v).eval x ^ 2
  have hWi : Integrable W μ := by
    have heq : ((X - C t) * Lagrange.nodal univ v ^ 2).eval = W := by
      funext x
      simp only [W, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
    rw [← heq]
    exact integrable_eval_of_ae_mem_Icc hμ _
  have hWsign : (∀ᵐ x ∂μ, 0 ≤ W x) ∨ (∀ᵐ x ∂μ, W x ≤ 0) := by
    rcases ht with rfl | rfl
    · left
      filter_upwards [hμ] with x hx
      exact mul_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg _)
    · right
      filter_upwards [hμ] with x hx
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _)
  obtain ⟨ξ, hξ, he⟩ := exists_integral_eq_mul_integral_of_pointwise_of_weight_constant_sign
    (s := Set.Ioo a b) (D := fun ξ => iteratedDeriv (2 * q + 1) f ξ / (2 * q + 1).factorial)
    (hfi.sub hHi) hWi hWsign (Set.nonempty_Ioo.mpr hab) isPreconnected_Ioo
    (hD.div_const _) (by
      filter_upwards [hμ] with x hx
      exact exists_sub_eval_hermiteEndpointInterpolate_eq hab htmem hv hva htv hx hf hf')
  exact ⟨ξ, hξ, by simpa only [Pi.sub_apply, integral_sub hfi hHi, hHintegral] using he⟩

/-- A Lobatto-degree rule with both interval endpoints and distinct interior nodes has
the order-`2q+2` derivative remainder with the nonpositive factor `(x−a)(x−b)`.
The case `q=0` is the two-endpoint linear rule. Source: Gautschi (2004), Theorem 3.7;
operator derivations (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_integral_sub_twoEndpoint_quadrature_eq_iteratedDeriv_mul
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ}
    (v : Fin q → ℝ) (w : Fin (q + 2) → ℝ) (hv : Function.Injective v)
    (hva : ∀ i, v i ∈ Ioo a b)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 2 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (twoEndpointNodeFamily a b v i))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 2, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 2) f) (Ioo a b)) :
    ∃ ξ ∈ Ioo a b,
      (∫ x, f x ∂μ) - ∑ i, w i * f (twoEndpointNodeFamily a b v i) =
        iteratedDeriv (2 * q + 2) f ξ / (2 * q + 2).factorial *
          ∫ x, (x - a) * (x - b) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ := by
  let H := Lagrange.hermiteTwoEndpointInterpolate a b (f a) (f b) v (f ∘ v) (deriv f ∘ v)
  have hav (i : Fin q) : a ≠ v i := (hva i).1.ne
  have hbv (i : Fin q) : b ≠ v i := (hva i).2.ne'
  have hHnode (i : Fin (q + 2)) : H.eval (twoEndpointNodeFamily a b v i) =
      f (twoEndpointNodeFamily a b v i) := by
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact Lagrange.eval_hermiteTwoEndpointInterpolate_left _ _ _ _ _ _ _ hav
    · exact Lagrange.eval_hermiteTwoEndpointInterpolate_right _ _ _ _ _ _ _ hab.ne hav hbv
    · exact Lagrange.eval_hermiteTwoEndpointInterpolate_at_node _ _ _ _ hv _ _ i
  have hHintegral : (∫ x, H.eval x ∂μ) = ∑ i, w i * f (twoEndpointNodeFamily a b v i) := by
    rw [hexact H (Lagrange.degree_hermiteTwoEndpointInterpolate_lt _ _ _ _ hv _ _)]
    simp only [hHnode]
  have hfi : Integrable f μ := by
    refine (hf.integrableOn_compact isCompact_Icc).integrable_of_ae_notMem_eq_zero ?_
    filter_upwards [hμ] with x hx hnot
    exact (hnot hx).elim
  have hHi := integrable_eval_of_ae_mem_Icc hμ H
  let W : ℝ → ℝ := fun x => (x - a) * (x - b) * (Lagrange.nodal univ v).eval x ^ 2
  have hWi : Integrable W μ := by
    have heq : ((X - C a) * (X - C b) * Lagrange.nodal univ v ^ 2).eval = W := by
      funext x
      simp only [W, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
    rw [← heq]
    exact integrable_eval_of_ae_mem_Icc hμ _
  have hWsign : (∀ᵐ x ∂μ, W x ≤ 0) := by
    filter_upwards [hμ] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2)) (sq_nonneg _)
  obtain ⟨ξ, hξ, he⟩ := exists_integral_eq_mul_integral_of_pointwise_of_weight_constant_sign
    (s := Set.Ioo a b) (D := fun ξ => iteratedDeriv (2 * q + 2) f ξ / (2 * q + 2).factorial)
    (hfi.sub hHi) hWi (Or.inr hWsign) (Set.nonempty_Ioo.mpr hab) isPreconnected_Ioo
    (hD.div_const _) (by
      filter_upwards [hμ] with x hx
      exact exists_sub_eval_hermiteTwoEndpointInterpolate_eq hab hv hva hx hf hf')
  exact ⟨ξ, hξ, by simpa only [Pi.sub_apply, integral_sub hfi hHi, hHintegral] using he⟩

end NLAlib
