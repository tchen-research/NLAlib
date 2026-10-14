import NLAlib.Polynomial.Quadrature.EndpointMeasureRemainder

/-! # Exactness at zero endpoint nodal norm

A zero signed endpoint nodal integral forces the original measure onto the supplied
nodes. Its finite Hermite interpolant therefore agrees almost everywhere with every
function, and polynomial exactness integrates every function. Repeated endpoints and
atomic termination do not require differentiability assumptions in this branch.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- A zero Radau signed nodal integral gives exactness for every function, including
terminal nodes at the opposite endpoint. Source: focused reroutes, Section 3, termination.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eq_endpoint_quadrature_of_integral_nodal_eq_zero
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b t : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) (ht : t = a ∨ t = b) {q : ℕ}
    (v : Fin q → ℝ) (w : Fin (q + 1) → ℝ) (hv : Function.Injective v)
    (htv : ∀ i, t ≠ v i)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (endpointNodeFamily t v i))
    (hzero : (∫ x, (x - t) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ) = 0)
    (f : ℝ → ℝ) : (∫ x, f x ∂μ) = ∑ i, w i * f (endpointNodeFamily t v i) := by
  let P := Lagrange.nodal univ v
  let W : ℝ → ℝ := fun x => (x - t) * P.eval x ^ 2
  have hWi : Integrable W μ := by
    have hp : ((X - C t) * P ^ 2).eval = W := by funext x; simp [W]
    rw [← hp]
    exact integrable_eval_of_ae_mem_Icc hμ _
  have hae : ∀ᵐ x ∂μ, W x = 0 := by
    rcases ht with rfl | rfl
    · have hw : ∀ᵐ x ∂μ, 0 ≤ W x := by
        filter_upwards [hμ] with x hx
        exact mul_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg _)
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hw hWi).mp hzero] with x hx
      exact hx
    · have hw : ∀ᵐ x ∂μ, 0 ≤ -W x := by
        filter_upwards [hμ] with x hx
        exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _))
      have hz : (∫ x, -W x ∂μ) = 0 := by rw [integral_neg]; exact neg_eq_zero.mpr hzero
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hw hWi.neg).mp hz] with x hx
      exact neg_eq_zero.mp hx
  let H := Lagrange.hermiteEndpointInterpolate t (f t) v (f ∘ v) 0
  have hHnode (i : Fin (q + 1)) : H.eval (endpointNodeFamily t v i) = f (endpointNodeFamily t v i) := by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Lagrange.eval_hermiteEndpointInterpolate_endpoint _ _ _ _ _ htv
    · exact Lagrange.eval_hermiteEndpointInterpolate_at_node _ _ hv _ _ i
  have hfH : f =ᵐ[μ] H.eval := by
    filter_upwards [hae] with x hx
    rcases mul_eq_zero.mp hx with hx | hx
    · have hxt : x = t := sub_eq_zero.mp hx
      subst x
      exact (Lagrange.eval_hermiteEndpointInterpolate_endpoint _ _ _ _ _ htv).symm
    · have hp : P.eval x = 0 := sq_eq_zero_iff.mp hx
      simp only [P, Lagrange.eval_nodal, prod_eq_zero_iff] at hp
      obtain ⟨i, _, hi⟩ := hp
      have hxi : x = v i := sub_eq_zero.mp hi
      subst x
      exact (hHnode i.succ).symm
  rw [integral_congr_ae hfH, hexact H (Lagrange.degree_hermiteEndpointInterpolate_lt _ _ hv _ _)]
  exact sum_congr rfl fun i _ => by rw [hHnode i]

/-- A zero Lobatto signed nodal integral gives exactness for every function, including
terminal finite atomic measures. Source: focused reroutes, Section 3, termination.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eq_twoEndpoint_quadrature_of_integral_nodal_eq_zero
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ}
    (v : Fin q → ℝ) (w : Fin (q + 2) → ℝ) (hv : Function.Injective v)
    (hav : ∀ i, a ≠ v i) (hbv : ∀ i, b ≠ v i)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 2 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (twoEndpointNodeFamily a b v i))
    (hzero : (∫ x, (x - a) * (x - b) * (Lagrange.nodal univ v).eval x ^ 2 ∂μ) = 0)
    (f : ℝ → ℝ) : (∫ x, f x ∂μ) = ∑ i, w i * f (twoEndpointNodeFamily a b v i) := by
  let P := Lagrange.nodal univ v
  let W : ℝ → ℝ := fun x => (x - a) * (x - b) * P.eval x ^ 2
  have hWi : Integrable W μ := by
    have hp : ((X - C a) * (X - C b) * P ^ 2).eval = W := by funext x; simp [W]
    rw [← hp]
    exact integrable_eval_of_ae_mem_Icc hμ _
  have hw : ∀ᵐ x ∂μ, 0 ≤ -W x := by
    filter_upwards [hμ] with x hx
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2)) (sq_nonneg _))
  have hz : (∫ x, -W x ∂μ) = 0 := by rw [integral_neg]; exact neg_eq_zero.mpr hzero
  have hae : ∀ᵐ x ∂μ, W x = 0 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hw hWi.neg).mp hz] with x hx
    exact neg_eq_zero.mp hx
  let H := Lagrange.hermiteTwoEndpointInterpolate a b (f a) (f b) v (f ∘ v) 0
  have hHnode (i : Fin (q + 2)) : H.eval (twoEndpointNodeFamily a b v i) = f (twoEndpointNodeFamily a b v i) := by
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact Lagrange.eval_hermiteTwoEndpointInterpolate_left _ _ _ _ _ _ _ hav
    · exact Lagrange.eval_hermiteTwoEndpointInterpolate_right _ _ _ _ _ _ _ hab.ne hav hbv
    · exact Lagrange.eval_hermiteTwoEndpointInterpolate_at_node _ _ _ _ hv _ _ i
  have hfH : f =ᵐ[μ] H.eval := by
    filter_upwards [hae] with x hx
    rcases mul_eq_zero.mp hx with hx | hx
    · rcases mul_eq_zero.mp hx with hx | hx
      · have hxa : x = a := sub_eq_zero.mp hx
        subst x
        exact (Lagrange.eval_hermiteTwoEndpointInterpolate_left _ _ _ _ _ _ _ hav).symm
      · have hxb : x = b := sub_eq_zero.mp hx
        subst x
        exact (Lagrange.eval_hermiteTwoEndpointInterpolate_right _ _ _ _ _ _ _ hab.ne hav hbv).symm
    · have hp : P.eval x = 0 := sq_eq_zero_iff.mp hx
      simp only [P, Lagrange.eval_nodal, prod_eq_zero_iff] at hp
      obtain ⟨i, _, hi⟩ := hp
      have hxi : x = v i := sub_eq_zero.mp hi
      subst x
      exact (hHnode i.succ.succ).symm
  rw [integral_congr_ae hfH, hexact H (Lagrange.degree_hermiteTwoEndpointInterpolate_lt _ _ _ _ hv _ _)]
  exact sum_congr rfl fun i _ => by rw [hHnode i]

end NLAlib
