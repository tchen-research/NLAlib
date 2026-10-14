import NLAlib.Polynomial.Quadrature.EndpointBoundaryExactness
import NLAlib.Polynomial.Quadrature.EndpointRuleRemainder

/-! # Radau remainder including the terminal boundary branch

Interior nodes use the Hermite–Rolle derivative remainder. If the opposite endpoint
also occurs, the Radau degree threshold forces exactness for every function and a
zero signed nodal norm. Thus the same single-point formula covers that branch without
assuming repeated derivative jets at the interval endpoints.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- The single-point Radau derivative remainder, including a possible opposite endpoint
at finite-support termination. The remaining nodes are in the closed interval; whenever
one is the opposite endpoint, its signed nodal norm and the error are both zero.
Source: operator derivations (AQ9)–(AQ10); focused reroutes, Section 3 (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_integral_sub_radau_degree_rule_eq_iteratedDeriv_mul
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b t : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) (ht : t = a ∨ t = b) {q : ℕ}
    (v w : Fin (q + 1) → ℝ) (hv : Function.Injective v)
    (hvi : ∀ i, v i ∈ Icc a b) (hvt : t ∈ Set.range v)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a b)) :
    ∃ e : Equiv.Perm (Fin (q + 1)), ∃ u : Fin q → ℝ,
      Function.Injective u ∧ (∀ i, u i ∈ Icc a b) ∧ (∀ i, t ≠ u i) ∧
        (∀ i, v (e i) = endpointNodeFamily t u i) ∧ ∃ ξ ∈ Ioo a b,
          (∫ x, f x ∂μ) - ∑ i, w i * f (v i) =
            iteratedDeriv (2 * q + 1) f ξ / (2 * q + 1).factorial *
              ∫ x, (x - t) * (Lagrange.nodal univ u).eval x ^ 2 ∂μ := by
  by_cases hboth : a ∈ Set.range v ∧ b ∈ Set.range v
  · have he (g : ℝ → ℝ) := integral_eq_radau_degree_rule_of_both_endpoints
      hab hμ v w hv hvi hboth.1 hboth.2 hexact g
    obtain ⟨e, u, hu, heu⟩ := exists_perm_endpointNodeFamily v hv hvt
    have hui (i : Fin q) : u i ∈ Icc a b := by
      simpa only [heu, endpointNodeFamily, Fin.cases_succ] using hvi (e i.succ)
    have htu (i : Fin q) : t ≠ u i := by
      intro h
      have hid := e.injective (hv ((heu 0).trans (h.trans (heu i.succ).symm)))
      have hval := congrArg Fin.val hid
      simp at hval
    let W : ℝ → ℝ := fun x => (x - t) * (Lagrange.nodal univ u).eval x ^ 2
    have hW (i : Fin (q + 1)) : W (v i) = 0 := by
      obtain ⟨j, rfl⟩ := e.surjective i
      rw [heu j]
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [W, endpointNodeFamily]
      · simp [W, endpointNodeFamily, Lagrange.eval_nodal_at_node (mem_univ j)]
    have hz : (∫ x, W x ∂μ) = 0 := by simpa only [hW, mul_zero, sum_const_zero] using he W
    refine ⟨e, u, hu, hui, htu, heu, (a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [he f, sub_self]
    change 0 = _ * ∫ x, W x ∂μ
    rw [hz, mul_zero]
  · have hint (i : Fin (q + 1)) (hne : v i ≠ t) : v i ∈ Ioo a b := by
      have ha : v i ≠ a := by
        intro h
        rcases ht with ht | ht
        · exact hne (h.trans ht.symm)
        · exact hboth ⟨⟨i, h⟩, by simpa only [ht] using hvt⟩
      have hb : v i ≠ b := by
        intro h
        rcases ht with ht | ht
        · exact hboth ⟨by simpa only [ht] using hvt, ⟨i, h⟩⟩
        · exact hne (h.trans ht.symm)
      exact ⟨lt_of_le_of_ne (hvi i).1 ha.symm, lt_of_le_of_ne (hvi i).2 hb⟩
    obtain ⟨e, u, hu, hui, heu, ξ, hξ, herr⟩ :=
      exists_integral_sub_rule_eq_iteratedDeriv_mul_endpoint hab hμ ht v w hv hvt hint hexact hf hf' hD
    have htu (i : Fin q) : t ≠ u i := by
      rcases ht with rfl | rfl
      · exact (hui i).1.ne
      · exact (hui i).2.ne'
    exact ⟨e, u, hu, fun i => ⟨(hui i).1.le, (hui i).2.le⟩, htu, heu, ξ, hξ, herr⟩

end NLAlib
