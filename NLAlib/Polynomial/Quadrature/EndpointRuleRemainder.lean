import NLAlib.Polynomial.Quadrature.EndpointReindex
import NLAlib.Polynomial.Quadrature.EndpointMeasureRemainder

/-! # Derivative remainders for finite rules with arbitrary node enumeration

Finite endpoint permutations connect actual spectral enumerations to the explicit
endpoint Hermite interpolants. The integral error is invariant under this reindexing.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- An actual finite Radau-degree rule with its designated endpoint and other nodes
interior has the single-point integral derivative remainder, regardless of enumeration.
The conclusion also supplies the interior nodes and their exact finite permutation.
Source: operator derivations (AQ9)–(AQ10); focused reroutes, Section 3 (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_integral_sub_rule_eq_iteratedDeriv_mul_endpoint
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b t : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) (ht : t = a ∨ t = b) {q : ℕ}
    (v : Fin (q + 1) → ℝ) (w : Fin (q + 1) → ℝ) (hv : Function.Injective v)
    (hvt : t ∈ Set.range v) (hvi : ∀ i, v i ≠ t → v i ∈ Ioo a b)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a b)) :
    ∃ e : Equiv.Perm (Fin (q + 1)), ∃ u : Fin q → ℝ,
      Function.Injective u ∧ (∀ i, u i ∈ Ioo a b) ∧
        (∀ i, v (e i) = endpointNodeFamily t u i) ∧ ∃ ξ ∈ Ioo a b,
          (∫ x, f x ∂μ) - ∑ i, w i * f (v i) =
            iteratedDeriv (2 * q + 1) f ξ / (2 * q + 1).factorial *
              ∫ x, (x - t) * (Lagrange.nodal univ u).eval x ^ 2 ∂μ := by
  obtain ⟨e, u, hu, heu⟩ := exists_perm_endpointNodeFamily v hv hvt
  have hui (i : Fin q) : u i ∈ Ioo a b := by
    have hne : v (e i.succ) ≠ t := by
      intro h
      have he0 : v (e 0) = t := heu 0
      have hid := e.injective (hv (h.trans he0.symm))
      have hval := congrArg Fin.val hid
      simp at hval
    have h := hvi (e i.succ) hne
    simpa only [heu, endpointNodeFamily, Fin.cases_succ] using h
  have hsum (g : ℝ → ℝ) : (∑ i, w i * g (v i)) =
      ∑ i, w (e i) * g (endpointNodeFamily t u i) := by
    calc _ = ∑ i, w (e i) * g (v (e i)) := (Equiv.sum_comp e _).symm
      _ = _ := sum_congr rfl fun i _ => by rw [heu i]
  obtain ⟨ξ, hξ, he⟩ := exists_integral_sub_endpoint_quadrature_eq_iteratedDeriv_mul
    hab hμ ht u (w ∘ e) hu hui (by intro p hp; exact (hexact p hp).trans (hsum p.eval)) hf hf' hD
  exact ⟨e, u, hu, hui, heu, ξ, hξ, by simpa only [Function.comp_apply, ← hsum] using he⟩

/-- A finite Lobatto-degree rule with distinct nodes in the closed interval containing
both endpoints has the classical single-point derivative remainder. Every remaining
node is proved interior from distinctness; enumeration is immaterial.
Source: operator derivations (AQ11); focused reroutes, Section 3 (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem exists_integral_sub_rule_eq_iteratedDeriv_mul_twoEndpoint
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ}
    (v : Fin (q + 2) → ℝ) (w : Fin (q + 2) → ℝ) (hv : Function.Injective v)
    (hvi : ∀ i, v i ∈ Icc a b) (hva : a ∈ Set.range v) (hvb : b ∈ Set.range v)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 2 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * q + 2, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 2) f) (Ioo a b)) :
    ∃ e : Equiv.Perm (Fin (q + 2)), ∃ u : Fin q → ℝ,
      Function.Injective u ∧ (∀ i, u i ∈ Ioo a b) ∧
        (∀ i, v (e i) = twoEndpointNodeFamily a b u i) ∧ ∃ ξ ∈ Ioo a b,
          (∫ x, f x ∂μ) - ∑ i, w i * f (v i) =
            iteratedDeriv (2 * q + 2) f ξ / (2 * q + 2).factorial *
              ∫ x, (x - a) * (x - b) * (Lagrange.nodal univ u).eval x ^ 2 ∂μ := by
  obtain ⟨e, u, hu, hui, heu⟩ := exists_perm_twoEndpointNodeFamily v hv hab hvi hva hvb
  have hsum (g : ℝ → ℝ) : (∑ i, w i * g (v i)) =
      ∑ i, w (e i) * g (twoEndpointNodeFamily a b u i) := by
    calc _ = ∑ i, w (e i) * g (v (e i)) := (Equiv.sum_comp e _).symm
      _ = _ := sum_congr rfl fun i _ => by rw [heu i]
  obtain ⟨ξ, hξ, he⟩ := exists_integral_sub_twoEndpoint_quadrature_eq_iteratedDeriv_mul
    hab hμ u (w ∘ e) hu hui (by intro p hp; exact (hexact p hp).trans (hsum p.eval)) hf hf' hD
  exact ⟨e, u, hu, hui, heu, ξ, hξ, by simpa only [Function.comp_apply, ← hsum] using he⟩

end NLAlib
