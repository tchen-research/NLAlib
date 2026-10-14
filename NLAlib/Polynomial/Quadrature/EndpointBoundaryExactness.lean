import NLAlib.Polynomial.Quadrature.EndpointZeroNorm
import NLAlib.Polynomial.Quadrature.EndpointReindex

/-! # Radau termination when both endpoints occur

A Radau-degree rule that includes both interval endpoints integrates the nonnegative
endpoint-weighted squared interior nodal polynomial to zero. Its original measure is
therefore concentrated on the displayed nodes, so every function is integrated exactly.
This closes the boundary-node branch without demanding derivative jets at endpoints.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- One degree beyond Lobatto exactness forces the endpoint nodal norm to zero and
gives exactness for every function. Source: focused reroutes, Section 3, termination.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eq_twoEndpoint_quadrature_of_one_extra_exact
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ} (v : Fin q → ℝ)
    (w : Fin (q + 2) → ℝ) (hv : Function.Injective v)
    (hav : ∀ i, a ≠ v i) (hbv : ∀ i, b ≠ v i)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 3 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (twoEndpointNodeFamily a b v i))
    (f : ℝ → ℝ) : (∫ x, f x ∂μ) = ∑ i, w i * f (twoEndpointNodeFamily a b v i) := by
  let P := Lagrange.nodal univ v
  let W : ℝ[X] := (X - C a) * (X - C b) * P ^ 2
  have hP : P.natDegree = q := by simp only [P, Lagrange.natDegree_nodal, card_univ, Fintype.card_fin]
  have hWd : W.degree < (2 * q + 3 : ℕ) := by
    apply degree_le_natDegree.trans_lt
    have h₁ := natDegree_mul_le (p := (X - C a : ℝ[X])) (q := X - C b)
    have h₂ := natDegree_mul_le (p := (X - C a : ℝ[X]) * (X - C b)) (q := P ^ 2)
    rw [natDegree_X_sub_C, natDegree_X_sub_C] at h₁
    rw [natDegree_pow, hP] at h₂
    exact_mod_cast (show W.natDegree < 2 * q + 3 by dsimp only [W]; omega)
  have hzero : (∫ x, (x - a) * (x - b) * P.eval x ^ 2 ∂μ) = 0 := by
    have h := hexact W hWd
    have hn (i : Fin (q + 2)) : W.eval (twoEndpointNodeFamily a b v i) = 0 := by
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · change W.eval a = 0
        simp [W]
      · change W.eval b = 0
        simp [W]
      · simp [W, twoEndpointNodeFamily, endpointNodeFamily, P,
          Lagrange.eval_nodal_at_node (mem_univ i)]
    simpa only [W, eval_mul, eval_sub, eval_X, eval_C, eval_pow, hn, mul_zero,
      sum_const_zero] using h
  exact integral_eq_twoEndpoint_quadrature_of_integral_nodal_eq_zero hab hμ v w hv hav hbv
    (fun p hp => hexact p (hp.trans_le (by exact_mod_cast (show 2 * q + 2 ≤ 2 * q + 3 by omega))))
    hzero f

/-- A distinct Radau-degree rule with both interval endpoints is a terminal rule:
it integrates every function exactly. This follows from its existing polynomial
exactness and interval support, with no smoothness or finite-support premise added.
Source: focused reroutes, Section 3, termination.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eq_radau_degree_rule_of_both_endpoints
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {q : ℕ} (v w : Fin (q + 1) → ℝ)
    (hv : Function.Injective v) (hvi : ∀ i, v i ∈ Icc a b)
    (hva : a ∈ Set.range v) (hvb : b ∈ Set.range v)
    (hexact : ∀ p : ℝ[X], p.degree < (2 * q + 1 : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i))
    (f : ℝ → ℝ) : (∫ x, f x ∂μ) = ∑ i, w i * f (v i) := by
  cases q with
  | zero =>
    obtain ⟨i, hi⟩ := hva
    obtain ⟨j, hj⟩ := hvb
    have hij : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    exact (hab.ne (hi.symm.trans ((congrArg v hij).trans hj))).elim
  | succ q =>
    obtain ⟨e, u, hu, hui, heu⟩ := exists_perm_twoEndpointNodeFamily v hv hab hvi hva hvb
    have hsum (g : ℝ → ℝ) : (∑ i, w i * g (v i)) =
        ∑ i, w (e i) * g (twoEndpointNodeFamily a b u i) := by
      calc _ = ∑ i, w (e i) * g (v (e i)) := (Equiv.sum_comp e _).symm
           _ = _ := sum_congr rfl fun i _ => by rw [heu i]
    have he := integral_eq_twoEndpoint_quadrature_of_one_extra_exact hab hμ u (w ∘ e) hu
      (fun i => (hui i).1.ne) (fun i => (hui i).2.ne') (by
        intro p hp
        have hd : p.degree < (2 * (q + 1) + 1 : ℕ) := by
          simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hp
        exact (hexact p hd).trans (hsum p.eval)) f
    exact he.trans (by simpa only [Function.comp_apply] using (hsum f).symm)

end NLAlib
