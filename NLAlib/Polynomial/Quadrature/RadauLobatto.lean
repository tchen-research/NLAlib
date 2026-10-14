import NLAlib.Polynomial.Quadrature.MeasureExactness
import Mathlib.Data.Fin.Tuple.Basic

/-! # Exactness of Radau and Lobatto from modified moments

Adjoining one or two prescribed endpoints to the roots of the appropriate modified
moment polynomial gives the Radau/Lobatto exactness degrees by polynomial division.
This is the intrinsic modified-measure specification (AQ1, AQ7–AQ8), independent of
the subsequent Jacobi-border realization.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- A finite node family with one prescribed endpoint, followed by the supplied nodes. -/
def endpointNodeFamily {q : ℕ} (a : ℝ) (v : Fin q → ℝ) : Fin (q + 1) → ℝ := Fin.cases a v

/-- A finite node family with two prescribed endpoints, followed by the supplied nodes. -/
def twoEndpointNodeFamily {q : ℕ} (a b : ℝ) (v : Fin q → ℝ) : Fin (q + 2) → ℝ :=
  endpointNodeFamily a (endpointNodeFamily b v)

/-- Adjoining an endpoint preserves distinctness when it is absent from the other nodes. -/
theorem endpointNodeFamily_injective {q : ℕ} {a : ℝ} {v : Fin q → ℝ}
    (hv : Function.Injective v) (ha : ∀ i, a ≠ v i) :
    Function.Injective (endpointNodeFamily a v) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · intro h
    exact (ha _ h).elim
  · intro h
    exact (ha _ h.symm).elim
  · intro h
    exact congrArg Fin.succ (hv h)

/-- The nodal polynomial of the endpoint-augmented family is its endpoint factor times
the interior nodal polynomial. -/
theorem nodal_endpointNodeFamily {q : ℕ} (a : ℝ) (v : Fin q → ℝ) :
    Lagrange.nodal univ (endpointNodeFamily a v) = (X - C a) * Lagrange.nodal univ v := by
  simp [Lagrange.nodal_eq, Fin.prod_univ_succ, endpointNodeFamily]

/-- The two-endpoint nodal polynomial has both prescribed factors. -/
theorem nodal_twoEndpointNodeFamily {q : ℕ} (a b : ℝ) (v : Fin q → ℝ) :
    Lagrange.nodal univ (twoEndpointNodeFamily a b v) =
      (X - C a) * (X - C b) * Lagrange.nodal univ v := by
  simp only [twoEndpointNodeFamily, nodal_endpointNodeFamily, mul_assoc]

/-- Modified left-endpoint orthogonality gives Radau exactness through degree `2q`
for the actual endpoint-augmented interpolatory rule. The case `q=0` is the one-endpoint
constant rule. Source: Gautschi (2004), Theorem 3.2; operator derivations (AQ1), (AQ7).
This proves intrinsic polynomial exactness, before constructing a Jacobi border.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_eq_endpoint_quadrature_of_modified_orthogonality
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {q : ℕ} (a : ℝ) (v : Fin q → ℝ)
    (hv : Function.Injective v) (ha : ∀ i, a ≠ v i)
    (horth : ∀ r : ℝ[X], r.degree < q →
      (∫ x, (x - a) * (Lagrange.nodal univ v).eval x * r.eval x ∂μ) = 0)
    {p : ℝ[X]} (hp : p.degree < (2 * q + 1 : ℕ)) :
    (∫ x, p.eval x ∂μ) = ∑ i : Fin (q + 1),
      (∫ x, (Lagrange.basis univ (endpointNodeFamily a v) i).eval x ∂μ) *
        p.eval (endpointNodeFamily a v i) := by
  have he := (integral_eq_quadrature_iff hμ
    (s := univ) (show (univ : Finset (Fin (q + 1))).Nonempty from ⟨0, mem_univ _⟩)
    (endpointNodeFamily_injective hv ha).injOn
    (fun i => ∫ x, (Lagrange.basis univ (endpointNodeFamily a v) i).eval x ∂μ) q).mpr
    ⟨fun _ _ => rfl, by
      intro r hr
      simp only [nodal_endpointNodeFamily, eval_mul, eval_sub, eval_X, eval_C]
      exact horth r hr⟩
  have hp' : p.degree < ((univ : Finset (Fin (q + 1))).card + q : ℕ) := by
    simpa only [card_univ, Fintype.card_fin, show q + 1 + q = 2 * q + 1 by omega] using hp
  simpa using he p hp'

/-- Modified two-endpoint orthogonality gives Lobatto exactness through degree `2q+1`
for the actual two-endpoint interpolatory rule. The case `q=0` is the two-endpoint linear
rule. Source: Gautschi (2004), Theorem 3.6; operator derivations (AQ1), (AQ8).
This proves intrinsic polynomial exactness; positivity and border realization are separate.
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_eq_twoEndpoint_quadrature_of_modified_orthogonality
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {q : ℕ} (a b : ℝ) (hab : a ≠ b)
    (v : Fin q → ℝ) (hv : Function.Injective v) (ha : ∀ i, a ≠ v i) (hb : ∀ i, b ≠ v i)
    (horth : ∀ r : ℝ[X], r.degree < q →
      (∫ x, (x - a) * (b - x) * (Lagrange.nodal univ v).eval x * r.eval x ∂μ) = 0)
    {p : ℝ[X]} (hp : p.degree < (2 * q + 2 : ℕ)) :
    (∫ x, p.eval x ∂μ) = ∑ i : Fin (q + 2),
      (∫ x, (Lagrange.basis univ (twoEndpointNodeFamily a b v) i).eval x ∂μ) *
        p.eval (twoEndpointNodeFamily a b v i) := by
  have hinj : Function.Injective (twoEndpointNodeFamily a b v) :=
    endpointNodeFamily_injective (endpointNodeFamily_injective hv hb)
      (fun i => Fin.cases hab ha i)
  have he := (integral_eq_quadrature_iff hμ
    (s := univ) (show (univ : Finset (Fin (q + 2))).Nonempty from ⟨0, mem_univ _⟩)
    hinj.injOn
    (fun i => ∫ x, (Lagrange.basis univ (twoEndpointNodeFamily a b v) i).eval x ∂μ) q).mpr
    ⟨fun _ _ => rfl, by
      intro r hr
      have heq : (fun x => (Lagrange.nodal univ (twoEndpointNodeFamily a b v)).eval x * r.eval x) =
          fun x => -((x - a) * (b - x) * (Lagrange.nodal univ v).eval x * r.eval x) := by
        funext x
        simp only [nodal_twoEndpointNodeFamily, eval_mul, eval_sub, eval_X, eval_C]
        ring
      rw [heq, integral_neg, horth r hr, neg_zero]⟩
  have hp' : p.degree < ((univ : Finset (Fin (q + 2))).card + q : ℕ) := by
    simpa only [card_univ, Fintype.card_fin, show q + 2 + q = 2 * q + 2 by omega] using hp
  simpa using he p hp'

end NLAlib
