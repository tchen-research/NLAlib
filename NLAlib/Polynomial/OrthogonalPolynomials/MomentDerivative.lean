import NLAlib.Polynomial.OrthogonalPolynomials.MomentCoordinates

/-!
# Differentiating finite moment pairings

Polynomial coefficient derivatives give a product rule for a varying moment
functional. The statement uses bounded degrees rather than any norm on the
infinite-dimensional polynomial space. Source: AQ26 in the operator re-derivations.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib

/-- The derivative of a varying polynomial pairing is the sum of the functional
variation and the polynomial variation. No representing measures are needed.
Source: AQ26.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem hasDerivAt_functional_polynomial
    {L : ℝ → (ℝ[X] →ₗ[ℝ] ℝ)} {D : ℝ[X] →ₗ[ℝ] ℝ}
    {p : ℝ → ℝ[X]} {p' : ℝ[X]} {x : ℝ} {d : ℕ}
    (hp : ∀ y, (p y).degree < d) (hp' : p'.degree < d)
    (hc : HasCoeffDerivAt p p' x)
    (hL : ∀ k, HasDerivAt (fun y => L y (X ^ k)) (D (X ^ k)) x) :
    HasDerivAt (fun y => L y (p y)) (D (p x) + L x p') x := by
  have hpair (M : ℝ[X] →ₗ[ℝ] ℝ) (s : ℝ[X]) (hs : s.degree < d) :
      M s = ∑ i : Fin d, s.coeff i.val * M (X ^ i.val) := by
    nth_rw 1 [eq_sum_monomial_fin_of_degree_lt hs]
    simp only [map_sum, ← C_mul_X_pow_eq_monomial, C_mul', map_smul, smul_eq_mul]
  have heq : (fun y => L y (p y)) =
      fun y => ∑ i : Fin d, (p y).coeff i.val * L y (X ^ i.val) := by
    funext y
    exact hpair (L y) (p y) (hp y)
  rw [heq, hpair D (p x) (hp x), hpair (L x) p' hp']
  convert HasDerivAt.fun_sum (fun i (_ : i ∈ (univ : Finset (Fin d))) =>
    (hc i.val).mul (hL i.val)) using 1
  all_goals first | rfl | simp [Finset.sum_add_distrib, add_comm]

/-- An affine finite-moment perturbation has the given moment derivative. -/
theorem hasDerivAt_finiteMomentFunctional_apply {d : ℕ} (m v : Fin d → ℝ)
    (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun t => finiteMomentFunctional (m + t • v) p)
      (finiteMomentFunctional v p) x := by
  simp only [finiteMomentFunctional_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  convert HasDerivAt.fun_sum (fun i (_ : i ∈ (univ : Finset (Fin d))) =>
    ((hasDerivAt_const x (m i)).add ((hasDerivAt_id x).mul_const (v i))).mul_const
      (p.coeff i.val)) using 1
  all_goals first | rfl | simp

end NLAlib
