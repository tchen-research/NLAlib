import NLAlib.Polynomial.Quadrature.EndpointJacobiRules

/-! # Actual endpoint matrix nodes and weights

The nodes are eigenvalues of the constructed Schur borders. Each weight is the measure
mass times the squared first coordinate of the corresponding normalized eigenvector.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

/-- Nodes of the actual left Radau matrix rule. -/
def leftRadauNodes (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (a : ℝ) : Fin (q + 1) → ℝ :=
  (isHermitian_leftRadauJacobiMatrix L q a).eigenvalues

/-- Mass-scaled first-coordinate weights of the actual left Radau rule. -/
def leftRadauWeights (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (a : ℝ) : Fin (q + 1) → ℝ :=
  fun i => L 1 * ((isHermitian_leftRadauJacobiMatrix L q a).eigenvectorBasis i 0) ^ 2

/-- Nodes of the actual right Radau matrix rule. -/
def rightRadauNodes (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (c : ℝ) : Fin (q + 1) → ℝ :=
  (isHermitian_rightRadauJacobiMatrix L q c).eigenvalues

/-- Mass-scaled first-coordinate weights of the actual right Radau rule. -/
def rightRadauWeights (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (c : ℝ) : Fin (q + 1) → ℝ :=
  fun i => L 1 * ((isHermitian_rightRadauJacobiMatrix L q c).eigenvectorBasis i 0) ^ 2

/-- Nodes of the actual two-endpoint Lobatto matrix rule. -/
def lobattoNodes (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (a c : ℝ) : Fin (q + 2) → ℝ :=
  (isHermitian_lobattoJacobiMatrix L q a c).eigenvalues

/-- Mass-scaled first-coordinate weights of the actual Lobatto rule. -/
def lobattoWeights (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (a c : ℝ) : Fin (q + 2) → ℝ :=
  fun i => L 1 * ((isHermitian_lobattoJacobiMatrix L q a c).eigenvectorBasis i 0) ^ 2

/-- The actual left Radau cfc estimate is its explicit Golub–Welsch node sum. -/
theorem mass_mul_cfc_leftRadauJacobiMatrix_eq_sum (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ)
    (a : ℝ) (f : ℝ → ℝ) :
    L 1 * cfc f (leftRadauJacobiMatrix L q a) 0 0 =
      ∑ i, leftRadauWeights L q a i * f (leftRadauNodes L q a i) := by
  have h := cfc_apply_zero_zero_eq_sum (Nat.succ_pos q) (isHermitian_leftRadauJacobiMatrix L q a) f
  calc _ = L 1 * ∑ i, ((isHermitian_leftRadauJacobiMatrix L q a).eigenvectorBasis i 0) ^ 2 *
      f ((isHermitian_leftRadauJacobiMatrix L q a).eigenvalues i) := congrArg (fun x => L 1 * x) h
       _ = _ := ?_
  rw [mul_sum]
  exact sum_congr rfl fun _ _ => by dsimp [leftRadauWeights, leftRadauNodes]; ring

/-- The actual right Radau cfc estimate is its explicit Golub–Welsch node sum. -/
theorem mass_mul_cfc_rightRadauJacobiMatrix_eq_sum (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ)
    (c : ℝ) (f : ℝ → ℝ) :
    L 1 * cfc f (rightRadauJacobiMatrix L q c) 0 0 =
      ∑ i, rightRadauWeights L q c i * f (rightRadauNodes L q c i) := by
  have h := cfc_apply_zero_zero_eq_sum (Nat.succ_pos q) (isHermitian_rightRadauJacobiMatrix L q c) f
  calc _ = L 1 * ∑ i, ((isHermitian_rightRadauJacobiMatrix L q c).eigenvectorBasis i 0) ^ 2 *
      f ((isHermitian_rightRadauJacobiMatrix L q c).eigenvalues i) := congrArg (fun x => L 1 * x) h
       _ = _ := ?_
  rw [mul_sum]
  exact sum_congr rfl fun _ _ => by dsimp [rightRadauWeights, rightRadauNodes]; ring

/-- The actual Lobatto cfc estimate is its explicit Golub–Welsch node sum. -/
theorem mass_mul_cfc_lobattoJacobiMatrix_eq_sum (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ)
    (a c : ℝ) (f : ℝ → ℝ) :
    L 1 * cfc f (lobattoJacobiMatrix L q a c) 0 0 =
      ∑ i, lobattoWeights L q a c i * f (lobattoNodes L q a c i) := by
  have h := cfc_apply_zero_zero_eq_sum (by omega : 0 < q + 2) (isHermitian_lobattoJacobiMatrix L q a c) f
  calc _ = L 1 * ∑ i, ((isHermitian_lobattoJacobiMatrix L q a c).eigenvectorBasis i 0) ^ 2 *
      f ((isHermitian_lobattoJacobiMatrix L q a c).eigenvalues i) := congrArg (fun x => L 1 * x) h
       _ = _ := ?_
  rw [mul_sum]
  exact sum_congr rfl fun _ _ => by dsimp [lobattoWeights, lobattoNodes]; ring

/-- The actual left Radau node sum integrates all polynomials through degree `2q`.
Source: focused mathematical reroutes, Section 3 (BL5), (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_eq_sum_leftRadauWeights_mul_eval {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (a : ℝ) {p : ℝ[X]} (hp : p.degree < (2 * q + 1 : ℕ)) :
    (∫ x, p.eval x ∂μ) = ∑ i, leftRadauWeights (polynomialIntegral μ hμ) q a i *
      p.eval (leftRadauNodes (polynomialIntegral μ hμ) q a i) := by
  exact (integral_eval_eq_mass_mul_cfc_leftRadauJacobiMatrix hμ q hs a hp).trans
    (by simpa only [polynomialIntegral_apply, eval_one] using
      mass_mul_cfc_leftRadauJacobiMatrix_eq_sum (polynomialIntegral μ hμ) q a p.eval)

/-- The actual right Radau node sum integrates all polynomials through degree `2q`.
Source: focused mathematical reroutes, Section 3 (BL5), (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_eq_sum_rightRadauWeights_mul_eval {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (c : ℝ) {p : ℝ[X]} (hp : p.degree < (2 * q + 1 : ℕ)) :
    (∫ x, p.eval x ∂μ) = ∑ i, rightRadauWeights (polynomialIntegral μ hμ) q c i *
      p.eval (rightRadauNodes (polynomialIntegral μ hμ) q c i) := by
  exact (integral_eval_eq_mass_mul_cfc_rightRadauJacobiMatrix hμ q hs c hp).trans
    (by simpa only [polynomialIntegral_apply, eval_one] using
      mass_mul_cfc_rightRadauJacobiMatrix_eq_sum (polynomialIntegral μ hμ) q c p.eval)

/-- The actual Lobatto node sum integrates all polynomials through degree `2q+1`.
Source: focused mathematical reroutes, Section 3 (BL10), (BL11).
atlas: gauss-radau-lobatto (partial) -/
theorem integral_eval_eq_sum_lobattoWeights_mul_eval {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard)
    (a c : ℝ) {p : ℝ[X]} (hp : p.degree < (2 * q + 2 : ℕ)) :
    (∫ x, p.eval x ∂μ) = ∑ i, lobattoWeights (polynomialIntegral μ hμ) q a c i *
      p.eval (lobattoNodes (polynomialIntegral μ hμ) q a c i) := by
  exact (integral_eval_eq_mass_mul_cfc_lobattoJacobiMatrix hμ q hs a c hp).trans
    (by simpa only [polynomialIntegral_apply, eval_one] using
      mass_mul_cfc_lobattoJacobiMatrix_eq_sum (polynomialIntegral μ hμ) q a c p.eval)

/-- Each actual endpoint rule has total weight equal to the original measure mass,
before any interval or nondegeneracy hypothesis is imposed.
atlas: gauss-radau-lobatto (partial) -/
theorem sum_endpointJacobiWeights (L : ℝ[X] →ₗ[ℝ] ℝ) (q : ℕ) (a c : ℝ) :
    (∑ i, leftRadauWeights L q a i) = L 1 ∧
      (∑ i, rightRadauWeights L q c i) = L 1 ∧ (∑ i, lobattoWeights L q a c i) = L 1 := by
  constructor
  · simp only [leftRadauWeights, ← mul_sum]
    have h : (∑ i, ((isHermitian_leftRadauJacobiMatrix L q a).eigenvectorBasis i 0) ^ 2) = 1 :=
      sum_sq_eigenvectorBasis_apply_zero (Nat.succ_pos q) (isHermitian_leftRadauJacobiMatrix L q a)
    rw [h, mul_one]
  constructor
  · simp only [rightRadauWeights, ← mul_sum]
    have h : (∑ i, ((isHermitian_rightRadauJacobiMatrix L q c).eigenvectorBasis i 0) ^ 2) = 1 :=
      sum_sq_eigenvectorBasis_apply_zero (Nat.succ_pos q) (isHermitian_rightRadauJacobiMatrix L q c)
    rw [h, mul_one]
  · simp only [lobattoWeights, ← mul_sum]
    have h : (∑ i, ((isHermitian_lobattoJacobiMatrix L q a c).eigenvectorBasis i 0) ^ 2) = 1 :=
      sum_sq_eigenvectorBasis_apply_zero (by omega : 0 < q + 2) (isHermitian_lobattoJacobiMatrix L q a c)
    rw [h, mul_one]

end NLAlib
