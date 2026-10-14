import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMatrix
import NLAlib.Polynomial.Quadrature.MomentGauss
import NLAlib.Polynomial.Quadrature.MeasureExactness

/-! # Canonical Gauss rules for positive measures

The finite moment Jacobi matrix constructs real, distinct zeros of the canonical
monic orthogonal polynomial. Integrating the corresponding cardinal polynomials
gives actual positive Gauss weights and a rule unique by its first `2n` moments.
Source: Gautschi (2004), Theorems 1.19, 1.22 and 1.46; operator derivations AQ1–AQ2.
-/

noncomputable section

open Polynomial MeasureTheory Finset Set
open scoped Matrix

namespace NLAlib

/-- Canonical real Gauss nodes from the Hermitian moment Jacobi matrix. The
definition is total; distinct orthogonal roots require at least `n` support points. -/
def gaussNodes (μ : Measure ℝ) (hμ : HasPolynomialMoments μ) (n : ℕ) : Fin n → ℝ :=
  momentGaussNodes (polynomialIntegral μ hμ) n

/-- Canonical Gauss weights, obtained by integrating the node cardinal
polynomials. Positivity and degree-`2n−1` exactness require support nondegeneracy. -/
def gaussWeights (μ : Measure ℝ) (hμ : HasPolynomialMoments μ) (n : ℕ) : Fin n → ℝ :=
  momentGaussWeights (polynomialIntegral μ hμ) n

private theorem measure_hankel_nonzero {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) (k : ℕ) (hk : k ≤ n) :
    hankelMomentDet (polynomialIntegral μ hμ) k ≠ 0 :=
  hankelMomentDet_ne_zero_of_le_support_encard μ hμ
    ((by exact_mod_cast hk : (k : ℕ∞) ≤ n).trans hn)

private theorem measure_norm_pos {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) (k : ℕ) (hk : k < n) :
    0 < orthogonalPolynomialNorm (polynomialIntegral μ hμ) k :=
  orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
    ((by exact_mod_cast (Nat.succ_le_of_lt hk) : (k + 1 : ℕ∞) ≤ n).trans hn)

/-- Canonical Gauss nodes are distinct whenever there are at least as many
support points as nodes, including a terminal atomic rule.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial), gauss-quadrature-general-measure (partial) -/
theorem gaussNodes_injective {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ}
    (hn : (n : ℕ∞) ≤ μ.support.encard) : Function.Injective (gaussNodes μ hμ n) :=
  eigenvalues_orthogonalPolynomialJacobiMatrix_injective _
    (measure_hankel_nonzero hμ hn) (measure_norm_pos hμ hn)

/-- The product of the actual real Gauss-node factors is exactly the canonical
monic orthogonal polynomial, including finite-support termination.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial), gauss-quadrature-general-measure (partial) -/
theorem nodal_gaussNodes_eq_monicOrthogonalPolynomial {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) :
    Lagrange.nodal univ (gaussNodes μ hμ n) =
      monicOrthogonalPolynomial (polynomialIntegral μ hμ) n := by
  rw [← charpoly_orthogonalPolynomialJacobiMatrix _
    (measure_hankel_nonzero hμ hn) (measure_norm_pos hμ hn)]
  simpa [Lagrange.nodal_eq, gaussNodes, momentGaussNodes] using
    (isHermitian_orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n).charpoly_eq.symm

/-- The zeros of the canonical monic polynomial are exactly the constructed
Gauss nodes. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) (x : ℝ) :
    (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).eval x = 0 ↔
      ∃ i : Fin n, gaussNodes μ hμ n i = x := by
  rw [← nodal_gaussNodes_eq_monicOrthogonalPolynomial hμ hn]
  simp only [Lagrange.nodal_eq, eval_prod, eval_sub, eval_X, eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, (sub_eq_zero.mp hi).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, sub_eq_zero.mpr hi.symm⟩

/-- The constructed `n`-node Gauss rule integrates every polynomial of degree
below `2n`. No pre-existing node or quadrature certificate is assumed.
Source: Gautschi (2004), Theorem 1.46.
atlas: quadrature-exactness-characterisation (partial), gauss-quadrature-general-measure (partial) -/
theorem integral_eval_eq_sum_gaussWeights_mul_eval {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {p : ℝ[X]} (hp : p.degree < (2 * n : ℕ)) :
    (∫ x, p.eval x ∂μ) = ∑ i : Fin n, gaussWeights μ hμ n i * p.eval (gaussNodes μ hμ n i) := by
  have he := (polynomial_gauss_exactness_iff (polynomialIntegral μ hμ)
    (s := univ) (by exact ⟨⟨0, hn0⟩, mem_univ _⟩)
    (gaussNodes_injective hμ hn).injOn (gaussWeights μ hμ n)).mpr
    ⟨fun i _ => rfl, by
      rw [nodal_gaussNodes_eq_monicOrthogonalPolynomial hμ hn]
      simpa only [card_univ, Fintype.card_fin] using
        isMonicOrthogonalPolynomial_polynomialIntegral μ hμ hn⟩
  simpa only [polynomialIntegral_apply, card_univ, Fintype.card_fin] using he p (by simpa using hp)

/-- Every constructed Gauss weight is strictly positive, including a terminal
finite atomic rule. Source: Gautschi (2004), Theorem 1.46.
atlas: quadrature-exactness-characterisation (partial), gauss-quadrature-general-measure (partial), orthogonal-polynomial-zeros (partial) -/
theorem gaussWeights_pos {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ}
    (hn : (n : ℕ∞) ≤ μ.support.encard) (i : Fin n) : 0 < gaussWeights μ hμ n i :=
  quadrature_weight_pos_of_gauss_exact hμ hn (gaussNodes_injective hμ hn) _
    (fun _ hp => integral_eval_eq_sum_gaussWeights_mul_eval hμ (by have := i.isLt; omega) hn hp) i

/-- The constructed Gauss weights sum to the measure's total mass.
Source: Gautschi (2004), Theorem 1.46.
atlas: gauss-quadrature-general-measure (partial) -/
theorem sum_gaussWeights_eq_measure_univ {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {n : ℕ} (hn0 : 0 < n) (hn : (n : ℕ∞) ≤ μ.support.encard) :
    (∑ i : Fin n, gaussWeights μ hμ n i) = (μ univ).toReal := by
  have h := integral_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn (p := 1) (by
    simp only [degree_one]
    exact_mod_cast (show 0 < 2 * n by omega))
  simpa [measureReal_def] using h.symm

/-- Any distinct-node rule matching the first `2n` moments is exactly the actual
constructed Gauss rule, up to node permutation. Positivity of its weights is a
consequence, not an additional assumption.
Source: Gautschi (2004), Gauss-rule characterization.
atlas: quadrature-exactness-characterisation (partial) -/
theorem rule_eq_gaussNodes_gaussWeights_of_moments {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) (v w : Fin n → ℝ) (hv : Function.Injective v)
    (hm : ∀ k < 2 * n, (∫ x, x ^ k ∂μ) = ∑ i, w i * v i ^ k) :
    ∃ e : Equiv.Perm (Fin n), (∀ i, v (e i) = gaussNodes μ hμ n i) ∧
      (∀ i, w (e i) = gaussWeights μ hμ n i) := by
  apply quadrature_rule_eq_up_to_permutation_of_moments hμ hn0 hn
    (gaussNodes μ hμ n) v (gaussWeights μ hμ n) w (gaussNodes_injective hμ hn) hv
  · intro k hk
    simpa only [eval_pow, eval_X] using
      integral_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn (p := X ^ k) (by
        rw [degree_X_pow]
        exact_mod_cast hk)
  · exact hm

end NLAlib
