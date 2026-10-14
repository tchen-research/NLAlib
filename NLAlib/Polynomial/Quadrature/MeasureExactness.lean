import NLAlib.Polynomial.Quadrature.ExactnessCharacterization
import NLAlib.Polynomial.OrthogonalPolynomials.MeasureMoments

/-! # Exactness and uniqueness for polynomial-moment measures

The polynomial-functional division criterion applies to the actual measure
integral. Support cardinality proves positive weights and maximal degree;
moment matching identifies any competing rule up to permutation.
Source: Gautschi (2004), quadrature characterization; operator derivations AQ1–AQ2.
-/

noncomputable section

open Polynomial MeasureTheory Set Finset

namespace NLAlib

/-- A real rule's polynomial exactness is equivalent to the corresponding
finite list of monomial moment identities. -/
theorem polynomial_rule_exact_iff_moments (L : ℝ[X] →ₗ[ℝ] ℝ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v w : ι → ℝ) (d : ℕ) :
    (∀ p : ℝ[X], p.degree < d → L p = ∑ i ∈ s, w i * p.eval (v i)) ↔
      (∀ k < d, L (X ^ k) = ∑ i ∈ s, w i * v i ^ k) := by
  let Q : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := fun p => ∑ i ∈ s, w i * p.eval (v i)
      map_add' := by intro p q; simp [mul_add, sum_add_distrib]
      map_smul' := by
        intro c p
        simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        ring }
  simpa only [Q, LinearMap.coe_mk, AddHom.coe_mk, eval_pow, eval_X] using
    Polynomial.linearMap_eq_of_degree_lt_iff_pow L Q d

/-- Exactness through degree `#s−1+k` is exactly the integrated-cardinal weight
condition together with nodal orthogonality through degree `k−1`.
Source: Gautschi (2004), characterization; operator derivations AQ1.
atlas: quadrature-exactness-characterisation (partial) -/
theorem integral_eq_quadrature_iff {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (hs : s.Nonempty)
    {v : ι → ℝ} (hv : InjOn v s) (w : ι → ℝ) (k : ℕ) :
    (∀ p : ℝ[X], p.degree < (s.card + k : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i ∈ s, w i * p.eval (v i)) ↔
      (∀ i ∈ s, w i = ∫ x, (Lagrange.basis s v i).eval x ∂μ) ∧
        (∀ q : ℝ[X], q.degree < k →
          (∫ x, (Lagrange.nodal s v).eval x * q.eval x ∂μ) = 0) := by
  simpa only [polynomialIntegral_apply, eval_mul] using
    Lagrange.linearMap_eq_sum_weighted_eval_iff (polynomialIntegral μ hμ) hs hv w k

/-- A positive measure with more than `n` support points admits no `n`-node
rule exact through degree `2n`. The terminal `n`-atom case is excluded precisely
by the support premise. Source: Gautschi (2004), maximal Gauss degree; AQ2.
atlas: quadrature-exactness-characterisation (partial) -/
theorem not_integral_eq_quadrature_degree_two_mul {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ}
    (hn : (n + 1 : ℕ∞) ≤ μ.support.encard) (v w : Fin n → ℝ) :
    ¬ (∀ p : ℝ[X], p.degree ≤ (2 * n : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i)) := by
  have hpos : 0 < polynomialIntegral μ hμ (Lagrange.nodal univ v ^ 2) := by
    simp only [polynomialIntegral_apply, eval_pow]
    apply integral_sq_eval_pos_of_le_support_encard hn Lagrange.nodal_ne_zero
    · rw [Lagrange.degree_nodal]
      simp only [card_univ, Fintype.card_fin]
      exact_mod_cast Nat.lt_succ_self n
    · exact hμ.integrable_sq _
  simpa only [polynomialIntegral_apply, card_univ, Fintype.card_fin] using
    Lagrange.not_linearMap_eq_sum_weighted_eval_of_nodal_sq_pos
      (polynomialIntegral μ hμ) univ v w hpos

/-- Gauss-degree exactness against a measure with at least as many support
points gives strictly positive weights, including a terminal atomic rule.
Source: Gautschi (2004), positivity of Gauss weights; operator derivations AQ2.
atlas: quadrature-exactness-characterisation (partial) -/
theorem quadrature_weight_pos_of_gauss_exact {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {v : Fin n → ℝ} (hv : Function.Injective v) (w : Fin n → ℝ)
    (he : ∀ p : ℝ[X], p.degree < (2 * n : ℕ) →
      (∫ x, p.eval x ∂μ) = ∑ i, w i * p.eval (v i)) (i : Fin n) : 0 < w i := by
  have hw := Lagrange.weight_eq_linearMap_basis_sq_of_exact
    (polynomialIntegral μ hμ) hv.injOn w (by simpa using he) (mem_univ i)
  rw [hw, polynomialIntegral_apply]
  simp only [eval_pow]
  apply integral_sq_eval_pos_of_le_support_encard hn (Lagrange.basis_ne_zero hv.injOn (mem_univ i))
  · rw [Lagrange.degree_basis hv.injOn (mem_univ i)]
    simp only [card_univ, Fintype.card_fin]
    exact_mod_cast (show n - 1 < n by have := i.isLt; omega)
  · exact hμ.integrable_sq _

/-- Matching the first `2n` moments forces two distinct-node rules for the same
measure to agree up to permutation. Positivity of the competing weights need
not be assumed: it follows from their moment exactness.
Source: Gautschi (2004), uniqueness of Gauss measure; operator derivations AQ2.
atlas: quadrature-exactness-characterisation (partial) -/
theorem quadrature_rule_eq_up_to_permutation_of_moments {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) (v u w a : Fin n → ℝ)
    (hv : Function.Injective v) (hu : Function.Injective u)
    (hw : ∀ k < 2 * n, (∫ x, x ^ k ∂μ) = ∑ i, w i * v i ^ k)
    (ha : ∀ k < 2 * n, (∫ x, x ^ k ∂μ) = ∑ i, a i * u i ^ k) :
    ∃ e : Equiv.Perm (Fin n), (∀ i, u (e i) = v i) ∧ (∀ i, a (e i) = w i) := by
  apply polynomial_gauss_rule_eq_up_to_permutation hn0 (polynomialIntegral μ hμ) v u w a hv hu
  · intro r hr hr0
    simpa only [polynomialIntegral_apply, eval_pow] using
      (integral_sq_eval_pos_of_le_support_encard hn hr0 hr (hμ.integrable_sq r)).ne'
  · apply (polynomial_rule_exact_iff_moments (polynomialIntegral μ hμ) univ v w (2 * n)).mpr
    simpa only [polynomialIntegral_apply, eval_pow, eval_X] using hw
  · apply (polynomial_rule_exact_iff_moments (polynomialIntegral μ hμ) univ u a (2 * n)).mpr
    simpa only [polynomialIntegral_apply, eval_pow, eval_X] using ha

end NLAlib
