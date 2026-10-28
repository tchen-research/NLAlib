import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationSmallSystem
import Mathlib.LinearAlgebra.Lagrange

/-!
# Root and Cauchy rows of rational modification

For distinct numerator roots, evaluation is equivalent to numerator divisibility.
For distinct denominator roots, the cofactor polynomials form a basis of the
lower-degree space. Their inverse-weight moments are exactly the Cauchy rows
after the denominator is cancelled. This works over any field, including complex
roots, rather than requiring all roots of a real polynomial to be real.
Source: Gautschi (2004), Theorems 2.52--2.53.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜] {l m : ℕ}

/-- The denominator with one simple linear factor removed. -/
def rootCofactor (z : Fin m → 𝕜) (i : Fin m) : 𝕜[X] :=
  ∏ j ∈ (Finset.univ : Finset (Fin m)).erase i, (X-C (z j))

/-- Vanishing at every distinct node is exactly divisibility by its nodal polynomial. -/
theorem nodal_dvd_iff_forall_eval_eq_zero (z : Fin l → 𝕜) (hz : Function.Injective z)
    (P : 𝕜[X]) :
    Lagrange.nodal Finset.univ z ∣ P ↔ ∀ i, P.eval (z i) = 0 := by
  constructor
  · rintro ⟨Q, rfl⟩ i
    rw [eval_mul, Lagrange.eval_nodal_at_node (Finset.mem_univ i), zero_mul]
  · intro h
    apply EuclideanDomain.mod_eq_zero.mp
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hz.injOn
    · simpa only [Lagrange.degree_nodal, Finset.card_univ, Fintype.card_fin] using
        (degree_mod_lt P (Lagrange.nodal_ne_zero (s := Finset.univ) (v := z)))
    · intro i _
      have he := congrArg (fun q : 𝕜[X] => q.eval (z i))
        (EuclideanDomain.div_add_mod P (Lagrange.nodal Finset.univ z))
      simpa only [eval_add, eval_mul,
        Lagrange.eval_nodal_at_node (Finset.mem_univ i), zero_mul, zero_add, h i] using he

/-- Lagrange interpolation written in the unnormalized cofactor basis. -/
theorem eq_sum_C_mul_rootCofactor (z : Fin m → 𝕜) (hz : Function.Injective z)
    {q : 𝕜[X]} (hq : q.degree < m) :
    q = ∑ i : Fin m, C (q.eval (z i) / (rootCofactor z i).eval (z i)) * rootCofactor z i := by
  have h := Lagrange.eq_interpolate (s := Finset.univ) hz.injOn
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hq)
  rw [Lagrange.interpolate_eq_sum] at h
  simpa only [rootCofactor, eval_prod, eval_sub, eval_X, eval_C] using h

/-- Vanishing of the cofactor moments is exactly orthogonality against every
polynomial below the denominator degree. -/
theorem forall_rootCofactor_moment_eq_zero_iff (T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (z : Fin m → 𝕜) (hz : Function.Injective z) (P : 𝕜[X]) :
    (∀ i, T (P * rootCofactor z i) = 0) ↔
      ∀ q : 𝕜[X], q.degree < m → T (P*q) = 0 := by
  constructor
  · intro h q hq
    rw [eq_sum_C_mul_rootCofactor z hz hq, mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [show P * (C _ * rootCofactor z i) = C _ * (P * rootCofactor z i) by ring,
      C_mul', map_smul, h i, smul_zero]
  · intro h i
    apply h
    have hi : i ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ i
    have hdeg := Lagrange.degree_nodal (s := Finset.univ.erase i) (v := z)
    change (Lagrange.nodal (Finset.univ.erase i) z).degree < _
    rw [hdeg, Finset.card_erase_of_mem hi, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (show m-1 < m by have := i.isLt; omega)

/-- The source evaluation/Cauchy rows and the native coefficient/moment rows
have precisely the same kernel. No assumption that roots are real is used.
atlas: christoffel-uvarov-modification (partial) -/
theorem rationalModification_root_constraints_iff (T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (x : Fin l → 𝕜) (z : Fin m → 𝕜) (hx : Function.Injective x)
    (hz : Function.Injective z) (P : 𝕜[X]) :
    ((∀ i, P.eval (x i) = 0) ∧ (∀ i, T (P * rootCofactor z i) = 0)) ↔
      ∀ i, rationalModificationConstraint T (Lagrange.nodal Finset.univ x) m i P = 0 := by
  rw [rationalModificationConstraint_eq_zero_iff T Lagrange.nodal_ne_zero,
    nodal_dvd_iff_forall_eval_eq_zero x hx, forall_rootCofactor_moment_eq_zero_iff T z hz]
  constructor
  · rintro ⟨hu, hm⟩
    exact ⟨hu, fun i => hm (X^i.val) (by rw [degree_X_pow]; exact_mod_cast i.isLt)⟩
  · rintro ⟨hu, hm⟩
    exact ⟨hu, fun q hq => functional_mul_eq_zero_of_monomial_tests T hm hq⟩

end NLAlib
