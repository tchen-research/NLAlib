import NLAlib.ForMathlib.LinearAlgebra.LagrangeQuadrature
import NLAlib.Polynomial.OrthogonalPolynomials.Basic
import NLAlib.Polynomial.OrthogonalPolynomials.Uniqueness
import Mathlib.Data.Real.Basic

/-! # Exactness and intrinsic Gauss-rule characterization

Polynomial division characterizes the exactness of an evaluation rule and
identifies Gauss exactness with the monic nodal polynomial's orthogonality.
Strict positivity of the square of that nodal polynomial excludes degree `2n`.
Source: Gautschi (2004), Chapter 1; operator derivations AQ1–AQ2.
-/

noncomputable section

open Polynomial Finset Set

namespace NLAlib

variable {𝕜 ι : Type*} [Field 𝕜] [DecidableEq ι]

/-- A rule exact through degree `2n−1` is precisely the interpolatory rule whose
monic nodal polynomial is degree-`n` orthogonal for the same functional.
Source: Gautschi (2004), quadrature characterization; operator derivations AQ1.
atlas: quadrature-exactness-characterisation (partial) -/
theorem polynomial_gauss_exactness_iff (L : 𝕜[X] →ₗ[𝕜] 𝕜)
    {s : Finset ι} (hs : s.Nonempty) {v : ι → 𝕜} (hv : InjOn v s) (w : ι → 𝕜) :
    (∀ p : 𝕜[X], p.degree < (2 * s.card : ℕ) →
      L p = ∑ i ∈ s, w i * p.eval (v i)) ↔
      (∀ i ∈ s, w i = L (Lagrange.basis s v i)) ∧
        IsMonicOrthogonalPolynomial L s.card (Lagrange.nodal s v) := by
  rw [show 2 * s.card = s.card + s.card by omega,
    Lagrange.linearMap_eq_sum_weighted_eval_iff L hs hv]
  constructor
  · rintro ⟨hw, ho⟩
    exact ⟨hw, Lagrange.nodal_monic, Lagrange.natDegree_nodal, ho⟩
  · rintro ⟨hw, ho⟩
    exact ⟨hw, ho.orthogonal⟩

end NLAlib

namespace Lagrange

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- A rule cannot integrate the square of its nodal polynomial when the
functional is strictly positive on that square. This is the exact degree-`2n`
obstruction, with no positivity assertion at a terminal zero norm.
Source: Gautschi (2004), maximal degree of Gauss quadrature; AQ2. -/
theorem not_linearMap_eq_sum_weighted_eval_of_nodal_sq_pos
    (L : ℝ[X] →ₗ[ℝ] ℝ) (s : Finset ι) (v w : ι → ℝ)
    (hpos : 0 < L (nodal s v ^ 2)) :
    ¬ (∀ p : ℝ[X], p.degree ≤ (2 * s.card : ℕ) →
      L p = ∑ i ∈ s, w i * p.eval (v i)) := by
  intro h
  have hdeg : (nodal s v ^ 2).degree ≤ (2 * s.card : ℕ) := by
    rw [degree_pow, degree_nodal]
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact le_rfl
  have hz := h (nodal s v ^ 2) hdeg
  have hsum : (∑ i ∈ s, w i * (nodal s v ^ 2).eval (v i)) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [eval_pow, eval_nodal_at_node hi]
    simp
  rw [hsum] at hz
  exact (ne_of_gt hpos) hz

/-- Exactness on degrees below twice the node count identifies every weight
with the functional of the squared cardinal polynomial.
Source: Gautschi (2004), positivity of Gauss weights; operator derivations AQ2. -/
theorem weight_eq_linearMap_basis_sq_of_exact
    (L : ℝ[X] →ₗ[ℝ] ℝ) {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s) (w : ι → ℝ)
    (h : ∀ p : ℝ[X], p.degree < (2 * s.card : ℕ) →
      L p = ∑ j ∈ s, w j * p.eval (v j)) {i : ι} (hi : i ∈ s) :
    w i = L (Lagrange.basis s v i ^ 2) := by
  have hn : 0 < s.card := (card_pos.mpr ⟨i, hi⟩)
  have hd : (Lagrange.basis s v i ^ 2).degree < (2 * s.card : ℕ) := by
    rw [degree_pow, degree_basis hv hi]
    simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using
      (show ((2 * (s.card - 1) : ℕ) : WithBot ℕ) < (2 * s.card : ℕ)
        from Nat.cast_lt.mpr (by omega))
  have he := h (Lagrange.basis s v i ^ 2) hd
  rw [sum_eq_single i] at he
  · simpa only [eval_pow, eval_basis_self hv hi, one_pow, mul_one] using he.symm
  · intro j hj hji
    rw [eval_pow, eval_basis_of_ne hji.symm hj]
    simp
  · exact fun hnot => (hnot hi).elim

end Lagrange

namespace NLAlib

/-- Two rules of Gauss degree for a nondegenerate polynomial functional agree
up to a permutation of their distinct nodes and weights. Positivity is needed
only through the nonzero square condition below the node count.
Source: Gautschi (2004), uniqueness of Gauss quadrature; operator derivations AQ1–AQ2.
atlas: quadrature-exactness-characterisation (partial) -/
theorem polynomial_gauss_rule_eq_up_to_permutation {n : ℕ} (hn : 0 < n)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (v u w a : Fin n → ℝ)
    (hv : Function.Injective v) (hu : Function.Injective u)
    (hL : ∀ r : ℝ[X], r.degree < n → r ≠ 0 → L (r ^ 2) ≠ 0)
    (hw : ∀ p : ℝ[X], p.degree < (2 * n : ℕ) → L p = ∑ i, w i * p.eval (v i))
    (ha : ∀ p : ℝ[X], p.degree < (2 * n : ℕ) → L p = ∑ i, a i * p.eval (u i)) :
    ∃ e : Equiv.Perm (Fin n), (∀ i, u (e i) = v i) ∧ (∀ i, a (e i) = w i) := by
  have hs : (univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, mem_univ _⟩
  have hw' : ∀ p : ℝ[X], p.degree < (2 * (univ : Finset (Fin n)).card : ℕ) →
      L p = ∑ i ∈ univ, w i * p.eval (v i) := by simpa using hw
  have ha' : ∀ p : ℝ[X], p.degree < (2 * (univ : Finset (Fin n)).card : ℕ) →
      L p = ∑ i ∈ univ, a i * p.eval (u i) := by simpa using ha
  obtain ⟨hweights, hp⟩ := (polynomial_gauss_exactness_iff L hs hv.injOn w).mp hw'
  obtain ⟨_, hq⟩ := (polynomial_gauss_exactness_iff L hs hu.injOn a).mp ha'
  have heq : Lagrange.nodal univ v = Lagrange.nodal univ u :=
    hp.eq_of_nonzero_sq hq (by simpa using hL)
  have hnode : ∀ i, ∃ j, u j = v i := by
    intro i
    have hz : (Lagrange.nodal univ u).eval (v i) = 0 := by
      rw [← heq, Lagrange.eval_nodal_at_node (mem_univ i)]
    simp only [Lagrange.nodal, eval_prod, eval_sub, eval_X, eval_C] at hz
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hz
    exact ⟨j, (sub_eq_zero.mp hj).symm⟩
  choose g hg using hnode
  have hginj : Function.Injective g := by
    intro i j hij
    apply hv
    rw [← hg i, ← hg j, hij]
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective g
    ⟨hginj, (Finite.injective_iff_surjective).mp hginj⟩
  have he : ∀ i, u (e i) = v i := hg
  refine ⟨e, he, fun i => ?_⟩
  have hdeg : (Lagrange.basis univ v i).degree < (2 * n : ℕ) := by
    rw [Lagrange.degree_basis hv.injOn (mem_univ i)]
    simp only [card_univ, Fintype.card_fin]
    exact_mod_cast (show n - 1 < 2 * n by omega)
  have h := ha (Lagrange.basis univ v i) hdeg
  rw [sum_eq_single (e i)] at h
  · rw [he i, Lagrange.eval_basis_self hv.injOn (mem_univ i), mul_one] at h
    exact h.symm.trans (hweights i (mem_univ i)).symm
  · intro j hj hji
    have hjv : u j = v (e.symm j) := by simpa using he (e.symm j)
    have hne : i ≠ e.symm j := by
      intro hij
      apply hji
      rw [hij, e.apply_symm_apply]
    rw [hjv, Lagrange.eval_basis_of_ne hne (mem_univ _), mul_zero]
  · simp

end NLAlib
