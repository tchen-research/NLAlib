import NLAlib.Polynomial.OrthogonalPolynomials.Basic
import NLAlib.Polynomial.Quadrature.GeneralMeasure
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive polynomial moment functionals

Polynomial integrability supplies a linear moment functional. Vanishing squared
integral is equivalent to vanishing on the topological measure support, and finite
support cardinality exactly controls positive definiteness of bounded-degree spaces.
Source: Gautschi (2004), Chapter 1; atlas `orthogonal-polynomials-measure-def`.
-/

noncomputable section

open Polynomial MeasureTheory Set Finset

namespace NLAlib

set_option backward.isDefEq.respectTransparency false

/-- Every polynomial is integrable against the measure. This is equivalent to finite
absolute moments of every natural order, including finite total mass at order zero.
Source: Gautschi (2004), Section 1.1. -/
def HasPolynomialMoments (μ : Measure ℝ) : Prop := ∀ p : ℝ[X], Integrable p.eval μ

/-- Finite polynomial moments include the constant moment and therefore force
finite total measure. This supplies the native finite-measure instance in
compact-support polynomial and Stieltjes consumers. -/
theorem HasPolynomialMoments.isFiniteMeasure {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) :
    IsFiniteMeasure μ := by
  apply (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1:ℝ) ≠ 0)).mp
  simpa only [eval_one] using (hμ (1 : ℝ[X]))

/-- Finite polynomial moments make the squared evaluation of every polynomial integrable. -/
theorem HasPolynomialMoments.integrable_sq {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    (p : ℝ[X]) : Integrable (fun x => (p.eval x) ^ 2) μ := by
  have hp : (p ^ 2).eval = fun x => (p.eval x) ^ 2 := by
    funext x
    exact eval_pow 2
  rw [← hp]
  exact hμ (p ^ 2)

/-- Polynomial integrability is equivalent to integrability of all monomials.
Source: finite coefficient expansion of a polynomial. -/
theorem hasPolynomialMoments_iff_integrable_pow (μ : Measure ℝ) :
    HasPolynomialMoments μ ↔ ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ := by
  constructor
  · intro h k
    simpa only [eval_pow, eval_X] using h (X ^ k)
  · intro h p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [show (p + q).eval = p.eval + q.eval by funext x; exact eval_add]
      exact hp.add hq
    | monomial k c => simpa only [eval_monomial] using (h k).const_mul c

/-- The monomial moment condition equals integrability of all absolute powers.
Source: the norm criterion for integrability. -/
theorem hasPolynomialMoments_iff_integrable_abs_pow (μ : Measure ℝ) :
    HasPolynomialMoments μ ↔ ∀ k : ℕ, Integrable (fun x : ℝ => |x| ^ k) μ := by
  rw [hasPolynomialMoments_iff_integrable_pow]
  apply forall_congr'
  intro k
  simpa only [Real.norm_eq_abs, abs_pow] using
    (integrable_norm_iff (μ := μ) (f := fun x : ℝ => x ^ k) (by fun_prop)).symm

/-- A finite measure concentrated on a compact real interval has all polynomial moments.
Source: compactly supported polynomial integrability. -/
theorem hasPolynomialMoments_of_ae_mem_Icc {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) : HasPolynomialMoments μ :=
  fun p => integrable_eval_of_ae_mem_Icc hμ p

/-- Integration of polynomial evaluation is a linear moment functional when polynomial
moments are finite. Source: Gautschi (2004), Section 1.1. -/
def polynomialIntegral (μ : Measure ℝ) (hμ : HasPolynomialMoments μ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x, p.eval x ∂μ
  map_add' p q := by
    simpa only [eval_add] using integral_add (hμ p) (hμ q)
  map_smul' c p := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c p.eval

/-- Evaluating the moment functional is integration of polynomial evaluation. -/
@[simp] theorem polynomialIntegral_apply (μ : Measure ℝ) (hμ : HasPolynomialMoments μ)
    (p : ℝ[X]) : polynomialIntegral μ hμ p = ∫ x, p.eval x ∂μ := rfl

/-- The bilinear moment pairing is the integral of the product of evaluations. -/
theorem polynomialIntegral_mul (μ : Measure ℝ) (hμ : HasPolynomialMoments μ) (p q : ℝ[X]) :
    polynomialIntegral μ hμ (p * q) = ∫ x, p.eval x * q.eval x ∂μ := by
  simp only [polynomialIntegral_apply, eval_mul]

/-- A polynomial with integrable square has zero squared integral exactly when it
vanishes on the measure support. Only this square's integrability is required.
Source: Gautschi (2004), Section 1.1, support nondegeneracy. -/
theorem integral_sq_eval_eq_zero_iff {μ : Measure ℝ} (p : ℝ[X])
    (hp : Integrable (fun x => (p.eval x) ^ 2) μ) :
    (∫ x, (p.eval x) ^ 2 ∂μ) = 0 ↔ ∀ x ∈ μ.support, p.eval x = 0 := by
  constructor
  · intro hzero
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (p.eval x)) hp).mp hzero
    have hsup : μ.support ⊆ {x | p.eval x = 0} := by
      apply Measure.support_subset_of_isClosed (isClosed_eq p.continuous continuous_const)
      filter_upwards [hae] with x hx
      simpa only [Pi.zero_apply, sq_eq_zero_iff] using hx
    exact hsup
  · intro hs
    apply integral_eq_zero_of_ae
    filter_upwards [μ.support_mem_ae] with x hx
    simp only [hs x hx, zero_pow (by decide : (2 : ℕ) ≠ 0), Pi.zero_apply]

/-- At least `n` support points give positive squared integral for every nonzero
polynomial of degree below `n`. The support cardinal is extended, so infinite
support requires no separate convention. Only this square's integrability is required.
Source: Gautschi (2004), Section 1.1. -/
theorem integral_sq_eval_pos_of_le_support_encard {μ : Measure ℝ} {n : ℕ}
    (hn : (n : ℕ∞) ≤ μ.support.encard) {p : ℝ[X]} (hp0 : p ≠ 0)
    (hp : p.degree < n) (hi : Integrable (fun x => (p.eval x) ^ 2) μ) :
    0 < ∫ x, (p.eval x) ^ 2 ∂μ := by
  apply lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg (p.eval x)))
  intro heq
  have hs := (integral_sq_eval_eq_zero_iff p hi).mp heq.symm
  have hsub : μ.support ⊆ (p.roots.toFinset : Set ℝ) := by
    intro x hx
    simpa only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp0, IsRoot.def] using hs x hx
  have hcard : p.roots.toFinset.card ≤ p.natDegree :=
    (Multiset.toFinset_card_le _).trans (card_roots' p)
  have hdeg : p.natDegree < n := (natDegree_lt_iff_degree_lt hp0).mpr hp
  have hle : (n : ℕ∞) ≤ p.natDegree := hn.trans
    ((encard_mono hsub).trans (by exact_mod_cast hcard))
  exact (not_le_of_gt hdeg) (by exact_mod_cast hle)

/-- Positive definiteness of the polynomial integral form below degree `n` is
equivalent to having at least `n` support points, including zero measure and
the empty polynomial space. Source: Gautschi (2004), Section 1.1.
atlas: orthogonal-polynomials-measure-def (partial) -/
theorem integral_sq_eval_pos_iff_le_support_encard (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (n : ℕ) :
    (∀ p : ℝ[X], p.degree < n → p ≠ 0 → 0 < ∫ x, (p.eval x) ^ 2 ∂μ) ↔
      (n : ℕ∞) ≤ μ.support.encard := by
  constructor
  · intro hpos
    by_contra hnot
    have hlt : μ.support.encard < n := lt_of_not_ge hnot
    have hfin : μ.support.Finite := finite_of_encard_le_coe hlt.le
    let s := hfin.toFinset
    have hcard : s.card < n := by
      simpa only [s, hfin.encard_eq_coe_toFinset_card, Nat.cast_lt] using hlt
    let p : ℝ[X] := Lagrange.nodal s id
    have hp : p.Monic := Lagrange.nodal_monic
    have hdeg : p.degree < n := by
      rw [show p = Lagrange.nodal s id from rfl, Lagrange.degree_nodal]
      exact_mod_cast hcard
    have hi := hμ.integrable_sq p
    have hz : (∫ x, (p.eval x) ^ 2 ∂μ) = 0 :=
      (integral_sq_eval_eq_zero_iff p hi).mpr (fun x hx =>
        Lagrange.eval_nodal_at_node (s := s) (v := id) (i := x)
          (by simpa only [s, Set.Finite.mem_toFinset] using hx))
    have h := hpos p hdeg hp.ne_zero
    rw [hz] at h
    exact lt_irrefl _ h
  · intro hn p hp hp0
    apply integral_sq_eval_pos_of_le_support_encard hn hp0 hp
    exact hμ.integrable_sq p

end NLAlib
