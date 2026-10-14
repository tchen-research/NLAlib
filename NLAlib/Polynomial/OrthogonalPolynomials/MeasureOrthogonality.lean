import NLAlib.Polynomial.OrthogonalPolynomials.MomentPositivity
import Mathlib.Algebra.Polynomial.Sequence

/-!
# Monic orthogonal families for positive measures

The finite moment construction has exact degrees, spans each degree space, and
is orthogonal and positive precisely before the support termination threshold.
At finite support it gives the terminal node polynomial, with zero squared norm.
Source: Gautschi (2004), Chapter 1; atlas `orthogonal-polynomials-measure-def`.
-/

noncomputable section

open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- The total moment-system polynomials form an exact-degree polynomial sequence.
Orthogonality is a separate theorem requiring nonsingular moment systems. -/
def monicMomentPolynomialSequence {𝕜 : Type*} [Field 𝕜]
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) : Polynomial.Sequence 𝕜 where
  elems' := monicOrthogonalPolynomial L
  degree_eq' n := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L n).ne_zero,
      natDegree_monicOrthogonalPolynomial]

/-- The first `n` monic moment polynomials span the polynomial space of degree
strictly below `n`, including its empty order-zero case. -/
theorem exists_sum_smul_monicOrthogonalPolynomial_eq_of_degree_lt {𝕜 : Type*} [Field 𝕜]
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {p : 𝕜[X]} {n : ℕ} (hp : p.degree < n) :
    ∃ c : ℕ → 𝕜, (∑ j ∈ Finset.range n, c j • monicOrthogonalPolynomial L j) = p := by
  let S := monicMomentPolynomialSequence L
  have hCoeff : ∀ i < n, IsUnit (S i).leadingCoeff := by
    intro i _
    rw [show S i = monicOrthogonalPolynomial L i from rfl,
      (monic_monicOrthogonalPolynomial L i).leadingCoeff]
    exact isUnit_one
  have hmem : p ∈ Polynomial.degreeLT 𝕜 n := Polynomial.mem_degreeLT.mpr hp
  rw [← S.span_degreeLT hCoeff] at hmem
  have hset : Set.Iio n = (Finset.range n : Set ℕ) := by ext i; simp
  rw [hset] at hmem
  exact (Submodule.mem_span_image_finset_iff_exists_fun' 𝕜).mp hmem

/-- The first `n+1` monic moment polynomials span all degree-`n` polynomials,
without any positive-definiteness assumption. Source: triangular monic basis.
atlas: orthogonal-polynomials-measure-def (partial) -/
theorem exists_sum_smul_monicOrthogonalPolynomial_eq_of_degree_le {𝕜 : Type*} [Field 𝕜]
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {p : 𝕜[X]} {n : ℕ} (hp : p.degree ≤ n) :
    ∃ c : ℕ → 𝕜, (∑ j ∈ range (n + 1), c j • monicOrthogonalPolynomial L j) = p := by
  let S := monicMomentPolynomialSequence L
  have hCoeff : ∀ i ≤ n, IsUnit (S i).leadingCoeff := by
    intro i _
    rw [show S i = monicOrthogonalPolynomial L i from rfl,
      (monic_monicOrthogonalPolynomial L i).leadingCoeff]
    exact isUnit_one
  have hmem : p ∈ Polynomial.degreeLE 𝕜 n := Polynomial.mem_degreeLE.mpr hp
  rw [← S.span_degreeLE hCoeff] at hmem
  have hset : Set.Iic n = (Finset.range (n + 1) : Set ℕ) := by ext i; simp
  rw [hset] at hmem
  exact (Submodule.mem_span_image_finset_iff_exists_fun' 𝕜).mp hmem

/-- With at least `n` support points, the canonical measure polynomial of order `n`
is monic and orthogonal to all lower degrees, including the terminal order. -/
theorem isMonicOrthogonalPolynomial_polynomialIntegral (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) :
    IsMonicOrthogonalPolynomial (polynomialIntegral μ hμ) n
      (monicOrthogonalPolynomial (polynomialIntegral μ hμ) n) :=
  isMonicOrthogonalPolynomial_monicOrthogonalPolynomial _
    (hankelMomentDet_ne_zero_of_le_support_encard μ hμ hn)

/-- With at least `n` support points the monic lower-degree orthogonality problem
of order `n` has a unique solution. Source: Gautschi (2004), Chapter 1.
atlas: orthogonal-polynomials-measure-def (partial) -/
theorem existsUnique_isMonicOrthogonalPolynomial_polynomialIntegral (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) :
    ∃! p : ℝ[X], IsMonicOrthogonalPolynomial (polynomialIntegral μ hμ) n p :=
  existsUnique_isMonicOrthogonalPolynomial_of_hankelMomentDet_ne_zero _
    (hankelMomentDet_ne_zero_of_le_support_encard μ hμ hn)

/-- Every monic moment polynomial before support termination has positive squared
integral norm. Source: Gautschi (2004), Chapter 1.
atlas: orthogonal-polynomials-measure-def (partial) -/
theorem orthogonalPolynomialNorm_pos_of_lt_support_encard (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : (n + 1 : ℕ∞) ≤ μ.support.encard) :
    0 < orthogonalPolynomialNorm (polynomialIntegral μ hμ) n := by
  let p := monicOrthogonalPolynomial (polynomialIntegral μ hμ) n
  change 0 < ∫ x, (p ^ 2).eval x ∂μ
  simp only [eval_pow]
  apply integral_sq_eval_pos_of_le_support_encard hn (monic_monicOrthogonalPolynomial _ n).ne_zero
  · rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial _ n).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast (Nat.lt_succ_self n)
  · exact hμ.integrable_sq p

/-- Distinct canonical measure polynomials whose moment systems are nonsingular
are orthogonal. The larger order may be the finite-support terminal order.
Source: Gautschi (2004), Chapter 1.
atlas: orthogonal-polynomials-measure-def (partial) -/
theorem polynomialIntegral_monicOrthogonalPolynomial_mul_eq_zero (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) {i j : ℕ}
    (hi : (i : ℕ∞) ≤ μ.support.encard) (hj : (j : ℕ∞) ≤ μ.support.encard) (hij : i ≠ j) :
    polynomialIntegral μ hμ (monicOrthogonalPolynomial (polynomialIntegral μ hμ) i *
      monicOrthogonalPolynomial (polynomialIntegral μ hμ) j) = 0 := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · rw [mul_comm]
    apply (isMonicOrthogonalPolynomial_polynomialIntegral μ hμ hj).orthogonal
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial _ i).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hij
  · apply (isMonicOrthogonalPolynomial_polynomialIntegral μ hμ hi).orthogonal
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial _ j).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hij

/-- At finite-support termination, the monic moment polynomial is exactly the
node polynomial of the support. This includes the zero measure, whose terminal
polynomial is the empty product one. Source: Gautschi (2004), Chapter 1.
atlas: orthogonal-polynomials-measure-def (partial) -/
theorem monicOrthogonalPolynomial_eq_nodal_support (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (hs : μ.support.Finite) :
    monicOrthogonalPolynomial (polynomialIntegral μ hμ) hs.toFinset.card =
      Lagrange.nodal hs.toFinset id := by
  let n := hs.toFinset.card
  have hn : (n : ℕ∞) ≤ μ.support.encard := by rw [hs.encard_eq_coe_toFinset_card]
  have hp := isMonicOrthogonalPolynomial_polynomialIntegral μ hμ hn
  have hq : IsMonicOrthogonalPolynomial (polynomialIntegral μ hμ) n
      (Lagrange.nodal hs.toFinset id) := by
    refine ⟨Lagrange.nodal_monic, Lagrange.natDegree_nodal, ?_⟩
    intro q _
    change (∫ x, (Lagrange.nodal hs.toFinset id * q).eval x ∂μ) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [μ.support_mem_ae] with x hx
    have hz : (Lagrange.nodal hs.toFinset id).eval x = 0 := by
      simpa only [id_eq] using Lagrange.eval_nodal_at_node
        (s := hs.toFinset) (v := id) (i := x)
        (by simpa only [Set.Finite.mem_toFinset] using hx)
    simp only [eval_mul, hz, zero_mul, Pi.zero_apply]
  exact hp.eq_of_hankelMomentDet_ne_zero hq
    (hankelMomentDet_ne_zero_of_le_support_encard μ hμ hn)

/-- The terminal finite-support monic polynomial has zero squared norm, and is
therefore not normalized into an orthonormal polynomial.
Source: Gautschi (2004), Chapter 1.
atlas: orthogonal-polynomials-measure-def (partial) -/
theorem orthogonalPolynomialNorm_eq_zero_of_finite_support (μ : Measure ℝ)
    (hμ : HasPolynomialMoments μ) (hs : μ.support.Finite) :
    orthogonalPolynomialNorm (polynomialIntegral μ hμ) hs.toFinset.card = 0 := by
  unfold orthogonalPolynomialNorm
  rw [monicOrthogonalPolynomial_eq_nodal_support μ hμ hs]
  change (∫ x, (Lagrange.nodal hs.toFinset id ^ 2).eval x ∂μ) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [μ.support_mem_ae] with x hx
  have hz : (Lagrange.nodal hs.toFinset id).eval x = 0 := by
    simpa only [id_eq] using Lagrange.eval_nodal_at_node
      (s := hs.toFinset) (v := id) (i := x)
      (by simpa only [Set.Finite.mem_toFinset] using hx)
  simp only [eval_pow, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), Pi.zero_apply]

end NLAlib
