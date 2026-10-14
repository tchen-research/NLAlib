import NLAlib.Polynomial.OrthogonalPolynomials.Christoffel
import NLAlib.Polynomial.OrthogonalPolynomials.PositiveMomentFunctional
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# The finite rational-modification constraint system

Remainder coefficients enforce numerator divisibility, and inverse-weight
moments enforce modified orthogonality. The actual coefficient matrix is
nonsingular under finite modified nondegeneracy, hence under the source square
positivity. No denominator degree or root-splitting assumption enters the proof.
Source: focused rational-modification reroute, Section 4 (CU1)--(CU3).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Polynomial Finset Matrix

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- One row of the native rational-modification constraint system. The first
`degree u` rows are coefficients of the field remainder, and the next `n` rows
are inverse-weight moment constraints. The definition is total even at `u=0`. -/
def rationalModificationConstraint (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ)
    (i : Fin (u.natDegree + n)) : 𝕜[X] →ₗ[𝕜] 𝕜 :=
  if i.val < u.natDegree then
    (Polynomial.lcoeff 𝕜 i.val).comp (Polynomial.modByMonicHom (u * C u.leadingCoeff⁻¹))
  else polynomialWeightedFunctional T (X ^ (i.val - u.natDegree))

/-- Applying a constraint gives the displayed native remainder or moment row. -/
@[simp] theorem rationalModificationConstraint_apply (T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (u P : 𝕜[X]) (n : ℕ) (i : Fin (u.natDegree + n)) :
    rationalModificationConstraint T u n i P =
      if i.val < u.natDegree then (P % u).coeff i.val
      else T (X ^ (i.val - u.natDegree) * P) := by
  unfold rationalModificationConstraint
  split_ifs <;> rfl

/-- The square monomial matrix of the actual rational-modification constraints. -/
def rationalModificationConstraintMatrix (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) :
    Matrix (Fin (u.natDegree + n)) (Fin (u.natDegree + n)) 𝕜 :=
  fun i j => rationalModificationConstraint T u n i (X ^ j.val)

/-- The leading monomial's column of rational-modification constraints. -/
def rationalModificationLeadingConstraints (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) :
    Fin (u.natDegree + n) → 𝕜 :=
  fun i => rationalModificationConstraint T u n i (X ^ (u.natDegree + n))

/-- The lower coefficient vector from the total matrix inverse. Its intended
solution interpretation requires the nonsingularity proved below. -/
def rationalModificationCoefficients (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) :
    Fin (u.natDegree + n) → 𝕜 :=
  (rationalModificationConstraintMatrix T u n)⁻¹ *ᵥ
    (fun i => -u.leadingCoeff * rationalModificationLeadingConstraints T u n i)

/-- The actual numerator computed by the finite inverse coefficient system. -/
def rationalModificationNumerator (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) : 𝕜[X] :=
  monomial (u.natDegree + n) u.leadingCoeff +
    ∑ j : Fin (u.natDegree + n), monomial j.val (rationalModificationCoefficients T u n j)

/-- Vanishing of every remainder and inverse-moment row is exactly divisibility
by the original numerator polynomial and the first `n` monomial moment tests. -/
theorem rationalModificationConstraint_eq_zero_iff (T : 𝕜[X] →ₗ[𝕜] 𝕜)
    {u : 𝕜[X]} (hu : u ≠ 0) (n : ℕ) (P : 𝕜[X]) :
    (∀ i : Fin (u.natDegree + n), rationalModificationConstraint T u n i P = 0) ↔
      u ∣ P ∧ ∀ r : Fin n, T (P * X ^ r.val) = 0 := by
  constructor
  · intro h
    have hrem : P % u = 0 := by
      apply Polynomial.ext
      intro k
      simp only [coeff_zero]
      by_cases hk : k < u.natDegree
      · let i : Fin (u.natDegree + n) := ⟨k, by omega⟩
        have hi := h i
        rw [rationalModificationConstraint_apply, if_pos hk] at hi
        exact hi
      · apply coeff_eq_zero_of_degree_lt
        exact ((degree_mod_lt P hu).trans_eq (degree_eq_natDegree hu)).trans_le
          (by exact_mod_cast (Nat.le_of_not_gt hk))
    refine ⟨EuclideanDomain.mod_eq_zero.mp hrem, ?_⟩
    intro r
    let i : Fin (u.natDegree + n) := ⟨u.natDegree + r.val, by have := r.isLt; omega⟩
    have hi := h i
    rw [rationalModificationConstraint_apply, if_neg (by dsimp [i]; omega)] at hi
    simpa only [i, Nat.add_sub_cancel_left, mul_comm] using hi
  · rintro ⟨hdiv, hmoment⟩ i
    rw [rationalModificationConstraint_apply]
    split_ifs with hi
    · rw [EuclideanDomain.mod_eq_zero.mpr hdiv, coeff_zero]
    · let r : Fin n := ⟨i.val - u.natDegree, by have := i.isLt; omega⟩
      simpa only [r, mul_comm] using hmoment r

/-- The constraint matrix applied to lower monomial coefficients gives exactly
the constraints of their polynomial. -/
theorem rationalModificationConstraint_sum_monomial_eq_mulVec
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ)
    (c : Fin (u.natDegree + n) → 𝕜) (i : Fin (u.natDegree + n)) :
    rationalModificationConstraint T u n i
      (∑ j : Fin (u.natDegree + n), monomial j.val (c j)) =
        (rationalModificationConstraintMatrix T u n *ᵥ c) i := by
  rw [map_sum]
  simp only [rationalModificationConstraintMatrix, mulVec, dotProduct]
  apply sum_congr rfl
  intro j _
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul]
  exact mul_comm _ _

/-- Finite modified nondegeneracy forces every lower-degree polynomial satisfying
the actual constraints to vanish. This is the kernel argument behind CU3. -/
theorem eq_zero_of_rationalModificationConstraint_eq_zero
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0)
    {P : 𝕜[X]} (hP : P.degree < (u.natDegree + n : ℕ))
    (hC : ∀ i : Fin (u.natDegree + n), rationalModificationConstraint T u n i P = 0) :
    P = 0 := by
  obtain ⟨hdiv, hmom⟩ := (rationalModificationConstraint_eq_zero_iff T hu n P).mp hC
  obtain ⟨s, rfl⟩ := hdiv
  by_cases hs : s = 0
  · simp [hs]
  have hsdeg : s.degree < n := by
    rw [degree_mul, degree_eq_natDegree hu, degree_eq_natDegree hs] at hP
    have h : u.natDegree + s.natDegree < u.natDegree + n := by exact_mod_cast hP
    rw [degree_eq_natDegree hs]
    exact_mod_cast (Nat.lt_of_add_lt_add_left h)
  have htests (r : Fin n) : polynomialWeightedFunctional T u (s * X ^ r.val) = 0 := by
    simpa only [polynomialWeightedFunctional_apply, mul_assoc] using hmom r
  have hs0 := eq_zero_of_degree_lt_of_orthogonal_of_hankelMomentDet_ne_zero
    (polynomialWeightedFunctional T u) hn hsdeg
    (fun q hq => functional_mul_eq_zero_of_monomial_tests _ htests hq)
  simp [hs0]

/-- The actual square coefficient matrix is nonsingular whenever the modified
order-`n` moment form is nondegenerate. The empty system is included.
Source: focused rational-modification reroute, normalization matrix (CU3). -/
theorem det_rationalModificationConstraintMatrix_ne_zero
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    (rationalModificationConstraintMatrix T u n).det ≠ 0 := by
  intro hzero
  obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  have hP := eq_zero_of_rationalModificationConstraint_eq_zero T hu hn
    (degree_sum_monomial_fin_lt c)
    (by intro i; rw [rationalModificationConstraint_sum_monomial_eq_mulVec, hMc]; rfl)
  exact hc (sum_monomial_fin_eq_zero_iff c |>.mp hP)

/-- The source positivity hypothesis proves nonvanishing of the actual
normalization determinant. It is vacuous in modified order zero.
Source: focused rational-modification reroute, normalization matrix (CU3).
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationConstraintMatrix_ne_zero_of_sq_pos
    (T : ℝ[X] →ₗ[ℝ] ℝ) {u : ℝ[X]} (hu : u ≠ 0) {n : ℕ}
    (hpos : ∀ p : ℝ[X], p.degree < n → p ≠ 0 →
      0 < polynomialWeightedFunctional T u (p^2)) :
    (rationalModificationConstraintMatrix T u n).det ≠ 0 := by
  apply det_rationalModificationConstraintMatrix_ne_zero T hu
  exact hankelMomentDet_ne_zero_of_posDef_of_le
    ((posDef_hankelMomentMatrix_iff_functional_sq_pos _ _).mpr hpos) le_rfl

/-- The computed lower coefficients solve the actual finite source system with
right-hand side the negative leading coefficient times the leading column. -/
theorem rationalModificationConstraintMatrix_mulVec_coefficients
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    rationalModificationConstraintMatrix T u n *ᵥ rationalModificationCoefficients T u n =
      fun i => -u.leadingCoeff * rationalModificationLeadingConstraints T u n i := by
  have hdet := det_rationalModificationConstraintMatrix_ne_zero T hu hn
  rw [rationalModificationCoefficients, mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]

/-- The actually computed numerator satisfies all native divisibility and
inverse-moment constraints. -/
theorem rationalModificationConstraint_numerator_eq_zero
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0)
    (i : Fin (u.natDegree + n)) :
    rationalModificationConstraint T u n i (rationalModificationNumerator T u n) = 0 := by
  rw [rationalModificationNumerator, map_add,
    rationalModificationConstraint_sum_monomial_eq_mulVec,
    rationalModificationConstraintMatrix_mulVec_coefficients T hu hn]
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul]
  simp only [rationalModificationLeadingConstraints, smul_eq_mul]
  ring

/-- The computed numerator has its prescribed top coefficient. -/
@[simp] theorem coeff_rationalModificationNumerator_self
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) :
    (rationalModificationNumerator T u n).coeff (u.natDegree + n) = u.leadingCoeff := by
  rw [rationalModificationNumerator, coeff_add, coeff_monomial, if_pos rfl,
    coeff_eq_zero_of_degree_lt (degree_sum_monomial_fin_lt _), add_zero]

/-- The computed numerator has degree at most the total numerator degree. -/
theorem degree_rationalModificationNumerator_le
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) (u : 𝕜[X]) (n : ℕ) :
    (rationalModificationNumerator T u n).degree ≤ (u.natDegree + n : ℕ) := by
  exact (degree_add_le _ _).trans (max_le (degree_monomial_le _ _)
    (degree_sum_monomial_fin_lt _).le)

/-- For a nonzero original numerator polynomial, the computed numerator has
exactly the prescribed degree. -/
theorem degree_rationalModificationNumerator_eq
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) (n : ℕ) :
    (rationalModificationNumerator T u n).degree = (u.natDegree + n : ℕ) := by
  apply le_antisymm (degree_rationalModificationNumerator_le T u n)
  apply le_degree_of_ne_zero
  rw [coeff_rationalModificationNumerator_self]
  exact leadingCoeff_ne_zero.mpr hu

/-- The coefficient system computes exactly the original numerator polynomial
times the canonical modified monic orthogonal polynomial, including order zero.
Source: focused rational-modification reroute, finite computation (CU2)--(CU3).
atlas: christoffel-uvarov-modification (partial) -/
theorem rationalModificationNumerator_eq_mul_monicOrthogonalPolynomial
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} (hu : u ≠ 0) {n : ℕ}
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    rationalModificationNumerator T u n =
      u * monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n := by
  let P := rationalModificationNumerator T u n
  let π := monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n
  have hπ : π.Monic := monic_monicOrthogonalPolynomial _ _
  have hπdeg : π.degree = n := by
    rw [degree_eq_natDegree hπ.ne_zero, natDegree_monicOrthogonalPolynomial]
  have hUdeg : (u * π).degree = (u.natDegree + n : ℕ) := by
    rw [degree_mul, degree_eq_natDegree hu, hπdeg, Nat.cast_add]
  have hPdeg : P.degree = (u.natDegree + n : ℕ) := degree_rationalModificationNumerator_eq T hu n
  have hP0 : P ≠ 0 := by
    intro h
    have hcoeff := coeff_rationalModificationNumerator_self T u n
    change P.coeff (u.natDegree + n) = u.leadingCoeff at hcoeff
    rw [h, coeff_zero] at hcoeff
    exact (leadingCoeff_ne_zero.mpr hu) hcoeff.symm
  have hPlead : P.leadingCoeff = u.leadingCoeff := by
    have hnat : P.natDegree = u.natDegree + n := by
      rw [degree_eq_natDegree hP0] at hPdeg
      exact WithBot.coe_inj.mp hPdeg
    rw [leadingCoeff, hnat]
    exact coeff_rationalModificationNumerator_self T u n
  have hdiff : (P - u * π).degree < (u.natDegree + n : ℕ) := by
    exact (degree_sub_lt_left (hPdeg.trans hUdeg.symm) hP0
      (hPlead.trans (by rw [leadingCoeff_mul, hπ.leadingCoeff, mul_one]))).trans_eq hPdeg
  have hπC : ∀ i : Fin (u.natDegree + n), rationalModificationConstraint T u n i (u * π) = 0 := by
    apply (rationalModificationConstraint_eq_zero_iff T hu n (u * π)).mpr
    refine ⟨dvd_mul_right _ _, ?_⟩
    intro r
    have h := functional_monicOrthogonalPolynomial_mul_X_pow_eq_zero
      (polynomialWeightedFunctional T u) hn r
    simpa only [π, polynomialWeightedFunctional_apply, mul_assoc] using h
  have heq := eq_zero_of_rationalModificationConstraint_eq_zero T hu hn hdiff
    (by intro i; rw [map_sub, rationalModificationConstraint_numerator_eq_zero T hu hn, hπC i]; simp)
  exact sub_eq_zero.mp heq

end NLAlib
