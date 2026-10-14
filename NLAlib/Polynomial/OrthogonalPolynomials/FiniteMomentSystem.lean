import NLAlib.Polynomial.OrthogonalPolynomials.Basic
import NLAlib.Polynomial.OrthogonalPolynomials.Uniqueness
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Finite moment systems for monic orthogonal polynomials

A nonsingular Hankel matrix solves the monic orthogonality problem exactly.
All statements are bilinear over an arbitrary field, so they apply to real and complex
formal moment functionals. Source: Gautschi (2004), Chapter 1.
Atlas: `formal-orthogonal-polynomials` and `hankel-moment-positivity`.
-/

noncomputable section

open Polynomial Finset Matrix
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- A finite monomial expansion recovers its indexed coefficients exactly. -/
@[simp] theorem coeff_sum_monomial_fin {n : ℕ} (c : Fin n → 𝕜) (i : Fin n) :
    (∑ j : Fin n, monomial j.val (c j)).coeff i.val = c i := by
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact if_neg (fun h => hji (Fin.ext h))
  · simp

/-- A finite monomial coefficient vector is zero exactly when its polynomial is zero. -/
theorem sum_monomial_fin_eq_zero_iff {n : ℕ} (c : Fin n → 𝕜) :
    (∑ i : Fin n, monomial i.val (c i)) = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext i
    have hc := congrArg (fun p : 𝕜[X] => p.coeff i.val) h
    simpa only [coeff_sum_monomial_fin, coeff_zero, Pi.zero_apply] using hc
  · rintro rfl
    simp

/-- Every finite order-`n` coefficient expansion has degree below `n`. -/
theorem degree_sum_monomial_fin_lt {n : ℕ} (c : Fin n → 𝕜) :
    (∑ i : Fin n, monomial i.val (c i)).degree < n := by
  apply mem_degreeLT.mp
  apply Submodule.sum_mem
  intro i _
  apply mem_degreeLT.mpr
  exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast i.isLt)

/-- A polynomial of degree below `n` is its finite vector of monomial coefficients. -/
theorem eq_sum_monomial_fin_of_degree_lt {p : 𝕜[X]} {n : ℕ} (hp : p.degree < n) :
    p = ∑ i : Fin n, monomial i.val (p.coeff i.val) := by
  by_cases hp0 : p = 0
  · subst p
    simp
  · rw [show (∑ i : Fin n, monomial i.val (p.coeff i.val)) =
        ∑ i ∈ Finset.range n, monomial i (p.coeff i) from
      Fin.sum_univ_eq_sum_range (fun i : ℕ => monomial i (p.coeff i)) n]
    exact p.as_sum_range' n ((natDegree_lt_iff_degree_lt hp0).mpr hp)

/-- The functional applied to a bounded-degree polynomial times a monomial is
the corresponding Hankel row applied to its coefficient vector. -/
theorem functional_sum_monomial_mul_X_pow (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n j : ℕ)
    (c : Fin n → 𝕜) :
    L ((∑ i : Fin n, monomial i.val (c i)) * X ^ j) =
      ∑ i : Fin n, c i * L (X ^ (i.val + j)) := by
  simp only [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add, C_mul', map_smul]
  rfl

/-- Orthogonality to the first `n` monomials is orthogonality to every polynomial
of degree below `n`. -/
theorem functional_mul_eq_zero_of_monomial_tests (L : 𝕜[X] →ₗ[𝕜] 𝕜) {p : 𝕜[X]} {n : ℕ}
    (h : ∀ i : Fin n, L (p * X ^ i.val) = 0) {q : 𝕜[X]} (hq : q.degree < n) :
    L (p * q) = 0 := by
  rw [eq_sum_monomial_fin_of_degree_lt hq, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [← C_mul_X_pow_eq_monomial, mul_comm p (C _ * _), mul_assoc, C_mul', map_smul,
    mul_comm (X ^ i.val) p, h i, smul_zero]

/-- A polynomial's lower-degree moment equations are multiplication of its coefficient
vector by the finite Hankel matrix. -/
theorem functional_mul_X_pow_eq_hankel_mulVec (L : 𝕜[X] →ₗ[𝕜] 𝕜)
    {p : 𝕜[X]} {n : ℕ} (hp : p.degree < n) (j : Fin n) :
    L (p * X ^ j.val) = (hankelMomentMatrix L n *ᵥ (fun i => p.coeff i.val)) j := by
  nth_rw 1 [eq_sum_monomial_fin_of_degree_lt hp]
  rw [functional_sum_monomial_mul_X_pow]
  simp only [hankelMomentMatrix, mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm, mul_comm]

/-- If the finite Hankel matrix is nonsingular, a lower-degree polynomial orthogonal
to every lower degree vanishes. This is bilinear nondegeneracy, not a positivity claim. -/
theorem eq_zero_of_degree_lt_of_orthogonal_of_hankelMomentDet_ne_zero
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {n : ℕ} (hn : hankelMomentDet L n ≠ 0)
    {p : 𝕜[X]} (hp : p.degree < n)
    (horth : ∀ q : 𝕜[X], q.degree < n → L (p * q) = 0) : p = 0 := by
  let c : Fin n → 𝕜 := fun i => p.coeff i.val
  have hunit : IsUnit (hankelMomentMatrix L n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
  let : Invertible (hankelMomentMatrix L n) := hunit.invertible
  have hMc : hankelMomentMatrix L n *ᵥ c = 0 := by
    funext j
    rw [← functional_mul_X_pow_eq_hankel_mulVec L hp j]
    apply horth (X ^ j.val)
    rw [degree_X_pow]
    exact_mod_cast j.isLt
  have hc : c = 0 := by
    apply Matrix.mulVec_injective_of_invertible (hankelMomentMatrix L n)
    simpa only [Matrix.mulVec_zero] using hMc
  rw [eq_sum_monomial_fin_of_degree_lt hp]
  have hc' (i : Fin n) : p.coeff i.val = 0 := congrFun hc i
  simp only [hc', monomial_zero_right, Finset.sum_const_zero]

/-- The finite moment-system monic polynomial is orthogonal to each lower monomial.
Only the order-`n` Hankel determinant needs to be nonzero. -/
theorem functional_monicOrthogonalPolynomial_mul_X_pow_eq_zero
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {n : ℕ} (hn : hankelMomentDet L n ≠ 0) (j : Fin n) :
    L (monicOrthogonalPolynomial L n * X ^ j.val) = 0 := by
  have hunit : IsUnit (hankelMomentMatrix L n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
  let : Invertible (hankelMomentMatrix L n) := hunit.invertible
  have hsystem : hankelMomentMatrix L n *ᵥ orthogonalPolynomialCoefficients L n =
      (fun i => -L (X ^ (n + i.val))) := by
    rw [orthogonalPolynomialCoefficients, Matrix.mulVec_mulVec,
      Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  unfold monicOrthogonalPolynomial orthogonalPolynomialLowerPart
  rw [add_mul, map_add, ← pow_add, functional_sum_monomial_mul_X_pow]
  have hs := congrFun hsystem j
  simp only [hankelMomentMatrix, mulVec, dotProduct] at hs
  have hsum : (∑ i : Fin n, orthogonalPolynomialCoefficients L n i * L (X ^ (i.val + j.val))) =
      -L (X ^ (n + j.val)) := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm, mul_comm]
  rw [hsum, add_neg_cancel]

/-- Nonsingular finite moments give a monic polynomial orthogonal to every lower
degree, also for nonpositive and complex moment functionals.
Source: Gautschi (2004), Section 1.3, finite coefficient system. -/
theorem isMonicOrthogonalPolynomial_monicOrthogonalPolynomial
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {n : ℕ} (hn : hankelMomentDet L n ≠ 0) :
    IsMonicOrthogonalPolynomial L n (monicOrthogonalPolynomial L n) := by
  refine ⟨monic_monicOrthogonalPolynomial L n, natDegree_monicOrthogonalPolynomial L n, ?_⟩
  intro q hq
  exact functional_mul_eq_zero_of_monomial_tests L
    (functional_monicOrthogonalPolynomial_mul_X_pow_eq_zero L hn) hq

/-- Two monic orthogonal polynomials coincide whenever the finite Hankel matrix
at their order is nonsingular. Source: Gautschi (2004), Section 1.3. -/
theorem IsMonicOrthogonalPolynomial.eq_of_hankelMomentDet_ne_zero
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ} {p q : 𝕜[X]}
    (hp : IsMonicOrthogonalPolynomial L n p) (hq : IsMonicOrthogonalPolynomial L n q)
    (hn : hankelMomentDet L n ≠ 0) : p = q := by
  apply hp.eq_of_nondegenerate hq
  intro r hr horth
  exact eq_zero_of_degree_lt_of_orthogonal_of_hankelMomentDet_ne_zero L hn hr horth

/-- A nonsingular order-`n` Hankel system supplies the unique monic orthogonal
polynomial of that degree. No positivity or complex-conjugation hypothesis is used.
Source: Gautschi (2004), Section 1.3.
atlas: formal-orthogonal-polynomials (partial), orthogonal-polynomials-measure-def (partial) -/
theorem existsUnique_isMonicOrthogonalPolynomial_of_hankelMomentDet_ne_zero
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {n : ℕ} (hn : hankelMomentDet L n ≠ 0) :
    ∃! p : 𝕜[X], IsMonicOrthogonalPolynomial L n p := by
  have hp := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hn
  refine ⟨monicOrthogonalPolynomial L n, hp, ?_⟩
  intro q hq
  exact hq.eq_of_hankelMomentDet_ne_zero hp hn

/-- Unique solvability of a monic orthogonality problem forces its Hankel system
to be nonsingular; a nonzero homogeneous solution would give a second monic polynomial. -/
theorem hankelMomentDet_ne_zero_of_existsUnique_isMonicOrthogonalPolynomial
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {n : ℕ} (h : ∃! p : 𝕜[X], IsMonicOrthogonalPolynomial L n p) :
    hankelMomentDet L n ≠ 0 := by
  obtain ⟨p, hp, huniq⟩ := h
  have hpd : p.degree = n := by rw [degree_eq_natDegree hp.monic.ne_zero, hp.natDegree_eq]
  have hker : ∀ c : Fin n → 𝕜, hankelMomentMatrix L n *ᵥ c = 0 → c = 0 := by
    intro c hc
    let r : 𝕜[X] := ∑ i : Fin n, monomial i.val (c i)
    have hr : r.degree < n := degree_sum_monomial_fin_lt c
    have horth : ∀ q : 𝕜[X], q.degree < n → L (r * q) = 0 := by
      intro q hq
      apply functional_mul_eq_zero_of_monomial_tests L _ hq
      intro i
      rw [functional_mul_X_pow_eq_hankel_mulVec L hr i]
      simp only [r, coeff_sum_monomial_fin, hc, Pi.zero_apply]
    have hpr : IsMonicOrthogonalPolynomial L n (p + r) := by
      refine ⟨hp.monic.add_of_left (hr.trans_eq hpd.symm), ?_, ?_⟩
      · rw [natDegree_add_eq_left_of_degree_lt (hr.trans_eq hpd.symm), hp.natDegree_eq]
      · intro q hq
        rw [add_mul, map_add, hp.orthogonal _ hq, horth _ hq, add_zero]
    have hr0 : r = 0 := by
      have heq := huniq (p + r) hpr
      exact (add_eq_left.mp heq)
    exact (sum_monomial_fin_eq_zero_iff c).mp hr0
  have hinj : Function.Injective (Matrix.mulVec (hankelMomentMatrix L n)) := by
    intro c d hcd
    apply sub_eq_zero.mp
    apply hker (c - d)
    rw [Matrix.mulVec_sub, hcd, sub_self]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

/-- A monic orthogonality problem is uniquely solvable exactly when its finite
Hankel determinant is nonzero. Source: Gautschi (2004), Section 1.3.
atlas: formal-orthogonal-polynomials (partial) -/
theorem existsUnique_isMonicOrthogonalPolynomial_iff_hankelMomentDet_ne_zero
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    (∃! p : 𝕜[X], IsMonicOrthogonalPolynomial L n p) ↔ hankelMomentDet L n ≠ 0 :=
  ⟨hankelMomentDet_ne_zero_of_existsUnique_isMonicOrthogonalPolynomial L,
    existsUnique_isMonicOrthogonalPolynomial_of_hankelMomentDet_ne_zero L⟩

/-- Multiplying a monic orthogonal polynomial by its leading monomial gives its
squared bilinear norm, since their difference has lower degree. -/
theorem IsMonicOrthogonalPolynomial.functional_mul_X_pow_eq_sq
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ} {p : 𝕜[X]}
    (hp : IsMonicOrthogonalPolynomial L n p) : L (p * X ^ n) = L (p ^ 2) := by
  have hpd : p.degree = n := by rw [degree_eq_natDegree hp.monic.ne_zero, hp.natDegree_eq]
  have hdiff : (p - X ^ n).degree < (n : WithBot ℕ) := by
    rw [← hpd]
    apply degree_sub_lt_left (by simp [hpd]) hp.monic.ne_zero
    simp [(hp.monic).leadingCoeff]
  have h := hp.orthogonal (p - X ^ n) hdiff
  rw [mul_sub, map_sub] at h
  simpa only [pow_two] using (sub_eq_zero.mp h).symm

/-- If the next moment system is nonsingular, the squared bilinear norm of a
monic orthogonal polynomial is nonzero, even for complex formal functionals. -/
theorem IsMonicOrthogonalPolynomial.functional_sq_ne_zero
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ} {p : 𝕜[X]}
    (hp : IsMonicOrthogonalPolynomial L n p) (hn : hankelMomentDet L (n + 1) ≠ 0) :
    L (p ^ 2) ≠ 0 := by
  intro hzero
  have hpd : p.degree = n := by rw [degree_eq_natDegree hp.monic.ne_zero, hp.natDegree_eq]
  have horth : ∀ q : 𝕜[X], q.degree < (n + 1 : ℕ) → L (p * q) = 0 := by
    intro q hq
    apply functional_mul_eq_zero_of_monomial_tests L _ hq
    intro i
    by_cases hi : i.val < n
    · apply hp.orthogonal
      rw [degree_X_pow]
      exact_mod_cast hi
    · have hieq : i.val = n := by have := i.isLt; omega
      rw [hieq, hp.functional_mul_X_pow_eq_sq, hzero]
  have hpzero := eq_zero_of_degree_lt_of_orthogonal_of_hankelMomentDet_ne_zero L hn
    (show p.degree < (n + 1 : ℕ) by rw [hpd]; exact_mod_cast Nat.lt_succ_self n) horth
  exact hp.monic.ne_zero hpzero

/-- Quasi-definiteness is equivalent to unique monic lower-degree orthogonality
at every order. Source: Gautschi (2004), Section 1.3.
atlas: formal-orthogonal-polynomials (partial) -/
theorem quasiDefinitePolynomialFunctional_iff_forall_existsUnique
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) : QuasiDefinitePolynomialFunctional L ↔
      ∀ n, ∃! p : 𝕜[X], IsMonicOrthogonalPolynomial L n p := by
  unfold QuasiDefinitePolynomialFunctional
  simp_rw [existsUnique_isMonicOrthogonalPolynomial_iff_hankelMomentDet_ne_zero]

/-- Every canonical formal monic polynomial has nonzero squared norm for a
quasi-definite functional. Source: Gautschi (2004), Section 1.3. -/
theorem orthogonalPolynomialNorm_ne_zero_of_quasiDefinite
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (hL : QuasiDefinitePolynomialFunctional L) (n : ℕ) :
    orthogonalPolynomialNorm L n ≠ 0 :=
  (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL n)).functional_sq_ne_zero
    (hL (n + 1))

/-- Distinct canonical monic polynomials are bilinearly orthogonal whenever both
finite Hankel systems are nonsingular. -/
theorem functional_monicOrthogonalPolynomial_mul_eq_zero_of_ne
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {i j : ℕ} (hi : hankelMomentDet L i ≠ 0)
    (hj : hankelMomentDet L j ≠ 0) (hij : i ≠ j) :
    L (monicOrthogonalPolynomial L i * monicOrthogonalPolynomial L j) = 0 := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · rw [mul_comm]
    apply (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hj).orthogonal
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L i).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hij
  · apply (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hi).orthogonal
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L j).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hij

/-- Monic recurrence subdiagonal coefficients do not vanish for a quasi-definite
functional, at every positive order. Order zero is the recurrence boundary
coefficient and equals zero by convention. Source: Gautschi (2004), Section 1.3.
atlas: formal-orthogonal-polynomials (partial) -/
theorem orthogonalRecurrenceBeta_ne_zero_of_quasiDefinite
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (hL : QuasiDefinitePolynomialFunctional L) {n : ℕ} (hn : 0 < n) :
    orthogonalRecurrenceBeta L n ≠ 0 := by
  rw [orthogonalRecurrenceBeta, if_neg hn.ne']
  exact div_ne_zero (orthogonalPolynomialNorm_ne_zero_of_quasiDefinite hL n)
    (orthogonalPolynomialNorm_ne_zero_of_quasiDefinite hL (n - 1))

/-- Within degree `n`, lower-degree orthogonality forces a polynomial to be a
scalar multiple of the canonical monic polynomial. The scalar is its degree-`n`
coefficient; the statement includes the zero polynomial and order zero. -/
theorem eq_C_mul_monicOrthogonalPolynomial_of_degree_le_of_orthogonal
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) {n : ℕ} (hL : hankelMomentDet L n ≠ 0)
    {p : 𝕜[X]} (hp : p.degree ≤ n)
    (ho : ∀ q : 𝕜[X], q.degree < n → L (p * q) = 0) :
    p = C (p.coeff n) * monicOrthogonalPolynomial L n := by
  let P := monicOrthogonalPolynomial L n
  let r := p - C (p.coeff n) * P
  have hP := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hL
  have hPd : P.degree = n := by
    rw [degree_eq_natDegree hP.monic.ne_zero, hP.natDegree_eq]
  have hrd : r.degree < n := by
    apply (degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    simp only [r, coeff_sub, coeff_C_mul]
    by_cases hkn : k = n
    · subst k
      have hcoeff : P.coeff n = 1 := by
        rw [← hP.natDegree_eq, coeff_natDegree, hP.monic.leadingCoeff]
      rw [hcoeff, mul_one, sub_self]
    · have hnk : n < k := by omega
      have hpzero : p.coeff k = 0 :=
        coeff_eq_zero_of_degree_lt (hp.trans_lt (by exact_mod_cast hnk))
      have hPzero : P.coeff k = 0 := coeff_eq_zero_of_degree_lt (by
        rw [hPd]
        exact_mod_cast hnk)
      rw [hpzero, hPzero, mul_zero, sub_self]
  have hr0 : r = 0 := by
    apply eq_zero_of_degree_lt_of_orthogonal_of_hankelMomentDet_ne_zero L hL hrd
    intro q hq
    rw [show r * q = p * q - C (p.coeff n) * (P * q) by dsimp [r]; ring,
      map_sub, C_mul', map_smul, ho q hq, hP.orthogonal q hq, smul_zero, sub_self]
  exact sub_eq_zero.mp hr0

end NLAlib
