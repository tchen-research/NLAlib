import NLAlib.Polynomial.OrthogonalPolynomials.Recurrence

/-! # Exact linear Christoffel modification

Multiplying a moment functional by `X-z` changes its monic polynomials by an
exact polynomial quotient. Original finite Hankel nondegeneracy and nonzero
evaluation at `z` imply the modified finite system is nonsingular.
Source: Gautschi (2004), Theorem 1.33; operator derivations OP20–OP22.
-/

noncomputable section

open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜]

/-- The moment functional weighted by a polynomial. Over a positive real measure,
this is integration against that polynomial density when the density is nonnegative. -/
def polynomialWeightedFunctional (L : 𝕜[X] →ₗ[𝕜] 𝕜) (w : 𝕜[X]) : 𝕜[X] →ₗ[𝕜] 𝕜 where
  toFun p := L (w * p)
  map_add' p q := by rw [mul_add, map_add]
  map_smul' c p := by simp only [mul_smul_comm, map_smul, RingHom.id_apply]

/-- Applying the polynomial-weighted functional is multiplication before applying
the original functional. -/
@[simp] theorem polynomialWeightedFunctional_apply (L : 𝕜[X] →ₗ[𝕜] 𝕜) (w p : 𝕜[X]) :
    polynomialWeightedFunctional L w p = L (w * p) := rfl

/-- The total monic Christoffel quotient for the linear factor `X-z`. Its exact
modification interpretation requires a nonsingular original moment system and
nonvanishing original degree-`n` evaluation at `z`. -/
def christoffelPolynomial (L : 𝕜[X] →ₗ[𝕜] 𝕜) (z : 𝕜) (n : ℕ) : 𝕜[X] :=
  (monicOrthogonalPolynomial L (n + 1) -
    C ((monicOrthogonalPolynomial L (n + 1)).eval z /
      (monicOrthogonalPolynomial L n).eval z) * monicOrthogonalPolynomial L n) /ₘ (X - C z)

private theorem weighted_lower_nondegenerate (L : 𝕜[X] →ₗ[𝕜] 𝕜) {n : ℕ}
    (hL : hankelMomentDet L n ≠ 0) {z : 𝕜}
    (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0)
    (r : 𝕜[X]) (hr : r.degree < n)
    (ho : ∀ s : 𝕜[X], s.degree < n → polynomialWeightedFunctional L (X - C z) (r * s) = 0) :
    r = 0 := by
  by_cases hr0 : r = 0
  · exact hr0
  let p := (X - C z) * r
  have hp0 : p ≠ 0 := mul_ne_zero (monic_X_sub_C z).ne_zero hr0
  have hpd : p.degree ≤ n := by
    apply natDegree_le_iff_degree_le.mp
    have hdeg := natDegree_mul_le (p := X - C z) (q := r)
    rw [natDegree_X_sub_C] at hdeg
    have hrn := (natDegree_lt_iff_degree_lt hr0).mpr hr
    exact hdeg.trans (by omega)
  have heq := eq_C_mul_monicOrthogonalPolynomial_of_degree_le_of_orthogonal L hL hpd
    (fun s hs => by
      change L (((X - C z) * r) * s) = 0
      rw [mul_assoc]
      exact ho s hs)
  have h := congrArg (eval z) heq
  simp only [p, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul] at h
  have hc : p.coeff n = 0 := (mul_eq_zero.mp h.symm).resolve_right hz
  rw [hc, C_0, zero_mul] at heq
  exact False.elim (hp0 heq)

/-- The linear modification quotient is exact: multiplying it by `X-z` recovers
the numerator, without an analytic division operation.
Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem X_sub_C_mul_christoffelPolynomial (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) {z : 𝕜}
    (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0) :
    (X - C z) * christoffelPolynomial L z n =
      monicOrthogonalPolynomial L (n + 1) -
        C ((monicOrthogonalPolynomial L (n + 1)).eval z /
          (monicOrthogonalPolynomial L n).eval z) * monicOrthogonalPolynomial L n := by
  let N := monicOrthogonalPolynomial L (n + 1) -
    C ((monicOrthogonalPolynomial L (n + 1)).eval z /
      (monicOrthogonalPolynomial L n).eval z) * monicOrthogonalPolynomial L n
  have hNz : N.eval z = 0 := by
    simp only [N, eval_sub, eval_mul, eval_C]
    rw [div_mul_cancel₀ _ hz, sub_self]
  have hmod : N %ₘ (X - C z) = 0 := by
    rw [modByMonic_X_sub_C_eq_C_eval, hNz, C_0]
  have h := modByMonic_add_div N (X - C z)
  rw [hmod, zero_add] at h
  change (X - C z) * (N /ₘ (X - C z)) = N
  exact h

/-- The exact quotient is a monic degree-`n` polynomial orthogonal for the
`X-z` weighted functional. Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem isMonicOrthogonalPolynomial_christoffelPolynomial
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) {z : 𝕜}
    (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0) :
    IsMonicOrthogonalPolynomial (polynomialWeightedFunctional L (X - C z)) n
      (christoffelPolynomial L z n) := by
  let P := monicOrthogonalPolynomial L
  let c := (P (n + 1)).eval z / (P n).eval z
  let N := P (n + 1) - C c * P n
  have hdeg (k : ℕ) : (P k).degree = k := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
      natDegree_monicOrthogonalPolynomial]
  have hsmall : (C c * P n).degree < (P (n + 1)).degree := by
    rw [hdeg (n + 1), C_mul']
    exact (degree_smul_le c _).trans_lt (by rw [hdeg n]; exact_mod_cast Nat.lt_succ_self n)
  have hNmonic : N.Monic := (monic_monicOrthogonalPolynomial L (n + 1)).sub_of_left hsmall
  have hNdegree : N.natDegree = n + 1 := by
    have h := degree_sub_eq_left_of_degree_lt hsmall
    exact (natDegree_eq_of_degree_eq h).trans (natDegree_monicOrthogonalPolynomial L (n + 1))
  have hmul := X_sub_C_mul_christoffelPolynomial L n hz
  refine ⟨?_, ?_, ?_⟩
  · apply (monic_X_sub_C z).of_mul_monic_left
    rw [hmul]
    exact hNmonic
  · change (N /ₘ (X - C z)).natDegree = n
    rw [natDegree_divByMonic _ (monic_X_sub_C z), hNdegree, natDegree_X_sub_C]
    omega
  · intro r hr
    change L ((X - C z) * (christoffelPolynomial L z n * r)) = 0
    rw [← mul_assoc, hmul, sub_mul, map_sub,
      show (C _ * P n) * r = C c * (P n * r) by
        change (C c * P n) * r = C c * (P n * r)
        exact mul_assoc _ _ _,
      C_mul', map_smul,
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
        (hL (n + 1) le_rfl)).orthogonal r (hr.trans (by exact_mod_cast Nat.lt_succ_self n)),
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL n (by omega))).orthogonal r hr,
      smul_zero, sub_self]

/-- Nonzero degree-`n` evaluation at the modification point makes the modified
order-`n` Hankel system nonsingular. Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem hankelMomentDet_polynomialWeightedFunctional_X_sub_C_ne_zero
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) {z : 𝕜}
    (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0) :
    hankelMomentDet (polynomialWeightedFunctional L (X - C z)) n ≠ 0 := by
  apply hankelMomentDet_ne_zero_of_existsUnique_isMonicOrthogonalPolynomial
  refine ⟨christoffelPolynomial L z n, isMonicOrthogonalPolynomial_christoffelPolynomial L n hL hz, ?_⟩
  intro p hp
  exact hp.eq_of_nondegenerate (isMonicOrthogonalPolynomial_christoffelPolynomial L n hL hz)
    (weighted_lower_nondegenerate L (hL n (by omega)) hz)

/-- The canonical monic polynomials of the linear modified functional are exactly
the Christoffel quotients. Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem monicOrthogonalPolynomial_polynomialWeightedFunctional_X_sub_C
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) {z : 𝕜}
    (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0) :
    monicOrthogonalPolynomial (polynomialWeightedFunctional L (X - C z)) n =
      christoffelPolynomial L z n :=
  (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial _
    (hankelMomentDet_polynomialWeightedFunctional_X_sub_C_ne_zero L n hL hz)).eq_of_nondegenerate
      (isMonicOrthogonalPolynomial_christoffelPolynomial L n hL hz)
      (weighted_lower_nondegenerate L (hL n (by omega)) hz)

/-- The squared bilinear norm after a linear Christoffel modification is the
negative polynomial-evaluation ratio times the original norm. This formula is
valid over the complex numbers as a bilinear identity.
Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem orthogonalPolynomialNorm_polynomialWeightedFunctional_X_sub_C
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) {z : 𝕜}
    (hL : ∀ k ≤ n + 1, hankelMomentDet L k ≠ 0)
    (hz : (monicOrthogonalPolynomial L n).eval z ≠ 0) :
    orthogonalPolynomialNorm (polynomialWeightedFunctional L (X - C z)) n =
      -((monicOrthogonalPolynomial L (n + 1)).eval z /
        (monicOrthogonalPolynomial L n).eval z) * orthogonalPolynomialNorm L n := by
  let P := christoffelPolynomial L z n
  have hP := isMonicOrthogonalPolynomial_christoffelPolynomial L n hL hz
  rw [orthogonalPolynomialNorm,
    monicOrthogonalPolynomial_polynomialWeightedFunctional_X_sub_C L n hL hz]
  change L ((X - C z) * P ^ 2) = _
  rw [pow_two, ← mul_assoc, X_sub_C_mul_christoffelPolynomial L n hz,
    sub_mul, map_sub]
  have hdeg : P.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hP.monic.ne_zero, hP.natDegree_eq]
    exact_mod_cast Nat.lt_succ_self n
  rw [(isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
    (hL (n + 1) le_rfl)).orthogonal P hdeg]
  rw [mul_assoc, C_mul', map_smul, smul_eq_mul,
    (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L
      (hL n (by omega))).functional_mul_eq_sq_of_monic hP.monic hP.natDegree_eq]
  change 0 - _ * orthogonalPolynomialNorm L n = -_ * orthogonalPolynomialNorm L n
  ring

/-- A quasi-definite functional remains quasi-definite after multiplication by
`X-z` whenever every original monic polynomial is nonzero at `z`.
Source: Gautschi (2004), Theorem 1.33.
atlas: kernel-polynomials-christoffel (partial), christoffel-uvarov-modification (partial) -/
theorem quasiDefinitePolynomialWeightedFunctional_X_sub_C
    {L : 𝕜[X] →ₗ[𝕜] 𝕜} (hL : QuasiDefinitePolynomialFunctional L) {z : 𝕜}
    (hz : ∀ n, (monicOrthogonalPolynomial L n).eval z ≠ 0) :
    QuasiDefinitePolynomialFunctional (polynomialWeightedFunctional L (X - C z)) :=
  fun n => hankelMomentDet_polynomialWeightedFunctional_X_sub_C_ne_zero L n
    (fun k _ => hL k) (hz n)

end NLAlib
