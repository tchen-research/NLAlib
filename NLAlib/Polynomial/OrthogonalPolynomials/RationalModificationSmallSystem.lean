import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationConstraints
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # The compressed rational-modification constraint system

Polynomial division reduces the inverse-moment tests to `min(n,degree v)`
on the span starting at degree `n-degree v`. Its actual minor is nonsingular
by the same modified positivity argument as the full monomial system.
Source: focused mathematical reroutes, Section 4, CU6--CU8.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset Matrix
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

/-- The smaller matrix applies the native remainder and inverse-moment rows
to the original monic polynomials from degree `n-degree v` upward. -/
def rationalModificationSmallMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (u v : 𝕜[X]) (n : ℕ) :
    Matrix (Fin (u.natDegree + min n v.natDegree))
      (Fin (u.natDegree + min n v.natDegree)) 𝕜 :=
  fun i j => rationalModificationConstraint T u (min n v.natDegree) i
    (monicOrthogonalPolynomial L (n-v.natDegree+j.val))

/-- On the original lower-orthogonal subspace, the smaller inverse-moment
test set is equivalent to all `n` tests. This includes `degree v>n` without
negative indices or additional pole equations. Source: CU7. -/
theorem rationalModificationConstraint_small_iff_full
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {u v : 𝕜[X]} (hu : u ≠ 0) (hv : v ≠ 0)
    (hTv : ∀ p, T (v*p) = L p) (n : ℕ) (P : 𝕜[X])
    (horth : ∀ q : 𝕜[X], q.degree < (n-v.natDegree : ℕ) → L (P*q) = 0) :
    (∀ i, rationalModificationConstraint T u (min n v.natDegree) i P = 0) ↔
      (∀ i, rationalModificationConstraint T u n i P = 0) := by
  rw [rationalModificationConstraint_eq_zero_iff T hu,
    rationalModificationConstraint_eq_zero_iff T hu]
  constructor
  · rintro ⟨hdiv, hsmall⟩
    refine ⟨hdiv, ?_⟩
    intro r
    by_cases hnm : n ≤ v.natDegree
    · exact hsmall ⟨r.val, by simpa only [min_eq_left hnm] using r.isLt⟩
    have hmn : v.natDegree ≤ n := (Nat.le_of_not_ge hnm)
    let a := (X^r.val) / v
    let b := (X^r.val) % v
    have hb : b.degree < (min n v.natDegree : ℕ) := by
      rw [min_eq_right hmn]
      exact (degree_mod_lt _ hv).trans_eq (degree_eq_natDegree hv)
    have ha : a.degree < (n-v.natDegree : ℕ) := by
      by_cases ha0 : a = 0
      · rw [ha0, degree_zero]
        exact WithBot.bot_lt_coe _
      have hle : v.degree ≤ (X^r.val : 𝕜[X]).degree :=
        le_of_not_gt (mt (Polynomial.div_eq_zero_iff hv).mpr ha0)
      have hdeg := degree_add_div hv hle
      rw [degree_eq_natDegree hv, degree_X_pow, degree_eq_natDegree ha0] at hdeg
      have heq : v.natDegree+a.natDegree = r.val := by exact_mod_cast hdeg
      rw [degree_eq_natDegree ha0]
      exact_mod_cast (show a.natDegree < n-v.natDegree by have := r.isLt; omega)
    have hbT : T (P*b) = 0 := functional_mul_eq_zero_of_monomial_tests T hsmall hb
    have haT : T (P*(v*a)) = 0 := by
      rw [show P*(v*a) = v*(P*a) by ring, hTv, horth a ha]
    have hdivpoly : (X^r.val : 𝕜[X]) = v*a+b := (EuclideanDomain.div_add_mod _ _).symm
    rw [hdivpoly, mul_add, map_add, haT, hbT, add_zero]
  · rintro ⟨hdiv, hfull⟩
    refine ⟨hdiv, ?_⟩
    intro r
    exact hfull ⟨r.val, r.isLt.trans_le (min_le_left _ _)⟩

/-- The actual compressed normalization minor is nonzero, including empty
systems and denominator degree greater than the orthogonal order.
Source: focused mathematical reroutes, compressed normalization (CU8).
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationSmallMatrix_ne_zero
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {u v : 𝕜[X]} (hu : u ≠ 0) (hv : v ≠ 0)
    (hTv : ∀ p, T (v*p) = L p) {n : ℕ}
    (hL : ∀ j < u.natDegree+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    (rationalModificationSmallMatrix L T u v n).det ≠ 0 := by
  intro hzero
  obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  let P : 𝕜[X] := ∑ j : Fin (u.natDegree + min n v.natDegree),
    c j • monicOrthogonalPolynomial L (n-v.natDegree+j.val)
  have hindex (j : Fin (u.natDegree + min n v.natDegree)) :
      n-v.natDegree+j.val < u.natDegree+n := by
    have := j.isLt
    omega
  have hPdeg : P.degree < (u.natDegree+n : ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    apply (degree_smul_le _ _).trans_lt
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hindex j
  have horth (q : 𝕜[X]) (hq : q.degree < (n-v.natDegree : ℕ)) : L (P*q) = 0 := by
    dsimp only [P]
    rw [sum_mul, map_sum]
    apply sum_eq_zero
    intro j _
    rw [smul_mul_assoc, map_smul,
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL _ (hindex j))).orthogonal q
        (hq.trans_le (by exact_mod_cast Nat.le_add_right (n-v.natDegree) j.val)), smul_zero]
  have hsmall (i : Fin (u.natDegree + min n v.natDegree)) :
      rationalModificationConstraint T u (min n v.natDegree) i P = 0 := by
    have h := congrFun hMc i
    simpa only [P, map_sum, map_smul, smul_eq_mul,
      rationalModificationSmallMatrix, Matrix.mulVec, dotProduct, mul_comm, Pi.zero_apply] using h
  have hP0 := eq_zero_of_rationalModificationConstraint_eq_zero T hu hn hPdeg
    ((rationalModificationConstraint_small_iff_full L T hu hv hTv n P horth).mp hsmall)
  have hlin : LinearIndependent 𝕜 (fun j : Fin (u.natDegree + min n v.natDegree) =>
      monicOrthogonalPolynomial L (n-v.natDegree+j.val)) :=
    (monicMomentPolynomialSequence L).linearIndependent.comp _
      (fun i j hij => Fin.ext (Nat.add_left_cancel hij))
  exact hc (funext (Fintype.linearIndependent_iff.mp hlin c hP0))

/-- The compressed constraint column of the degree-`n+degree u` monic original
polynomial. -/
def rationalModificationSmallLeadingConstraints (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (u v : 𝕜[X]) (n : ℕ) : Fin (u.natDegree + min n v.natDegree) → 𝕜 :=
  fun i => rationalModificationConstraint T u (min n v.natDegree) i
    (monicOrthogonalPolynomial L (u.natDegree+n))

/-- The actual small determinant in a last-row convention. The polynomial
columns run from `max(n-degree v,0)` through `n+degree u`, with exactly
`degree u+min(n,degree v)` native constraints. -/
def rationalModificationSmallBorderMatrix (L T : 𝕜[X] →ₗ[𝕜] 𝕜)
    (u v : 𝕜[X]) (n : ℕ) :
    Matrix (Fin (u.natDegree + min n v.natDegree) ⊕ Fin 1)
      (Fin (u.natDegree + min n v.natDegree) ⊕ Fin 1) 𝕜[X] :=
  fromBlocks ((rationalModificationSmallMatrix L T u v n).map C)
    (fun i _ => C (rationalModificationSmallLeadingConstraints L T u v n i))
    (fun _ j => monicOrthogonalPolynomial L (n-v.natDegree+j.val))
    (fun _ _ => monicOrthogonalPolynomial L (u.natDegree+n))

set_option maxHeartbeats 1000000 in
private theorem small_border_det_eq
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (u v : 𝕜[X]) (n : ℕ)
    (hdet : (rationalModificationSmallMatrix L T u v n).det ≠ 0) :
    (rationalModificationSmallBorderMatrix L T u v n).det =
      C (rationalModificationSmallMatrix L T u v n).det *
        (monicOrthogonalPolynomial L (u.natDegree+n) -
          ∑ j : Fin (u.natDegree + min n v.natDegree),
            C (((rationalModificationSmallMatrix L T u v n)⁻¹ *ᵥ
              rationalModificationSmallLeadingConstraints L T u v n) j) *
                monicOrthogonalPolynomial L (n-v.natDegree+j.val)) := by
  let M := rationalModificationSmallMatrix L T u v n
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  let : Invertible (M.map C) :=
    { invOf := (M⁻¹).map C
      invOf_mul_self := by rw [← Matrix.map_mul, M.nonsing_inv_mul hunit]; simp
      mul_invOf_self := by rw [← Matrix.map_mul, M.mul_nonsing_inv hunit]; simp }
  rw [rationalModificationSmallBorderMatrix, det_fromBlocks₁₁,
    det_eq_elem_of_subsingleton _ (0 : Fin 1)]
  rw [show (M.map C).det = C M.det from (RingHom.map_det C M).symm]
  congr 1
  change monicOrthogonalPolynomial L (u.natDegree+n) -
      ∑ j : Fin (u.natDegree + min n v.natDegree),
        (∑ i : Fin (u.natDegree + min n v.natDegree),
          monicOrthogonalPolynomial L (n-v.natDegree+i.val) * C (M⁻¹ i j)) *
            C (rationalModificationSmallLeadingConstraints L T u v n j) =
      monicOrthogonalPolynomial L (u.natDegree+n) -
        ∑ i : Fin (u.natDegree + min n v.natDegree),
          C (∑ j : Fin (u.natDegree + min n v.natDegree), M⁻¹ i j *
            rationalModificationSmallLeadingConstraints L T u v n j) *
              monicOrthogonalPolynomial L (n-v.natDegree+i.val)
  simp only [map_sum, map_mul, sum_mul]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- The actual small bordered determinant is original numerator times modified
monic polynomial, with exact scalar `det M/leadingCoeff u`. Its normalization
has already been proved nonzero, and `degree v>n` is included.
Source: focused mathematical reroutes, CU6--CU8.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationSmallBorderMatrix_eq
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {u v : 𝕜[X]} (hu : u ≠ 0) (hv : v ≠ 0)
    (hTv : ∀ p, T (v*p) = L p) {n : ℕ}
    (hL : ∀ j ≤ u.natDegree+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    (rationalModificationSmallBorderMatrix L T u v n).det =
      C ((rationalModificationSmallMatrix L T u v n).det/u.leadingCoeff) *
        u * monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n := by
  let M := rationalModificationSmallMatrix L T u v n
  let b := rationalModificationSmallLeadingConstraints L T u v n
  let c := M⁻¹ *ᵥ b
  let lower : 𝕜[X] := ∑ j : Fin (u.natDegree + min n v.natDegree),
    C (c j) * monicOrthogonalPolynomial L (n-v.natDegree+j.val)
  let P := monicOrthogonalPolynomial L (u.natDegree+n) - lower
  have hdet : M.det ≠ 0 := det_rationalModificationSmallMatrix_ne_zero L T hu hv hTv
    (fun j hj => hL j hj.le) hn
  have hMc : M *ᵥ c = b := by
    dsimp only [c]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  have hindex (j : Fin (u.natDegree + min n v.natDegree)) :
      n-v.natDegree+j.val < u.natDegree+n := by have := j.isLt; omega
  have hlower : lower.degree < (u.natDegree+n : ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j _
    rw [C_mul']
    apply (degree_smul_le _ _).trans_lt
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
    exact_mod_cast hindex j
  have htop : (monicOrthogonalPolynomial L (u.natDegree+n)).degree =
      ((u.natDegree+n : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L _).ne_zero,
      natDegree_monicOrthogonalPolynomial]
  have hPmonic : P.Monic := (monic_monicOrthogonalPolynomial L _).sub_of_left (hlower.trans_eq htop.symm)
  have hPdeg : P.degree = ((u.natDegree+n : ℕ) : WithBot ℕ) :=
    (degree_sub_eq_left_of_degree_lt (hlower.trans_eq htop.symm)).trans htop
  have hPC (i : Fin (u.natDegree + min n v.natDegree)) :
      rationalModificationConstraint T u (min n v.natDegree) i P = 0 := by
    have hi := congrFun hMc i
    simp only [M, c, b, rationalModificationSmallMatrix, Matrix.mulVec, dotProduct] at hi
    dsimp only [P, lower]
    rw [map_sub, map_sum]
    simp only [C_mul', map_smul, smul_eq_mul]
    rw [show (∑ j : Fin (u.natDegree + min n v.natDegree), c j *
        rationalModificationConstraint T u (min n v.natDegree) i
          (monicOrthogonalPolynomial L (n-v.natDegree+j.val))) = b i by
      simpa only [M, rationalModificationSmallMatrix, Matrix.mulVec, dotProduct, mul_comm] using congrFun hMc i]
    simp only [b, rationalModificationSmallLeadingConstraints, sub_self]
  have horth (q : 𝕜[X]) (hq : q.degree < (n-v.natDegree : ℕ)) : L (P*q) = 0 := by
    dsimp only [P, lower]
    rw [sub_mul, map_sub,
      (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL _ le_rfl)).orthogonal q
        (hq.trans_le (by exact_mod_cast (show n-v.natDegree ≤ u.natDegree+n by omega))),
      sum_mul, map_sum]
    simp only [C_mul', smul_mul_assoc, map_smul]
    rw [sum_eq_zero (fun j _ => by
      rw [(isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L (hL _ (hindex j).le)).orthogonal q
        (hq.trans_le (by exact_mod_cast Nat.le_add_right (n-v.natDegree) j.val)), smul_zero])]
    simp
  have hfull := (rationalModificationConstraint_small_iff_full L T hu hv hTv n P horth).mp hPC
  let π := monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n
  have hπ := isMonicOrthogonalPolynomial_monicOrthogonalPolynomial (polynomialWeightedFunctional T u) hn
  have hπm : π.Monic := hπ.monic
  have hUdeg : (u*π).degree = ((u.natDegree+n : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_eq_natDegree hu, degree_eq_natDegree hπ.monic.ne_zero,
      hπ.natDegree_eq, Nat.cast_add]
  have hNdeg : (C u.leadingCoeff*P).degree = ((u.natDegree+n : ℕ) : WithBot ℕ) := by
    rw [degree_C_mul (leadingCoeff_ne_zero.mpr hu), hPdeg]
  have hdiff : (C u.leadingCoeff*P-u*π).degree < (u.natDegree+n : ℕ) := by
    apply (degree_sub_lt_left (hNdeg.trans hUdeg.symm)
      (mul_ne_zero (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hu)) hPmonic.ne_zero) ?_).trans_eq hNdeg
    simp only [leadingCoeff_mul, leadingCoeff_C, hPmonic.leadingCoeff, hπm.leadingCoeff, mul_one]
  have hπC : ∀ i, rationalModificationConstraint T u n i (u*π) = 0 := by
    apply (rationalModificationConstraint_eq_zero_iff T hu n _).mpr
    refine ⟨dvd_mul_right _ _, ?_⟩
    intro r
    simpa only [π, polynomialWeightedFunctional_apply, mul_assoc] using
      functional_monicOrthogonalPolynomial_mul_X_pow_eq_zero (polynomialWeightedFunctional T u) hn r
  have heq : C u.leadingCoeff*P = u*π := sub_eq_zero.mp
    (eq_zero_of_rationalModificationConstraint_eq_zero T hu hn hdiff (by
      intro i
      rw [map_sub, C_mul', map_smul, hfull i, smul_zero, hπC i, sub_self]))
  rw [small_border_det_eq L T u v n hdet]
  change C M.det * P = _
  rw [mul_assoc, ← heq, ← mul_assoc, ← map_mul,
    div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hu)]

/-- The actual compressed inverse system gives the explicit original-basis
expansion of the modified numerator. In particular a quadratic denominator
and constant numerator involve exactly the last three original polynomials
when `n≥2`, and the initial bordered cases otherwise. Source: CU6--CU8.
atlas: christoffel-uvarov-modification (partial) -/
theorem mul_monicOrthogonalPolynomial_eq_small_expansion
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {u v : 𝕜[X]} (hu : u ≠ 0) (hv : v ≠ 0)
    (hTv : ∀ p, T (v*p) = L p) {n : ℕ}
    (hL : ∀ j ≤ u.natDegree+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    u*monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n =
      C u.leadingCoeff * (monicOrthogonalPolynomial L (u.natDegree+n) -
        ∑ j : Fin (u.natDegree+min n v.natDegree),
          C (((rationalModificationSmallMatrix L T u v n)⁻¹ *ᵥ
            rationalModificationSmallLeadingConstraints L T u v n) j) *
              monicOrthogonalPolynomial L (n-v.natDegree+j.val)) := by
  have hdet := det_rationalModificationSmallMatrix_ne_zero L T hu hv hTv (fun j hj => hL j hj.le) hn
  have he := small_border_det_eq L T u v n hdet
  rw [det_rationalModificationSmallBorderMatrix_eq L T hu hv hTv hL hn, mul_assoc] at he
  have h := congrArg (fun p : 𝕜[X] => C u.leadingCoeff*p) he
  rw [← mul_assoc, ← map_mul,
    mul_div_cancel₀ _ (leadingCoeff_ne_zero.mpr hu)] at h
  apply mul_left_cancel₀ (C_ne_zero.mpr hdet)
  exact h.trans (by ring)

end NLAlib
