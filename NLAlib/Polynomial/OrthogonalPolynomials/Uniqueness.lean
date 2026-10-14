import NLAlib.Polynomial.OrthogonalPolynomials.Basic

/-!
# Uniqueness of monic orthogonal polynomials

Monic lower-degree orthogonality determines a polynomial whenever squared bilinear
norms do not vanish in the lower-degree space. Source: Gautschi (2004), Chapter 1.
This interface is used by general-measure quadrature and the Lanczos measure bridge.
-/

noncomputable section

open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [Field 𝕜] {L : 𝕜[X] →ₗ[𝕜] 𝕜} {n : ℕ} {p q : 𝕜[X]}

/-- Monic orthogonality is unique whenever its lower-degree bilinear pairing is
nondegenerate. This includes complex formal functionals with isotropic vectors. -/
theorem IsMonicOrthogonalPolynomial.eq_of_nondegenerate
    (hp : IsMonicOrthogonalPolynomial L n p) (hq : IsMonicOrthogonalPolynomial L n q)
    (hL : ∀ r : 𝕜[X], r.degree < n →
      (∀ s : 𝕜[X], s.degree < n → L (r * s) = 0) → r = 0) : p = q := by
  have hpd : p.degree = n := by rw [degree_eq_natDegree hp.monic.ne_zero, hp.natDegree_eq]
  have hqd : q.degree = n := by rw [degree_eq_natDegree hq.monic.ne_zero, hq.natDegree_eq]
  have hdiff : (p - q).degree < n := by
    rw [← hpd]
    apply degree_sub_lt_left (hpd.trans hqd.symm) hp.monic.ne_zero
    exact hp.monic.leadingCoeff.trans hq.monic.leadingCoeff.symm
  apply sub_eq_zero.mp
  apply hL (p - q) hdiff
  intro s hs
  rw [sub_mul, map_sub, hp.orthogonal _ hs, hq.orthogonal _ hs, sub_self]

/-- Two monic orthogonal polynomials of the same degree coincide if all lower-degree
nonzero polynomials have nonzero squared bilinear norm. This applies to positive real
moment functionals and does not require an inner-product-space instance. -/
theorem IsMonicOrthogonalPolynomial.eq_of_nonzero_sq
    (hp : IsMonicOrthogonalPolynomial L n p) (hq : IsMonicOrthogonalPolynomial L n q)
    (hL : ∀ r : 𝕜[X], r.degree < n → r ≠ 0 → L (r ^ 2) ≠ 0) : p = q := by
  have hpd : p.degree = n := by rw [degree_eq_natDegree hp.monic.ne_zero, hp.natDegree_eq]
  have hqd : q.degree = n := by rw [degree_eq_natDegree hq.monic.ne_zero, hq.natDegree_eq]
  have hdiff : (p - q).degree < n := by
    rw [← hpd]
    apply degree_sub_lt_left (hpd.trans hqd.symm) hp.monic.ne_zero
    exact hp.monic.leadingCoeff.trans hq.monic.leadingCoeff.symm
  have hzero : L ((p - q) ^ 2) = 0 := by
    rw [pow_two, sub_mul, map_sub, hp.orthogonal _ hdiff, hq.orthogonal _ hdiff, sub_self]
  by_contra hne
  exact hL (p - q) hdiff (sub_ne_zero.mpr hne) hzero

end NLAlib
