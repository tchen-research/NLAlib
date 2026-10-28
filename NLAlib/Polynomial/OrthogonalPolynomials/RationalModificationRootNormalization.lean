import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationRootDeterminant
import NLAlib.Polynomial.OrthogonalPolynomials.MomentScaling

/-!
# Leading coefficients in the root presentation

Numerator and denominator polynomials need not be monic. Their nonzero leading
coefficients are retained in the actual source determinant normalization; a
possibly negative or complex scalar does not change the canonical monic family.
-/

noncomputable section
open Polynomial
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜] {l m : ℕ}

/-- Leading-coefficient normalization recovers the original functional when
the monic nodal denominator is cleared. -/
theorem smul_dividedFunctional_nodal_mul
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {v : 𝕜[X]} {cv : 𝕜} (z : Fin m → 𝕜)
    (hv : v = C cv * Lagrange.nodal Finset.univ z)
    (hTv : ∀ p, T (v*p) = L p) (p : 𝕜[X]) :
    (cv • T) (Lagrange.nodal Finset.univ z * p) = L p := by
  have h := hTv p
  rw [hv, mul_assoc, C_mul', map_smul] at h
  exact h

/-- Normalizing numerator and denominator scales the modified functional by
their leading-coefficient ratio. -/
theorem polynomialWeightedFunctional_smul_nodal
    (T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} {cu : 𝕜} (hcu : cu ≠ 0)
    (cv : 𝕜) (x : Fin l → 𝕜) (hu : u = C cu * Lagrange.nodal Finset.univ x) :
    polynomialWeightedFunctional (cv • T) (Lagrange.nodal Finset.univ x) =
      (cv/cu) • polynomialWeightedFunctional T u := by
  apply LinearMap.ext
  intro p
  simp only [polynomialWeightedFunctional_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hu, mul_assoc, C_mul', map_smul, smul_eq_mul]
  field_simp

/-- The source root/Cauchy first-row determinant for arbitrary nonzero leading
coefficients is exactly a nonzero scalar times `u πhat_n`. No monicity of the
modifying polynomials or reality of their simple roots is imposed.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationRootFirstRowMatrix_nonmonic
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {u v : 𝕜[X]} {cu cv : 𝕜}
    (hcu : cu ≠ 0) (hcv : cv ≠ 0) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z)
    (hu : u = C cu * Lagrange.nodal Finset.univ x)
    (hv : v = C cv * Lagrange.nodal Finset.univ z)
    (hTv : ∀ p, T (v*p) = L p) {n : ℕ} (hm : m ≤ n)
    (hL : ∀ j ≤ l+n, hankelMomentDet L j ≠ 0)
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    let D := rationalModificationRootFirstRowMatrix L (cv • T) x z n
    let c := (-1 : 𝕜)^(l+m) * (rationalModificationRootMatrix L (cv • T) x z n).det / cu
    D.det = C c * u * monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n ∧ c ≠ 0 := by
  dsimp only
  have hratio : cv/cu ≠ 0 := div_ne_zero hcv hcu
  have he := polynomialWeightedFunctional_smul_nodal T hcu cv x hu
  have hnc : hankelMomentDet (polynomialWeightedFunctional (cv • T)
      (Lagrange.nodal Finset.univ x)) n ≠ 0 := by
    rw [he, hankelMomentDet_smul]
    exact mul_ne_zero (pow_ne_zero _ hratio) hn
  have hp : monicOrthogonalPolynomial (polynomialWeightedFunctional (cv • T)
      (Lagrange.nodal Finset.univ x)) n = monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n := by
    rw [he, monicOrthogonalPolynomial_smul _ hratio _ hn]
  have hd := det_rationalModificationRootFirstRowMatrix_eq_mul_monicOrthogonalPolynomial L (cv • T)
    x z hx hz (smul_dividedFunctional_nodal_mul L T z hv hTv) hm hL hnc
  constructor
  · rw [hd.1, hp]
    let a := (-1 : 𝕜)^(l+m) * (rationalModificationRootMatrix L (cv • T) x z n).det
    change C a * Lagrange.nodal Finset.univ x * _ = C (a/cu) * u * _
    rw [hu, ← mul_assoc (C (a/cu)) (C cu) (Lagrange.nodal Finset.univ x),
      ← map_mul, div_mul_cancel₀ _ hcu]
  · exact div_ne_zero hd.2 hcu

end NLAlib
