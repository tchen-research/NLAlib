import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationAuxiliaryDeterminant
import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationRootNormalization

/-!
# Nonmonic normalization of the source auxiliary-power determinant

Arbitrary nonzero leading coefficients only scale the finite functional and
the actual determinant normalization. The canonical monic output is unchanged.
-/

noncomputable section
open Polynomial
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜] {l m n : ℕ}

/-- The source first-row determinant below the denominator degree, with the
actual nonzero normalization for arbitrary numerator/denominator leading
coefficients. Source: Gautschi (2004), Theorem 2.53.
atlas: christoffel-uvarov-modification (partial) -/
theorem det_rationalModificationAuxiliaryFirstRowMatrix_nonmonic
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {u : 𝕜[X]} {cu cv : 𝕜}
    (hcu : cu ≠ 0) (hcv : cv ≠ 0) (x : Fin l → 𝕜) (z : Fin m → 𝕜)
    (hx : Function.Injective x) (hz : Function.Injective z)
    (hu : u = C cu * Lagrange.nodal Finset.univ x) (hm : n ≤ m)
    (hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0) :
    let D := rationalModificationAuxiliaryFirstRowMatrix L (cv • T) x z hm
    let c := (rationalModificationAuxiliaryMatrix L (cv • T) x z hm).det / cu
    D.det = C c * u * monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n ∧ c ≠ 0 := by
  dsimp only
  have hratio : cv/cu ≠ 0 := div_ne_zero hcv hcu
  have he := polynomialWeightedFunctional_smul_nodal T hcu cv x hu
  have hnc : hankelMomentDet (polynomialWeightedFunctional (cv • T)
      (Lagrange.nodal Finset.univ x)) n ≠ 0 := by
    rw [he,hankelMomentDet_smul]
    exact mul_ne_zero (pow_ne_zero _ hratio) hn
  have hp : monicOrthogonalPolynomial (polynomialWeightedFunctional (cv • T)
      (Lagrange.nodal Finset.univ x)) n = monicOrthogonalPolynomial (polynomialWeightedFunctional T u) n := by
    rw [he,monicOrthogonalPolynomial_smul _ hratio _ hn]
  have hd := det_rationalModificationAuxiliaryFirstRowMatrix_eq L (cv • T) x z hx hz hm hnc
  constructor
  · rw [hd.1,hp]
    let a := (rationalModificationAuxiliaryMatrix L (cv • T) x z hm).det
    change C a * Lagrange.nodal Finset.univ x * _ = C (a/cu) * u * _
    rw [hu,← mul_assoc (C (a/cu)) (C cu) (Lagrange.nodal Finset.univ x),
      ← map_mul,div_mul_cancel₀ _ hcu]
  · exact div_ne_zero hd.2 hcu

end NLAlib
