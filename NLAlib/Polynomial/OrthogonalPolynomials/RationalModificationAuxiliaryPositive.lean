import NLAlib.Polynomial.OrthogonalPolynomials.ComplexCauchyRows
import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationAuxiliaryNormalization

/-!
# Positive-measure specialization of the auxiliary-power determinant

This is the actual source measure constructor for orders below the divisor
degree. Positivity and adequate original support derive the required finite
modified nondegeneracy; the matrix's rows are actual complex Cauchy integrals.
Source: Gautschi (2004), Theorem 2.53.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set
namespace NLAlib

/-- The source auxiliary-power determinant equals a nonzero constant times the
actual modified measure polynomial. Its normalized denominator rows are the
actual original measure's Cauchy integrals. Nonreal simple roots are permitted.
atlas: christoffel-uvarov-modification (partial) -/
theorem exists_det_auxiliaryFirstRow_eq_rationalPolynomialModifiedMeasure
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ t ∂μ, t ∈ Icc a b) (u v : ℝ[X]) (hu : u ≠ 0) (hv : v ≠ 0)
    (hv0 : ∀ t ∈ Icc a b, v.eval t ≠ 0)
    (hpos : ∀ t ∈ Icc a b, 0 < u.eval t/v.eval t)
    (x : Fin u.natDegree → ℂ) (z : Fin v.natDegree → ℂ)
    (hx : Function.Injective x) (hz : Function.Injective z)
    (hux : u.map Complex.ofRealHom = C (u.leadingCoeff : ℂ)*Lagrange.nodal Finset.univ x)
    (hvz : v.map Complex.ofRealHom = C (v.leadingCoeff : ℂ)*Lagrange.nodal Finset.univ z)
    {n : ℕ} (hm : n ≤ v.natDegree)
    (hcard : ((u.natDegree+n : ℕ) : ℕ∞) ≤ μ.support.encard) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    let hr := hasDividedPolynomialMoments_of_ae_mem_Icc hs hv0
    let hc := hasComplexDividedPolynomialMoments_of_ae_mem_Icc hs
      (v := v.map Complex.ofRealHom) (by
        intro t ht
        change (v.map Complex.ofRealHom).eval (Complex.ofRealHom t) ≠ 0
        rw [eval_map_apply]
        exact Complex.ofReal_ne_zero.mpr (hv0 t ht))
    let hpa : ∀ᵐ t ∂μ, 0 ≤ u.eval t/v.eval t := hs.mono fun t ht => (hpos t ht).le
    let hν := hasPolynomialMoments_rationalPolynomialModifiedMeasure μ u v hr hpa
    let L := complexPolynomialIntegral μ hμ
    let T := complexDividedPolynomialIntegral μ (v.map Complex.ofRealHom) hc
    ∃ c : ℂ, c ≠ 0 ∧
      (rationalModificationAuxiliaryFirstRowMatrix L ((v.leadingCoeff : ℂ) • T) x z hm).det =
        C c * u.map Complex.ofRealHom *
          (monicOrthogonalPolynomial (polynomialIntegral (rationalPolynomialModifiedMeasure μ u v) hν) n).map
            Complex.ofRealHom ∧
      ∀ (p : ℂ[X]) (i : Fin v.natDegree),
        ((v.leadingCoeff : ℂ) • T) (p*rootCofactor z i) =
          ∫ t : ℝ, p.eval (t : ℂ)/((t : ℂ)-z i) ∂μ := by
  dsimp only
  let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
  let hr := hasDividedPolynomialMoments_of_ae_mem_Icc hs hv0
  let hc := hasComplexDividedPolynomialMoments_of_ae_mem_Icc hs
    (v := v.map Complex.ofRealHom) (by
      intro t ht
      change (v.map Complex.ofRealHom).eval (Complex.ofRealHom t) ≠ 0
      rw [eval_map_apply]
      exact Complex.ofReal_ne_zero.mpr (hv0 t ht))
  let hpa : ∀ᵐ t ∂μ, 0 ≤ u.eval t/v.eval t := hs.mono fun t ht => (hpos t ht).le
  let hν := hasPolynomialMoments_rationalPolynomialModifiedMeasure μ u v hr hpa
  let L := complexPolynomialIntegral μ hμ
  let T := complexDividedPolynomialIntegral μ (v.map Complex.ofRealHom) hc
  have hcu : (u.leadingCoeff : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (leadingCoeff_ne_zero.mpr hu)
  have hcv : (v.leadingCoeff : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (leadingCoeff_ne_zero.mpr hv)
  have hps : ∀ᵐ t ∂μ, 0 < u.eval t/v.eval t := hs.mono hpos
  have hsn : (n : ℕ∞) ≤ μ.support.encard :=
    ((by exact_mod_cast (show n ≤ u.natDegree+n by omega) : (n : ℕ∞) ≤ u.natDegree+n).trans hcard)
  have heq : complexPolynomialIntegral (rationalPolynomialModifiedMeasure μ u v) hν =
      polynomialWeightedFunctional T (u.map Complex.ofRealHom) :=
    complexPolynomialIntegral_rationalPolynomialModifiedMeasure_eq u v hr hc hpa
  have hn : hankelMomentDet (polynomialWeightedFunctional T (u.map Complex.ofRealHom)) n ≠ 0 := by
    rw [← heq]
    apply hankelMomentDet_complexPolynomialIntegral_ne_zero hν
    rw [support_rationalPolynomialModifiedMeasure_eq hps]
    exact hsn
  have hnr : hankelMomentDet (polynomialIntegral (rationalPolynomialModifiedMeasure μ u v) hν) n ≠ 0 :=
    hankelMomentDet_rationalPolynomialModifiedMeasure_ne_zero u v hr hps hsn
  have hp : monicOrthogonalPolynomial (polynomialWeightedFunctional T (u.map Complex.ofRealHom)) n =
      (monicOrthogonalPolynomial (polynomialIntegral (rationalPolynomialModifiedMeasure μ u v) hν) n).map
        Complex.ofRealHom := by
    rw [← heq]
    exact monicOrthogonalPolynomial_complexPolynomialIntegral_eq_map hν hnr
  have hd := det_rationalModificationAuxiliaryFirstRowMatrix_nonmonic L T hcu hcv x z hx hz hux hm hn
  dsimp only at hd
  refine ⟨_,hd.2,hd.1.trans (by rw [hp]),?_⟩
  intro p i
  apply smul_complexDividedPolynomialIntegral_rootCofactor_eq_cauchy hcv z hvz hc _ p i
  filter_upwards [hs] with t ht
  change (v.map Complex.ofRealHom).eval (Complex.ofRealHom t) ≠ 0
  rw [eval_map_apply]
  exact Complex.ofReal_ne_zero.mpr (hv0 t ht)

end NLAlib
