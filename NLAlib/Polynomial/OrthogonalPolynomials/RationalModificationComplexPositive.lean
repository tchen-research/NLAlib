import NLAlib.Polynomial.OrthogonalPolynomials.ComplexDividedMoments
import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationRootNormalization
import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationPositive

/-!
# The source determinant for positive measures and complex modification roots

Real numerator and denominator polynomials may have nonreal simple roots. The
complex Bochner integral adapter and scalar normalization give the root/Cauchy
determinant of the actual positive modified measure. Finite Hankel invertibility
is derived from the source support condition, not postulated of the result.
Source: Gautschi (2004), Theorems 2.52--2.53.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set
namespace NLAlib

/-- The source complex-root determinant represents the actual positive modified
measure's canonical polynomial. The roots are complete simple-root lists of the
given real polynomials, and their leading coefficients need not be positive.
The scalar is the actual nonzero root/Cauchy minor normalization.
atlas: christoffel-uvarov-modification (partial) -/
theorem exists_det_rootFirstRow_eq_rationalPolynomialModifiedMeasure
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ t ∂μ, t ∈ Icc a b) (u v : ℝ[X]) (hu : u ≠ 0) (hv : v ≠ 0)
    (hv0 : ∀ t ∈ Icc a b, v.eval t ≠ 0)
    (hpos : ∀ t ∈ Icc a b, 0 < u.eval t/v.eval t)
    (x : Fin u.natDegree → ℂ) (z : Fin v.natDegree → ℂ)
    (hx : Function.Injective x) (hz : Function.Injective z)
    (hux : u.map Complex.ofRealHom = C (u.leadingCoeff : ℂ) * Lagrange.nodal Finset.univ x)
    (hvz : v.map Complex.ofRealHom = C (v.leadingCoeff : ℂ) * Lagrange.nodal Finset.univ z)
    {n : ℕ} (hm : v.natDegree ≤ n)
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
      (rationalModificationRootFirstRowMatrix L ((v.leadingCoeff : ℂ) • T) x z n).det =
        C c * u.map Complex.ofRealHom *
          (monicOrthogonalPolynomial (polynomialIntegral (rationalPolynomialModifiedMeasure μ u v) hν) n).map
            Complex.ofRealHom := by
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
  have hTv (p : ℂ[X]) : T (v.map Complex.ofRealHom*p) = L p := by
    apply complexDividedPolynomialIntegral_denominator_mul hμ _ hc
    filter_upwards [hs] with t ht
    change (v.map Complex.ofRealHom).eval (Complex.ofRealHom t) ≠ 0
    rw [eval_map_apply]
    exact Complex.ofReal_ne_zero.mpr (hv0 t ht)
  have hL (j : ℕ) (hj : j ≤ u.natDegree+n) : hankelMomentDet L j ≠ 0 :=
    hankelMomentDet_complexPolynomialIntegral_ne_zero hμ
      ((by exact_mod_cast hj : (j : ℕ∞) ≤ u.natDegree+n).trans hcard)
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
  have hd := det_rationalModificationRootFirstRowMatrix_nonmonic L T hcu hcv x z hx hz
    hux hvz hTv hm hL hn
  dsimp only at hd
  refine ⟨_, hd.2, ?_⟩
  exact hd.1.trans (by rw [hp])

end NLAlib
