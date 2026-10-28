import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationMeasure
import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationSmallDeterminant
import NLAlib.Polynomial.OrthogonalPolynomials.MomentPositivity

/-!
# Positive compactly supported rational modifications

A strictly positive rational density preserves the support. Enough original
support points therefore imply both finite original and modified Hankel
nondegeneracy used by the Christoffel--Uvarov determinant. Neither normalization
nor modified nondegeneracy is assumed of the computed output.
Source: Gautschi (2004), Theorems 2.52--2.53, finite-order interpretation.
-/

noncomputable section
open Polynomial MeasureTheory Set
namespace NLAlib

/-- A strictly positive rational density preserves the topological support. -/
theorem support_rationalPolynomialModifiedMeasure_eq {μ : Measure ℝ} {u v : ℝ[X]}
    (hpos : ∀ᵐ x ∂μ, 0 < u.eval x/v.eval x) :
    (rationalPolynomialModifiedMeasure μ u v).support = μ.support := by
  apply Set.Subset.antisymm
  · exact (withDensity_absolutelyContinuous μ _).support_mono
  · apply (withDensity_absolutelyContinuous' (by fun_prop) ?_).support_mono
    filter_upwards [hpos] with x hx
    exact (ENNReal.ofReal_pos.mpr hx).ne'

/-- The finite modified Hankel system is nonsingular as a consequence of
strict positivity and enough support, with the exact native measure functional.
atlas: christoffel-uvarov-modification (partial) -/
theorem hankelMomentDet_rationalPolynomialModifiedMeasure_ne_zero
    {μ : Measure ℝ} (u v : ℝ[X]) (hdiv : HasDividedPolynomialMoments μ v)
    (hpos : ∀ᵐ x ∂μ, 0 < u.eval x/v.eval x) {n : ℕ}
    (hs : (n : ℕ∞) ≤ μ.support.encard) :
    hankelMomentDet (polynomialIntegral (rationalPolynomialModifiedMeasure μ u v)
      (hasPolynomialMoments_rationalPolynomialModifiedMeasure μ u v hdiv
        (hpos.mono fun _ h => h.le))) n ≠ 0 := by
  apply hankelMomentDet_ne_zero_of_le_support_encard
  rw [support_rationalPolynomialModifiedMeasure_eq hpos]
  exact hs

/-- The actual positive modified-measure polynomial is the source's compressed
determinant divided by its proved nonzero normalization and by `u`. The minimal
uniform support bound is `n+degree u`; equality and denominator degree above `n`
are both retained.
atlas: christoffel-uvarov-modification (partial) -/
theorem monicOrthogonalPolynomial_rationalPolynomialModifiedMeasure_eq_det_div
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) (u v : ℝ[X]) (hu : u ≠ 0) (hv : v ≠ 0)
    (hv0 : ∀ x ∈ Icc a b, v.eval x ≠ 0)
    (hpos : ∀ x ∈ Icc a b, 0 < u.eval x/v.eval x) {n : ℕ}
    (hcard : ((u.natDegree+n : ℕ) : ℕ∞) ≤ μ.support.encard) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    let hdiv := hasDividedPolynomialMoments_of_ae_mem_Icc hs hv0
    let hpa : ∀ᵐ x ∂μ, 0 ≤ u.eval x/v.eval x := hs.mono fun x hx => (hpos x hx).le
    let hν := hasPolynomialMoments_rationalPolynomialModifiedMeasure μ u v hdiv hpa
    let L := polynomialIntegral μ hμ
    let T := dividedPolynomialIntegral μ v hdiv
    let D := rationalModificationSmallFirstRowMatrix L T u v n
    monicOrthogonalPolynomial (polynomialIntegral (rationalPolynomialModifiedMeasure μ u v) hν) n =
      ((u.leadingCoeff / D.det.coeff (u.natDegree+n)) • D.det) / u ∧
      D.det.coeff (u.natDegree+n) ≠ 0 := by
  dsimp only
  let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
  let hdiv := hasDividedPolynomialMoments_of_ae_mem_Icc hs hv0
  let hpa : ∀ᵐ x ∂μ, 0 ≤ u.eval x/v.eval x := hs.mono fun x hx => (hpos x hx).le
  have hps : ∀ᵐ x ∂μ, 0 < u.eval x/v.eval x := hs.mono hpos
  let L := polynomialIntegral μ hμ
  let T := dividedPolynomialIntegral μ v hdiv
  have hTv (p : ℝ[X]) : T (v*p) = L p :=
    dividedPolynomialIntegral_denominator_mul hμ v hdiv (hs.mono hv0) p
  have hL (j : ℕ) (hj : j ≤ u.natDegree+n) : hankelMomentDet L j ≠ 0 :=
    hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hj : (j : ℕ∞) ≤ u.natDegree+n).trans hcard)
  have heq := polynomialIntegral_rationalPolynomialModifiedMeasure_eq μ u v hdiv hpa
  have hn : hankelMomentDet (polynomialWeightedFunctional T u) n ≠ 0 := by
    rw [← heq]
    exact hankelMomentDet_rationalPolynomialModifiedMeasure_ne_zero u v hdiv hps
      ((by exact_mod_cast (show n ≤ u.natDegree+n by omega) : (n : ℕ∞) ≤ u.natDegree+n).trans hcard)
  rw [heq]
  exact ⟨monicOrthogonalPolynomial_eq_rationalModification_small_det_div L T hu hv hTv hL hn,
    coeff_det_rationalModificationSmallFirstRowMatrix_self_ne_zero L T hu hv hTv hL hn⟩

end NLAlib
