import NLAlib.Polynomial.OrthogonalPolynomials.Christoffel
import NLAlib.Polynomial.OrthogonalPolynomials.MeasureMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual moment functional of a rational measure modification

Division by a fixed pole-free polynomial defines a signed linear functional.
Multiplication by the numerator then realizes the positive modified measure.
Source: focused rational-modification reroute, Section 4 (CU1)--(CU5).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set
namespace NLAlib

/-- Every polynomial divided by the fixed denominator is integrable. -/
def HasDividedPolynomialMoments (μ : Measure ℝ) (v : ℝ[X]) : Prop :=
  ∀ p : ℝ[X], Integrable (fun x => p.eval x / v.eval x) μ

/-- The compact-support and pole-free source hypotheses imply all divided
polynomial moments, irrespective of the denominator degree. -/
theorem hasDividedPolynomialMoments_of_ae_mem_Icc {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {v : ℝ[X]}
    (hv : ∀ x ∈ Icc a b, v.eval x ≠ 0) : HasDividedPolynomialMoments μ v := by
  intro p
  have hc : ContinuousOn (fun x => p.eval x/v.eval x) (Icc a b) :=
    p.continuous.continuousOn.div v.continuous.continuousOn hv
  refine (hc.integrableOn_compact (isCompact_Icc (a := a) (b := b))).integrable_of_ae_notMem_eq_zero ?_
  filter_upwards [hμ] with x hx hnot
  exact (hnot hx).elim

/-- The actual inverse-weight moment functional. The denominator may have
either sign; the positive numerator/denominator ratio is imposed separately.
Source: focused rational-modification reroute, inverse moments in CU1. -/
def dividedPolynomialIntegral (μ : Measure ℝ) (v : ℝ[X])
    (hμ : HasDividedPolynomialMoments μ v) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x, p.eval x / v.eval x ∂μ
  map_add' p q := by
    simp only [eval_add, add_div]
    exact integral_add (hμ p) (hμ q)
  map_smul' c p := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply, mul_div_assoc]
    exact integral_const_mul c (fun x => p.eval x/v.eval x)

/-- The inverse-weight functional evaluates to the actual divided integral. -/
@[simp] theorem dividedPolynomialIntegral_apply (μ : Measure ℝ) (v : ℝ[X])
    (hμ : HasDividedPolynomialMoments μ v) (p : ℝ[X]) :
    dividedPolynomialIntegral μ v hμ p = ∫ x, p.eval x/v.eval x ∂μ := rfl

/-- The modified functional used by the finite algebraic construction is exactly
the original measure integral weighted by the given rational function.
Source: focused rational-modification reroute, definition of modified L. -/
theorem polynomialWeightedFunctional_dividedPolynomialIntegral_apply
    (μ : Measure ℝ) (u v : ℝ[X]) (hμ : HasDividedPolynomialMoments μ v) (p : ℝ[X]) :
    polynomialWeightedFunctional (dividedPolynomialIntegral μ v hμ) u p =
      ∫ x, u.eval x*p.eval x/v.eval x ∂μ := by
  simp only [polynomialWeightedFunctional, dividedPolynomialIntegral_apply, eval_mul]
  rfl

/-- The native positive measure with rational density. Under nonnegative ratio
the `ofReal` truncation does not alter the intended modification. -/
def rationalPolynomialModifiedMeasure (μ : Measure ℝ) (u v : ℝ[X]) : Measure ℝ :=
  μ.withDensity (fun x => ENNReal.ofReal (u.eval x/v.eval x))

/-- The native modified measure integrates by the actual numerator/denominator
ratio on its full measure domain. Source: rational modification in Section 4. -/
theorem integral_rationalPolynomialModifiedMeasure (μ : Measure ℝ) (u v : ℝ[X])
    (hpos : ∀ᵐ x ∂μ, 0 ≤ u.eval x/v.eval x) (f : ℝ → ℝ) :
    (∫ x, f x ∂rationalPolynomialModifiedMeasure μ u v) =
      ∫ x, u.eval x*f x/v.eval x ∂μ := by
  rw [rationalPolynomialModifiedMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hpos] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
  ring

/-- The finite construction's functional and the actual positive modified
measure have identical polynomial moments.
Source: focused rational-modification reroute, measure/function correspondence.
atlas: christoffel-uvarov-modification (partial) -/
theorem polynomialWeightedFunctional_dividedPolynomialIntegral_eq_integral_modified
    (μ : Measure ℝ) (u v : ℝ[X]) (hμ : HasDividedPolynomialMoments μ v)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ u.eval x/v.eval x) (p : ℝ[X]) :
    polynomialWeightedFunctional (dividedPolynomialIntegral μ v hμ) u p =
      ∫ x, p.eval x ∂rationalPolynomialModifiedMeasure μ u v := by
  rw [polynomialWeightedFunctional_dividedPolynomialIntegral_apply,
    integral_rationalPolynomialModifiedMeasure μ u v hpos]

/-- Multiplication by the pole-free denominator recovers the original actual
polynomial moment functional. This is the identity used to compress CU7. -/
theorem dividedPolynomialIntegral_denominator_mul
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) (v : ℝ[X])
    (hdiv : HasDividedPolynomialMoments μ v)
    (hv : ∀ᵐ x ∂μ, v.eval x ≠ 0) (p : ℝ[X]) :
    dividedPolynomialIntegral μ v hdiv (v*p) = polynomialIntegral μ hμ p := by
  rw [dividedPolynomialIntegral_apply, polynomialIntegral_apply]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [eval_mul, mul_div_cancel_left₀ _ hx]

/-- Finite divided polynomial moments and a nonnegative rational density give
all polynomial moments of the actual positive modified measure. -/
theorem hasPolynomialMoments_rationalPolynomialModifiedMeasure
    (μ : Measure ℝ) (u v : ℝ[X]) (hdiv : HasDividedPolynomialMoments μ v)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ u.eval x/v.eval x) :
    HasPolynomialMoments (rationalPolynomialModifiedMeasure μ u v) := by
  intro p
  apply (integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)).mpr
  apply (hdiv (u*p)).congr
  filter_upwards [hpos] with x hx
  simp only [eval_mul, ENNReal.toReal_ofReal hx, smul_eq_mul]
  ring

/-- The canonical native modified measure functional is the exact weighted
divided functional used by the proved finite coefficient and determinant systems.
Source: focused mathematical reroutes, definition of modified L in CU1.
atlas: christoffel-uvarov-modification (partial) -/
theorem polynomialIntegral_rationalPolynomialModifiedMeasure_eq
    (μ : Measure ℝ) (u v : ℝ[X]) (hdiv : HasDividedPolynomialMoments μ v)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ u.eval x/v.eval x) :
    polynomialIntegral (rationalPolynomialModifiedMeasure μ u v)
      (hasPolynomialMoments_rationalPolynomialModifiedMeasure μ u v hdiv hpos) =
      polynomialWeightedFunctional (dividedPolynomialIntegral μ v hdiv) u := by
  apply LinearMap.ext
  intro p
  rw [polynomialIntegral_apply,
    ← polynomialWeightedFunctional_dividedPolynomialIntegral_eq_integral_modified μ u v hdiv hpos]

end NLAlib
