import NLAlib.Polynomial.OrthogonalPolynomials.ComplexMeasureMoments
import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationPositive
import NLAlib.Polynomial.OrthogonalPolynomials.RationalModificationRootConstraints

/-!
# Actual complex Cauchy moments in rational modification

Compact support and pole-free denominators supply complex Bochner integrability.
Removing a simple denominator factor then gives precisely the source Cauchy
integral, even when the pole is nonreal. The original and positive modified
measure functionals are linked to the finite algebraic determinant construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set Finset
namespace NLAlib

/-- The complex divided-polynomial moments needed for a fixed denominator. -/
def HasComplexDividedPolynomialMoments (μ : Measure ℝ) (v : ℂ[X]) : Prop :=
  ∀ p : ℂ[X], Integrable (fun x : ℝ => p.eval (x : ℂ)/v.eval (x : ℂ)) μ

/-- Finite compact support and a pole-free denominator imply every required
complex divided moment. -/
theorem hasComplexDividedPolynomialMoments_of_ae_mem_Icc
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {v : ℂ[X]}
    (hv : ∀ x ∈ Icc a b, v.eval (x : ℂ) ≠ 0) : HasComplexDividedPolynomialMoments μ v := by
  intro p
  have hc : ContinuousOn (fun x : ℝ => p.eval (x : ℂ)/v.eval (x : ℂ)) (Icc a b) :=
    (p.continuous.comp Complex.continuous_ofReal).continuousOn.div
      (v.continuous.comp Complex.continuous_ofReal).continuousOn hv
  refine (hc.integrableOn_compact isCompact_Icc).integrable_of_ae_notMem_eq_zero ?_
  filter_upwards [hs] with x hx hn
  exact (hn hx).elim

/-- Integration against a complex rational weight, as a scalar-linear
functional on complex polynomials. -/
def complexDividedPolynomialIntegral (μ : Measure ℝ) (v : ℂ[X])
    (hdiv : HasComplexDividedPolynomialMoments μ v) : ℂ[X] →ₗ[ℂ] ℂ where
  toFun p := ∫ x : ℝ, p.eval (x : ℂ)/v.eval (x : ℂ) ∂μ
  map_add' p q := by
    simp only [eval_add, add_div]
    exact integral_add (hdiv p) (hdiv q)
  map_smul' c p := by
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply, mul_div_assoc]
    exact integral_const_mul c _

/-- Evaluation of the divided functional is its actual Bochner integral. -/
@[simp] theorem complexDividedPolynomialIntegral_apply (μ : Measure ℝ) (v : ℂ[X])
    (hdiv : HasComplexDividedPolynomialMoments μ v) (p : ℂ[X]) :
    complexDividedPolynomialIntegral μ v hdiv p =
      ∫ x : ℝ, p.eval (x : ℂ)/v.eval (x : ℂ) ∂μ := rfl

/-- Clearing the actual denominator recovers the original measure functional. -/
theorem complexDividedPolynomialIntegral_denominator_mul
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) (v : ℂ[X])
    (hdiv : HasComplexDividedPolynomialMoments μ v)
    (hv : ∀ᵐ (x : ℝ) ∂μ, v.eval (x : ℂ) ≠ 0) (p : ℂ[X]) :
    complexDividedPolynomialIntegral μ v hdiv (v*p) = complexPolynomialIntegral μ hμ p := by
  rw [complexDividedPolynomialIntegral_apply, complexPolynomialIntegral_apply]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [eval_mul, mul_div_cancel_left₀ _ hx]

/-- The polynomial cofactor row is the source's actual Cauchy integral; it has
no spurious real-root restriction. The denominator convention is `t-z_i`.
atlas: christoffel-uvarov-modification (partial) -/
theorem complexDividedPolynomialIntegral_rootCofactor_eq_cauchy
    {μ : Measure ℝ} {m : ℕ} (z : Fin m → ℂ)
    (hdiv : HasComplexDividedPolynomialMoments μ (Lagrange.nodal Finset.univ z))
    (hz : ∀ᵐ (t : ℝ) ∂μ, ∀ i, (t : ℂ) ≠ z i) (p : ℂ[X]) (i : Fin m) :
    complexDividedPolynomialIntegral μ (Lagrange.nodal Finset.univ z) hdiv (p*rootCofactor z i) =
      ∫ t : ℝ, p.eval (t : ℂ)/((t : ℂ)-z i) ∂μ := by
  rw [complexDividedPolynomialIntegral_apply]
  apply integral_congr_ae
  filter_upwards [hz] with t ht
  have hc : (rootCofactor z i).eval (t : ℂ) ≠ 0 := by
    simp only [rootCofactor, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (ht j))
  have he : (Lagrange.nodal Finset.univ z).eval (t : ℂ) =
      ((t : ℂ)-z i) * (rootCofactor z i).eval (t : ℂ) := by
    rw [Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i), eval_mul, eval_sub, eval_X, eval_C]
    rfl
  rw [eval_mul, he]
  field_simp [hc, sub_ne_zero.mpr (ht i)]

/-- The positive modified real measure gives exactly the weighted complex
divided functional used by the root determinant, rather than an assumed moment
adapter. Nonreal roots of the real denominator are allowed.
atlas: christoffel-uvarov-modification (partial) -/
theorem complexPolynomialIntegral_rationalPolynomialModifiedMeasure_eq
    {μ : Measure ℝ} (u v : ℝ[X]) (hr : HasDividedPolynomialMoments μ v)
    (hc : HasComplexDividedPolynomialMoments μ (v.map Complex.ofRealHom))
    (hpos : ∀ᵐ t ∂μ, 0 ≤ u.eval t/v.eval t) :
    complexPolynomialIntegral (rationalPolynomialModifiedMeasure μ u v)
        (hasPolynomialMoments_rationalPolynomialModifiedMeasure μ u v hr hpos) =
      polynomialWeightedFunctional (complexDividedPolynomialIntegral μ (v.map Complex.ofRealHom) hc)
        (u.map Complex.ofRealHom) := by
  apply LinearMap.ext
  intro p
  rw [complexPolynomialIntegral_apply, polynomialWeightedFunctional_apply,
    complexDividedPolynomialIntegral_apply, rationalPolynomialModifiedMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (by filter_upwards with t; exact ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hpos] with t ht
  rw [ENNReal.toReal_ofReal ht, eval_mul]
  change (u.eval t/v.eval t) • p.eval (t : ℂ) =
    ((u.map Complex.ofRealHom).eval (Complex.ofRealHom t) * p.eval (t : ℂ)) /
      (v.map Complex.ofRealHom).eval (Complex.ofRealHom t)
  rw [eval_map_apply, eval_map_apply]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofRealHom_eq_coe]
  ring

end NLAlib
