import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Integration

/-!
# Uniform finite hash collisions

Two distinct coordinates of the actual product uniform law collide with
probability the reciprocal of the alphabet cardinality. This is the hash
average in the CountSketch Gram-error calculation.
Source: operator manuscript `sh:count-second`; supports `sparse-ose`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [Nonempty ρ]
variable [MeasurableSpace ρ] [MeasurableSingletonClass ρ] [DecidableEq ρ]

/-- A fixed alphabet symbol has reciprocal-cardinality mass under the actual
uniform finite law. Source: the native uniform PMF; supports the CountSketch
hash average in `sparse-ose`. -/
theorem integral_ite_eq_uniformOfFintype (r : ρ) :
    (∫ a : ρ, (if a = r then (1 : ℝ) else 0) ∂(PMF.uniformOfFintype ρ).toMeasure) =
      (Fintype.card ρ : ℝ)⁻¹ := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Distinct coordinates in the actual product uniform law collide with
probability exactly the reciprocal alphabet cardinality. Source: independent
uniform hashes in manuscript `sh:count-second`; supports `sparse-ose`. -/
theorem integral_ite_coordinate_eq_coordinate_pi_uniformOfFintype
    (i j : ι) (hij : i ≠ j) :
    (∫ h : ι → ρ, (if h i = h j then (1 : ℝ) else 0)
        ∂Measure.pi (fun _ => (PMF.uniformOfFintype ρ).toMeasure)) =
      (Fintype.card ρ : ℝ)⁻¹ := by
  let μ := Measure.pi fun _ : ι => (PMF.uniformOfFintype ρ).toMeasure
  let δ (r : ρ) (a : ρ) : ℝ := if a = r then 1 else 0
  have hδ (r : ρ) : Measurable (δ r) := Measurable.of_discrete
  have hcoord (r : ρ) (k : ι) :
      (∫ h : ι → ρ, δ r (h k) ∂μ) = (Fintype.card ρ : ℝ)⁻¹ := by
    rw [integral_comp_eval (hδ r).aestronglyMeasurable]
    exact integral_ite_eq_uniformOfFintype r
  have hind : iIndepFun (fun k (h : ι → ρ) => h k) μ :=
    iIndepFun_pi (fun _ : ι => aemeasurable_id)
  have hpair (r : ρ) :
      (∫ h : ι → ρ, δ r (h i) * δ r (h j) ∂μ) = (Fintype.card ρ : ℝ)⁻¹ ^ 2 := by
    have hh := ((hind.indepFun hij).comp (hδ r) (hδ r)).integral_fun_mul_eq_mul_integral
      (Measurable.of_discrete.aestronglyMeasurable) (Measurable.of_discrete.aestronglyMeasurable)
    simpa only [Function.comp_apply, hcoord, pow_two] using hh
  have hpoint (h : ι → ρ) : (if h i = h j then (1 : ℝ) else 0) =
      ∑ r, δ r (h i) * δ r (h j) := by
    simp only [δ, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    simp only [eq_comm]
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun _ _ => Integrable.of_finite]
  change (∑ r : ρ, ∫ h : ι → ρ, δ r (h i) * δ r (h j) ∂μ) = _
  simp_rw [hpair]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card ρ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end NLAlib
