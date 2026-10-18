import NLAlib.Matrix.Spectral.NumericalRange
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Quadratic-form weak variance of a matrix law

The supremum is taken over single unit-vector quadratic forms, retaining the
weak variance used by Tropp's Gaussian proxy theorem. It is distinct from a
bilinear supremum over two independently chosen unit vectors.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- The actual quadratic-form weak variance of a complex matrix law: the
supremum of the variances of `Re (uᴴ Z u)` over Euclidean unit vectors `u`.
For square-integrable laws the supremum is finite. In empty dimension it is
zero; Mathlib's `sSup` also has value zero for an unbounded set of real values.
Source: Tropp (2026), equation (1.4). -/
def quadraticWeakVariance (μ : Measure M) : ℝ :=
  sSup ((fun u : n → ℂ => Var[fun Z : M => (quadForm Z u).re; μ]) ''
    {u | ‖WithLp.toLp 2 u‖ = 1})

omit [DecidableEq n] in
/-- The quadratic-form weak variance is nonnegative, including empty dimension. -/
theorem quadraticWeakVariance_nonneg (μ : Measure M) : 0 ≤ quadraticWeakVariance μ := by
  apply Real.sSup_nonneg
  rintro _ ⟨u, _, rfl⟩
  exact variance_nonneg _ _

open scoped Matrix.Norms.L2Operator in
/-- Every unit quadratic-form variance is bounded by the spectral-norm second
moment of the matrix law. Hermitian support and centeredness are unnecessary. -/
theorem variance_re_quadForm_le_integral_specNorm_sq
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : MemLp (id : M → M) 2 μ)
    {u : n → ℂ} (hu : ‖WithLp.toLp 2 u‖ = 1) :
    Var[fun Z => (quadForm Z u).re; μ] ≤ ∫ Z, specNorm Z ^ 2 ∂μ := by
  let q : M → ℝ := fun Z => (quadForm Z u).re
  have hq : Measurable q := by
    dsimp [q]
    simp only [quadForm, dotProduct, Matrix.mulVec]
    fun_prop
  have hi : Integrable (fun Z : M => specNorm Z ^ 2) μ := by
    simpa only [specNorm_eq_norm, id_eq] using hμ.norm.integrable_sq
  have hb (Z : M) : q Z ^ 2 ≤ specNorm Z ^ 2 := by
    have hnorm := norm_quadForm_le_specNorm Z u
    rw [hu, one_pow, mul_one] at hnorm
    have habs := (Complex.abs_re_le_norm (quadForm Z u)).trans hnorm
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (specNorm_nonneg _)).mpr habs
  have hqi : Integrable (fun Z => q Z ^ 2) μ := by
    apply hi.mono' (hq.pow_const 2).aestronglyMeasurable
    filter_upwards [] with Z
    simpa only [Real.norm_eq_abs, abs_sq] using hb Z
  exact (variance_le_expectation_sq hq.aestronglyMeasurable).trans (integral_mono hqi hi hb)

open scoped Matrix.Norms.L2Operator in
/-- The unit quadratic-form variances form a bounded set for every
square-integrable matrix law. -/
theorem bddAbove_range_variance_re_quadForm
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : MemLp (id : M → M) 2 μ) :
    BddAbove ((fun u : n → ℂ => Var[fun Z : M => (quadForm Z u).re; μ]) ''
      {u | ‖WithLp.toLp 2 u‖ = 1}) := by
  refine ⟨∫ Z, specNorm Z ^ 2 ∂μ, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact variance_re_quadForm_le_integral_specNorm_sq μ hμ hu

open scoped Matrix.Norms.L2Operator in
/-- The defined supremum bounds each actual unit quadratic-form variance. -/
theorem variance_re_quadForm_le_quadraticWeakVariance
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : MemLp (id : M → M) 2 μ)
    {u : n → ℂ} (hu : ‖WithLp.toLp 2 u‖ = 1) :
    Var[fun Z => (quadForm Z u).re; μ] ≤ quadraticWeakVariance μ :=
  le_csSup (bddAbove_range_variance_re_quadForm μ hμ) ⟨u, hu, rfl⟩

open scoped Matrix.Norms.L2Operator in
/-- The square root of the actual weak variance supplies the variance parameter
required by Gaussian maximum-eigenvalue concentration, including zero variance. -/
theorem variance_re_quadForm_le_sq_sqrt_quadraticWeakVariance_gaussian
    (μ : Measure M) [IsGaussian μ] {u : n → ℂ} (hu : ‖WithLp.toLp 2 u‖ = 1) :
    Var[fun Z => (quadForm Z u).re; μ] ≤ Real.sqrt (quadraticWeakVariance μ) ^ 2 := by
  rw [Real.sq_sqrt (quadraticWeakVariance_nonneg μ)]
  exact variance_re_quadForm_le_quadraticWeakVariance μ IsGaussian.memLp_two_id hu

end NLAlib
