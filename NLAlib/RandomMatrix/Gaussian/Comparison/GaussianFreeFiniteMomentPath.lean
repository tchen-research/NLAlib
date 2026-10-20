import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteArcCrossingBounds
import NLAlib.Matrix.Functions.ResolventMomentDerivatives
import NLAlib.Probability.Transforms.ResolventMoments

/-! # Endpoint continuity and positivity for actual finite Gaussian moments

All laws, expectations and regularity are those of the actual objects.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ
local notation "J" => (((d × n) × (d × n)) ⊕ ((d × n) × (d × n))) → ℝ
local notation "H" => (hermitianMatrixFromRealCoordinates : J →L[ℝ] M)

omit [DecidableEq ι] [Fintype d] [DecidableEq d] in
open scoped Matrix.Norms.L2Operator in
/-- The actual square-root diagonal/GUE interpolation is continuous in time, including both endpoints. -/
theorem continuous_gaussianFreeFiniteInterpolation_time
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (x : E) :
    Continuous (fun q : ℝ => gaussianFreeFiniteInterpolation A₀ A q x) := by
  unfold gaussianFreeFiniteInterpolation
  apply continuous_const.add
  apply continuous_finsetSum
  intro k _
  have hc : Continuous (fun q : ℝ => gaussianFreeFiniteCoefficient A q k) := by
    cases k with
    | inl ia =>
      simpa +instances only [gaussianFreeFiniteCoefficient, Pi.smul_def'] using!
        Real.continuous_sqrt.smul (continuous_const : Continuous (fun _ : ℝ =>
          A ia.1 ⊗ₖ (Matrix.single ia.2 ia.2 1 : Matrix n n ℂ)))
    | inr ik =>
      simpa +instances only [gaussianFreeFiniteCoefficient, Pi.smul_def', Function.comp_def,
        Pi.sub_def, id_eq] using!
        (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).smul
          (continuous_const : Continuous (fun _ : ℝ => A ik.1 ⊗ₖ gueCoefficientMatrix ik.2))
  simpa only [Pi.smul_def'] using
    (continuous_const : Continuous (fun _ : ℝ => x k)).smul hc

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The genuine sample Gram moment is continuous in interpolation time at every nonreal spectral parameter. -/
theorem continuous_gaussianFreeFinite_resolventEvenMoment_time
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) (x : E) :
    Continuous (fun q : ℝ => resolventEvenMoment
      (gaussianFreeFiniteInterpolation A₀ A q x) ζ p) := by
  let Y : ℝ → M := fun q => gaussianFreeFiniteInterpolation A₀ A q x
  have hY : Continuous Y := continuous_gaussianFreeFiniteInterpolation_time A₀ A x
  have hc := (contDiff_resolventEvenMoment_coordinate (0 : M)
    Matrix.isHermitian_zero ζ hζ p (r := ⊤)).continuous.comp
    (matrixRealCoordinatesContinuousLinearEquiv.continuous.comp hY)
  have he (q : ℝ) : (0 : M) + H (matrixRealCoordinates (Y q)) = Y q := by
    rw [zero_add]
    exact hermitianMatrixFromRealCoordinates_matrixRealCoordinates
      (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x)
  change Continuous (fun q : ℝ => resolventEvenMoment
    ((0 : M) + H (matrixRealCoordinates (Y q))) ζ p) at hc
  simpa only [he, Y] using hc

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual expected Gram moment is continuous through both endpoints by its native uniform resolvent domination.
Source: arXiv:2108.06312v2, Theorem 6.2 endpoint interpolation.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem continuous_integral_gaussianFreeFinite_resolventEvenMoment
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    Continuous (fun q : ℝ => ∫ x : E, resolventEvenMoment
      (gaussianFreeFiniteInterpolation A₀ A q x) ζ p ∂gaussianVector K) := by
  apply continuous_of_dominated (bound := fun _ => (|ζ.im|⁻¹) ^ (2 * p))
  · intro q
    exact (integrable_gaussianFreeFinite_resolventEvenMoment A₀ hA₀ A hA q ζ hζ hp).aestronglyMeasurable
  · intro q
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (resolventEvenMoment_nonneg _ _ hp)]
    exact resolventEvenMoment_le_inv_abs_im_pow _
      (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x) hζ hp
  · exact integrable_const _
  · filter_upwards [] with x
    exact continuous_gaussianFreeFinite_resolventEvenMoment_time A₀ hA₀ A hA ζ hζ p x

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- In nonempty matrix dimension the genuine expected positive-order Gram moment is strictly positive at every interpolation time. -/
theorem integral_gaussianFreeFinite_resolventEvenMoment_pos [Nonempty d] [Nonempty n]
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    0 < ∫ x : E, resolventEvenMoment
      (gaussianFreeFiniteInterpolation A₀ A q x) ζ p ∂gaussianVector K := by
  apply integral_resolventEvenMoment_pos (gaussianVector K)
    (gaussianFreeFiniteInterpolation A₀ A q)
  · have hm := ((gaussianFreeFiniteSeriesCLM (n := n) A q).continuous.const_add
        (A₀ ⊗ₖ (1 : Matrix n n ℂ)))
    have hm' : Continuous (gaussianFreeFiniteInterpolation (n := n) A₀ A q) := by
      change Continuous (fun x : E => A₀ ⊗ₖ (1 : Matrix n n ℂ) +
        ∑ k, x k • gaussianFreeFiniteCoefficient A q k)
      simpa +instances only [gaussianFreeFiniteSeriesCLM_apply, Pi.add_def] using! hm
    exact hm'.measurable.aemeasurable
  · exact Filter.Eventually.of_forall fun x =>
      gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x
  · exact hζ
  · exact hp

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The true expected Gram moment is the real part of its actual integrable mixed-resolvent trace. -/
theorem integral_gaussianFreeFinite_resolventEvenMoment_eq_re
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) :
    (∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ p
      ∂gaussianVector K) =
    (∫ x : E, normalizedTrace (gaussianFreeFiniteMixedArc A₀ A q ζ p p x)
      ∂gaussianVector K).re := by
  obtain ⟨C₀, C₁, _, _, hb, _⟩ :=
    exists_uniform_bounds_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ p p
  have hi : Integrable (gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ p p) (gaussianVector K) :=
    Integrable.of_bound
      (contDiff_gaussianFreeFiniteMixedArc A₀ hA₀ A hA q ζ hζ p p (r := ⊤)).continuous.aestronglyMeasurable
      C₀ (Filter.Eventually.of_forall hb)
  let T : M →L[ℂ] ℂ := (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap
  have ht : Integrable (fun x : E => normalizedTrace (gaussianFreeFiniteMixedArc A₀ A q ζ p p x))
      (gaussianVector K) := T.integrable_comp hi
  calc
    _ = ∫ x : E, (normalizedTrace (gaussianFreeFiniteMixedArc A₀ A q ζ p p x)).re
        ∂gaussianVector K := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => resolventEvenMoment_eq_re_normalizedTrace_mul_pow
        (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x) ζ p
    _ = _ := Complex.reCLM.integral_comp_comm ht

end NLAlib
