import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteArcCrossing
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteParameters
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteArcMarginals
import NLAlib.Matrix.Functions.ResolventModulusMoments
import NLAlib.ForMathlib.MeasureTheory.MomentInterpolation

/-! # Uniform native four-arc crossing bounds

All coefficient budgets are those of the actual finite-dimensional
interpolation. The Schatten crossing estimate is applied to the actual
resolvents before integration under their genuine Gaussian marginals.
Source: arXiv:2108.06312v2, Lemma 6.3.
Atlas: gaussian-free-spectrum-two-sided (partial).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Kronecker ComplexOrder MatrixOrder
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ

open scoped Matrix.Norms.L2Operator in
/-- The true four-arc crossing of an outer family within the original
variance/covariance budgets and the actual finite-N coefficients has the
original product budget, uniformly throughout the interpolation. -/
theorem norm_nativeMixedArc_crossing_le_original_parameters
    {κ : Type*} [Fintype κ] [DecidableEq κ] (C : κ → M)
    (hC : ∀ k, (C k).IsHermitian)
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hVC : specNorm (coefficientVariance C) ≤ specNorm (coefficientVariance A))
    (hWC : specNorm (coefficientCovariance C) ≤ specNorm (coefficientCovariance A))
    (ζ : ℂ) (a b : Fin 4 → ℕ) {L : ℕ}
    (hL : ∑ j, (a j + b j) = L) (hLpos : 0 < L)
    (hArc : ∀ j, 0 < a j + b j) (x : Fin 4 → E) :
    ‖(Fintype.card (d × n) : ℂ)⁻¹ *
      coefficientCrossingTraceMultilinear C (gaussianFreeFiniteCoefficient A q)
        (fun j => gaussianFreeFiniteMixedArc A₀ A q ζ (a j) (b j) (x j))‖ ≤
      (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) *
        ∑ j, (((a j + b j : ℕ) : ℝ) / L) *
          (normalizedTrace (CFC.abs (resolvent
            (gaussianFreeFiniteInterpolation A₀ A q (x j)) ζ) ^ L)).re := by
  have h := norm_inv_card_mul_coefficientCrossingTrace_resolvent_le_sum_normalizedTrace
    C (gaussianFreeFiniteCoefficient (n := n) A q) hC
    (gaussianFreeFiniteCoefficient_isHermitian A hA q)
    (fun j => gaussianFreeFiniteInterpolation A₀ A q (x j))
    (fun j => gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q (x j))
    ζ a b hL hLpos hArc
  have hV := specNorm_coefficientVariance_gaussianFreeFiniteCoefficient_le (n := n) A hq hq1
  have hW := specNorm_coefficientCovariance_gaussianFreeFiniteCoefficient_le (n := n) A hq hq1
  have hpref : Real.sqrt (specNorm (coefficientVariance C)) *
      Real.sqrt (specNorm (coefficientCovariance C)) *
      Real.sqrt (specNorm (coefficientCovariance (gaussianFreeFiniteCoefficient (n := n) A q))) *
      Real.sqrt (specNorm (coefficientVariance (gaussianFreeFiniteCoefficient (n := n) A q))) ≤
        specNorm (coefficientVariance A) * specNorm (coefficientCovariance A) := by
    calc
      _ ≤ Real.sqrt (specNorm (coefficientVariance A)) *
          Real.sqrt (specNorm (coefficientCovariance A)) *
          Real.sqrt (specNorm (coefficientCovariance A)) *
          Real.sqrt (specNorm (coefficientVariance A)) := by
            gcongr
      _ = _ := by
        nlinarith [Real.sq_sqrt (specNorm_nonneg (coefficientVariance A)),
          Real.sq_sqrt (specNorm_nonneg (coefficientCovariance A))]
  have hsum : 0 ≤ ∑ j : Fin 4, (((a j + b j : ℕ) : ℝ) / L) *
      (normalizedTrace (CFC.abs (resolvent
        (gaussianFreeFiniteInterpolation A₀ A q (x j)) ζ) ^ L)).re := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (by positivity)
    rw [← RCLike.re_eq_complex_re, re_normalizedTrace_cfcAbs_pow_eq_sum_div_card]
    exact div_nonneg (Finset.sum_nonneg fun r _ => pow_nonneg (singularValues_nonneg _ r) _)
      (Nat.cast_nonneg _)
  exact h.trans (mul_le_mul_of_nonneg_right hpref hsum)

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The literal positive native Gram moment is continuous in its actual
Gaussian coordinates; this does not require a supplied measurable law. -/
theorem continuous_gaussianFreeFinite_resolventEvenMoment
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) :
    Continuous (fun x : E => resolventEvenMoment
      (gaussianFreeFiniteInterpolation A₀ A q x) ζ p) := by
  let T : M →L[ℂ] ℂ := (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap
  have h := Complex.reCLM.continuous.comp (T.continuous.comp
    (contDiff_gaussianFreeFiniteMixedArc (n := n) A₀ hA₀ A hA q ζ hζ p p (r := ⊤)).continuous)
  have heq : (fun x : E => resolventEvenMoment
      (gaussianFreeFiniteInterpolation A₀ A q x) ζ p) =
      fun x : E => (normalizedTrace (gaussianFreeFiniteMixedArc A₀ A q ζ p p x)).re := by
    funext x
    exact resolventEvenMoment_eq_re_normalizedTrace_mul_pow
      (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x) ζ p
  rw [heq]
  simpa +instances only [T, Function.comp_def, LinearMap.coe_toContinuousLinearMap',
    normalizedTraceLinearMap_apply] using! h

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual native positive Gram moment is Gaussian integrable, with
uniform nonreal-height domination derived from Hermitian resolvents. -/
theorem integrable_gaussianFreeFinite_resolventEvenMoment
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    Integrable (fun x : E => resolventEvenMoment
      (gaussianFreeFiniteInterpolation A₀ A q x) ζ p) (gaussianVector K) := by
  apply Integrable.of_bound
    (continuous_gaussianFreeFinite_resolventEvenMoment A₀ hA₀ A hA q ζ hζ p).aestronglyMeasurable
    ((|ζ.im|⁻¹) ^ (2 * p))
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (resolventEvenMoment_nonneg _ _ hp)]
  exact resolventEvenMoment_le_inv_abs_im_pow _
    (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x) hζ hp

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual mean of the higher native modulus trace has precisely five
unused inverse-height powers times the fractional original Gram moment.
The scalar fractional-moment step is proved under the actual Gaussian law.
Source: arXiv:2108.06312v2, Lemma 6.3. -/
theorem integral_gaussianFreeFinite_resolventEvenMoment_add_two_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    (∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ (p + 2)
        ∂gaussianVector K) ≤
      (|ζ.im|⁻¹) ^ 5 *
        (∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ p
          ∂gaussianVector K) ^ (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  let μ := gaussianVector K
  let f : E → ℝ := fun x => resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ p
  let α : ℝ := ((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)
  have hα : 0 < α := by
    apply div_pos
    · exact_mod_cast (show 0 < 2 * p - 1 by omega)
    · positivity
  have hα1 : α ≤ 1 := by
    dsimp [α]
    rw [div_le_one (by positivity : (0 : ℝ) < (2 * p : ℕ))]
    exact_mod_cast (show 2 * p - 1 ≤ 2 * p by omega)
  have hfnn (x : E) : 0 ≤ f x := resolventEvenMoment_nonneg _ _ hp
  have hfi : Integrable f μ := integrable_gaussianFreeFinite_resolventEvenMoment A₀ hA₀ A hA q ζ hζ hp
  have hmean : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hfnn
  have hfrac : (∫ x, f x ^ α ∂μ) ≤ (∫ x, f x ∂μ) ^ α := by
    apply integral_rpow_le_of_integral_rpow_le hfi.aestronglyMeasurable hfnn hα hα1 hmean
    · simpa only [Real.rpow_one] using hfi
    · simp only [Real.rpow_one, le_refl]
  have hfraci : Integrable (fun x => f x ^ α) μ :=
    integrable_rpow_of_nonneg_of_le hfi.aestronglyMeasurable hfnn hα.le (by norm_num) hα1
      (by simpa only [Real.rpow_one] using hfi)
  calc
    _ ≤ ∫ x, (|ζ.im|⁻¹) ^ 5 * f x ^ α ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun x => resolventEvenMoment_nonneg _ _ (by omega))
        (hfraci.const_mul _)
      filter_upwards [] with x
      have hHerm := gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x
      have h := hHerm.re_normalizedTrace_cfcAbs_resolvent_pow_le hζ hp
        (L := 2 * (p + 2)) (by omega)
      have hmom : (normalizedTrace (CFC.abs (resolvent
          (gaussianFreeFiniteInterpolation A₀ A q x) ζ) ^ (2 * (p + 2)))).re =
          resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ (p + 2) := by
        simpa only [RCLike.re_eq_complex_re, resolventEvenMoment] using
          re_normalizedTrace_cfcAbs_pow_two_mul
            (resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ) (p + 2)
      rw [hmom] at h
      simpa only [f, α, show 2 * (p + 2) - (2 * p - 1) = 5 by omega] using h
    _ = (|ζ.im|⁻¹) ^ 5 * ∫ x, f x ^ α ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hfrac (by positivity)

open scoped Matrix.Norms.L2Operator in
/-- Integrating a genuine four-arc crossing under four actual standard
Gaussian marginal maps retains the original normalized modulus moment.
The maps may be dependent, and only their actual marginal laws are used.
Source: arXiv:2108.06312v2, Lemma 6.3.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem norm_integral_nativeMixedArc_crossing_le_original_moment
    {κ : Type*} [Fintype κ] [DecidableEq κ] (C : κ → M)
    (hC : ∀ k, (C k).IsHermitian)
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hVC : specNorm (coefficientVariance C) ≤ specNorm (coefficientVariance A))
    (hWC : specNorm (coefficientCovariance C) ≤ specNorm (coefficientCovariance A))
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b : Fin 4 → ℕ) {m : ℕ} (hm : 0 < m)
    (hL : ∑ j, (a j + b j) = 2 * m) (hArc : ∀ j, 0 < a j + b j)
    (Y : Fin 4 → E × E → E)
    (hY : ∀ j, MeasurePreserving (Y j)
      ((gaussianVector K).prod (gaussianVector K)) (gaussianVector K)) :
    ‖∫ w : E × E, (Fintype.card (d × n) : ℂ)⁻¹ *
      coefficientCrossingTraceMultilinear C (gaussianFreeFiniteCoefficient A q)
        (fun j => gaussianFreeFiniteMixedArc A₀ A q ζ (a j) (b j) (Y j w))
      ∂(gaussianVector K).prod (gaussianVector K)‖ ≤
      (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) *
        ∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ m
          ∂gaussianVector K := by
  let μ := gaussianVector K
  let f : E → ℝ := fun x => resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A q x) ζ m
  let v : ℝ := specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)
  let wgt : Fin 4 → ℝ := fun j => ((a j + b j : ℕ) : ℝ) / (2 * m : ℕ)
  have hfi : Integrable f μ := integrable_gaussianFreeFinite_resolventEvenMoment A₀ hA₀ A hA q ζ hζ hm
  have hi (j : Fin 4) : Integrable (fun w : E × E => f (Y j w)) (μ.prod μ) :=
    (hY j).integrable_comp_of_integrable hfi
  have he (j : Fin 4) : (∫ w : E × E, f (Y j w) ∂μ.prod μ) = ∫ x, f x ∂μ :=
    (hY j).hasLaw.integral_comp hfi.aestronglyMeasurable
  have hwgt : ∑ j, wgt j = 1 := by
    dsimp only [wgt]
    rw [← Finset.sum_div, show (∑ j, ((a j + b j : ℕ) : ℝ)) = (2 * m : ℕ) by exact_mod_cast hL,
      div_self (by positivity : ((2 * m : ℕ) : ℝ) ≠ 0)]
  have hbound (w : E × E) :
      ‖(Fintype.card (d × n) : ℂ)⁻¹ * coefficientCrossingTraceMultilinear C
        (gaussianFreeFiniteCoefficient A q)
        (fun j => gaussianFreeFiniteMixedArc A₀ A q ζ (a j) (b j) (Y j w))‖ ≤
        v * ∑ j, wgt j * f (Y j w) := by
    have h := norm_nativeMixedArc_crossing_le_original_parameters C hC A₀ hA₀ A hA hq hq1
      hVC hWC ζ a b hL (by omega) hArc (fun j => Y j w)
    have hmom (j : Fin 4) : (normalizedTrace (CFC.abs (resolvent
        (gaussianFreeFiniteInterpolation A₀ A q (Y j w)) ζ) ^ (2 * m))).re = f (Y j w) := by
      simpa only [RCLike.re_eq_complex_re, resolventEvenMoment, f] using
        re_normalizedTrace_cfcAbs_pow_two_mul
          (resolvent (gaussianFreeFiniteInterpolation A₀ A q (Y j w)) ζ) m
    simpa only [hmom, v, wgt] using h
  calc
    _ ≤ ∫ w : E × E, v * ∑ j, wgt j * f (Y j w) ∂μ.prod μ :=
      norm_integral_le_of_norm_le
        ((integrable_finsetSum _ fun j _ => (hi j).const_mul (wgt j)).const_mul v)
        (Eventually.of_forall hbound)
    _ = v * (∑ j, wgt j) * ∫ x, f x ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ fun j _ => (hi j).const_mul (wgt j)]
      simp only [integral_const_mul, he, ← Finset.sum_mul, mul_assoc]
    _ = _ := by rw [hwgt, mul_one]

end NLAlib
