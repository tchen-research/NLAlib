import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteResolventWords
import NLAlib.RandomMatrix.Gaussian.Basic.GUECoefficientParameters
import NLAlib.Matrix.Functions.PartialTraceResolventFrame
import NLAlib.Probability.Gaussian.Calculus.Poincare

/-! # Native GUE normalized partial-trace gradient decay

The derivatives are the genuine Fréchet derivatives of the existing affine
Gaussian matrix model. The true entry covariance and normalized trace frame
give the exact inverse-square ensemble-dimension gradient budget.
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
local notation "M" => Matrix (d×n) (d×n) ℂ

/-- Actual normalized partial-trace entries of the finite-N source
resolvent, as functions on its canonical standard Gaussian coordinates. -/
def gaussianFreeFinitePartialTraceResolventEntry
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ)
    (q : ℝ) (ζ : ℂ) (a b : d) (x : E) : ℂ :=
  normalizedPartialTrace (resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ) a b

open scoped Matrix.Norms.L2Operator in
private def partialTraceEntryCLM (a b : d) : M →L[ℂ] ℂ :=
  (Fintype.card n : ℂ)⁻¹ •
    (Matrix.traceLinearMap (d×n) ℂ ℂ).toContinuousLinearMap.comp
      (ContinuousLinearMap.mul ℂ M
        ((Matrix.single b a 1 : Matrix d d ℂ)⊗ₖ(1 : Matrix n n ℂ)))

open scoped Matrix.Norms.L2Operator in
private theorem partialTraceEntryCLM_apply (a b : d) (T : M) :
    partialTraceEntryCLM a b T=normalizedPartialTrace T a b := by
  simpa only [partialTraceEntryCLM,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',
    LinearMap.coe_toContinuousLinearMap',Matrix.traceLinearMap_apply,smul_eq_mul] using
    (normalizedPartialTrace_apply_eq_trace T a b).symm

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The genuine partial-trace resolvent derivative is the actual native
single-insertion resolvent sandwich. Every coordinate direction uses the
true finite-N coefficient matrices of the existing Gaussian realization. -/
theorem fderiv_gaussianFreeFinitePartialTraceResolventEntry_apply
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im≠0) (a b : d) (x h : E) :
    fderiv ℝ (gaussianFreeFinitePartialTraceResolventEntry A₀ A q ζ a b) x h =
      normalizedPartialTrace (resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ*
        (∑ k, h k • gaussianFreeFiniteCoefficient A q k)*
        resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ) a b := by
  let L := gaussianFreeFiniteSeriesCLM (n := n) A q
  let T := gaussianFreeFiniteInterpolation A₀ A q x
  let P : M →L[ℝ] ℂ := (partialTraceEntryCLM (n := n) a b).restrictScalars ℝ
  have hT : T.IsHermitian := gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x
  have heq : gaussianFreeFiniteInterpolation A₀ A q =
      fun y : E => A₀⊗ₖ(1 : Matrix n n ℂ)+L y := by
    funext y
    simp [gaussianFreeFiniteInterpolation,L]
  have hL : HasFDerivAt (gaussianFreeFiniteInterpolation A₀ A q) L x := by
    rw [heq]
    exact L.hasFDerivAt.const_add _
  have hR := (hasFDerivAt_resolvent_of_isHermitian ζ T hT hζ).restrictScalars ℝ
  have hcomp := P.hasFDerivAt.comp x (hR.comp x hL)
  have hfun : (fun y : E => P (resolvent (gaussianFreeFiniteInterpolation A₀ A q y) ζ)) =
      gaussianFreeFinitePartialTraceResolventEntry A₀ A q ζ a b := by
    funext y
    exact partialTraceEntryCLM_apply a b _
  change HasFDerivAt (fun y : E => P (resolvent (gaussianFreeFiniteInterpolation A₀ A q y) ζ)) _ x at hcomp
  rw [hfun] at hcomp
  rw [hcomp.fderiv]
  simp only [P,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',
    rationalBlockMap_apply,rationalBlockDifference_resolvent,
    partialTraceEntryCLM_apply,L,gaussianFreeFiniteSeriesCLM_apply,T]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem specNorm_covariance_gaussianFreeFiniteCoefficient_zero
    (A : ι → Matrix d d ℂ) :
    specNorm (coefficientCovariance (gaussianFreeFiniteCoefficient (n := n) A 0)) =
      specNorm (coefficientCovariance A)/(Fintype.card n : ℝ) := by
  have he : coefficientCovariance (gaussianFreeFiniteCoefficient (n := n) A 0) =
      coefficientCovariance (fun ik : ι×GUECoordinate Unit n => A ik.1⊗ₖgueCoefficientMatrix ik.2) := by
    ext ab ce
    simp [coefficientCovariance,coefficientVectorization,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fintype.sum_sum_type,gaussianFreeFiniteCoefficient]
  rw [he,specNorm_coefficientCovariance_kronecker_gueCoefficientMatrix]

open scoped Matrix.Norms.L2Operator in
/-- The true squared-coordinate-gradient budget for the GUE endpoint of the
actual normalized partial-trace resolvent is exactly v²/(N² |Im z|⁴).
The full original unnormalized entry covariance is retained. This is the
genuine dimension decay needed for the finite-N Dyson covariance error.
Source: Gaussian covariance identity and the native GUE coefficient frame.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem sum_norm_fderiv_gaussianFreeFinitePartialTraceResolventEntry_sq_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im≠0) (a b : d) (x : E) :
    (∑ k : K, ‖fderiv ℝ (gaussianFreeFinitePartialTraceResolventEntry A₀ A 0 ζ a b) x
      (Pi.single k 1)‖^2) ≤
      specNorm (coefficientCovariance A)/(Fintype.card n : ℝ)^2*|ζ.im|⁻¹^4 := by
  have hpoint : ∀ k : K,
      fderiv ℝ (gaussianFreeFinitePartialTraceResolventEntry A₀ A 0 ζ a b) x
        (Pi.single k 1) =
      normalizedPartialTrace (resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ*
        gaussianFreeFiniteCoefficient A 0 k*
        resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ) a b := by
    intro k
    rw [fderiv_gaussianFreeFinitePartialTraceResolventEntry_apply A₀ hA₀ A hA 0 ζ hζ]
    simp
  simp_rw [hpoint]
  have hh := sum_norm_normalizedPartialTrace_resolvent_sandwich_sq_le
    (gaussianFreeFiniteCoefficient A 0)
    (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x) hζ a b
  rw [specNorm_covariance_gaussianFreeFiniteCoefficient_zero] at hh
  simpa only [div_div,← sq] using hh


open scoped Matrix.Norms.L2Operator in
/-- The actual GUE normalized partial-trace resolvent entry has centered
second moment at most v²/(N² |Im z|⁴) under the genuine coordinate law.
The Gaussian Poincare hypotheses are all derived from this native resolvent
function, including its actual continuous bounded derivative.
Source: arXiv:2108.06312v2, Gaussian covariance identity and Section 6.1.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem integral_norm_partialTraceResolventEntry_sub_integral_sq_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im≠0) (a b : d) :
    (∫ x : E, ‖gaussianFreeFinitePartialTraceResolventEntry A₀ A 0 ζ a b x-
      ∫ y : E, gaussianFreeFinitePartialTraceResolventEntry A₀ A 0 ζ a b y
        ∂gaussianVector K‖^2 ∂gaussianVector K) ≤
      specNorm (coefficientCovariance A)/(Fintype.card n : ℝ)^2*|ζ.im|⁻¹^4 := by
  let f := gaussianFreeFinitePartialTraceResolventEntry (n := n) A₀ A 0 ζ a b
  let L := gaussianFreeFiniteSeriesCLM (n := n) A 0
  let P : M →L[ℝ] ℂ := (partialTraceEntryCLM (n := n) a b).restrictScalars ℝ
  let R : E → M := fun x => resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ
  have hReq : R=gaussianFreeFiniteResolventWord A₀ A 0 (fun _ : Fin 1 => ζ) := by
    funext x
    simp [R,gaussianFreeFiniteResolventWord]
  have hRc : ContDiff ℝ ⊤ R := by
    rw [hReq]
    exact contDiff_gaussianFreeFiniteResolventWord A₀ hA₀ A hA 0 _ (fun _ => hζ)
  have hR (x : E) : ‖R x‖≤|ζ.im|⁻¹ :=
    (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x).specNorm_resolvent_le hζ
  have heq : f=P ∘ R := by
    funext x
    exact (partialTraceEntryCLM_apply a b _).symm
  have hfc : ContDiff ℝ ⊤ f := by rw [heq]; exact P.contDiff.comp hRc
  have hdfc : Continuous (fderiv ℝ f) := (hfc.fderiv_right (m := ⊤) (by simp)).continuous
  have hfb (x : E) : ‖f x‖≤‖P‖*|ζ.im|⁻¹ := by
    rw [heq,Function.comp_apply]
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hR x) (norm_nonneg _))
  have hdfb (x : E) : ‖fderiv ℝ f x‖≤‖P‖*|ζ.im|⁻¹^2*‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro h
    rw [fderiv_gaussianFreeFinitePartialTraceResolventEntry_apply A₀ hA₀ A hA 0 ζ hζ]
    rw [← gaussianFreeFiniteSeriesCLM_apply A 0 h,← partialTraceEntryCLM_apply a b]
    change ‖P (R x*(L h)*R x)‖≤_
    calc
      _ ≤ ‖P‖*‖R x*(L h)*R x‖ := P.le_opNorm _
      _ ≤ ‖P‖*((‖R x‖*‖L h‖)*‖R x‖) :=
        mul_le_mul_of_nonneg_left
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _)
      _ ≤ ‖P‖*((|ζ.im|⁻¹*(‖L‖*‖h‖))*|ζ.im|⁻¹) := by
        gcongr
        · exact hR x
        · exact L.le_opNorm h
        · exact hR x
      _ = _ := by ring
  exact integral_norm_sub_integral_sq_le_gaussian_gradient_bound f (fderiv ℝ f)
    (fun x => (hfc.differentiable (by simp) x).hasFDerivAt) hdfc
    (‖P‖*|ζ.im|⁻¹) (‖P‖*|ζ.im|⁻¹^2*‖L‖)
    (specNorm (coefficientCovariance A)/(Fintype.card n : ℝ)^2*|ζ.im|⁻¹^4)
    hfb hdfb (sum_norm_fderiv_gaussianFreeFinitePartialTraceResolventEntry_sq_le
      A₀ hA₀ A hA ζ hζ a b)

end NLAlib
