import NLAlib.Matrix.Functions.ResolventDifferences
import NLAlib.Matrix.Basic.NormalizedTrace
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Derivatives of the Hermitian resolvent and its normalized trace

The actual complex Fréchet derivatives are rational block maps. On a
Hermitian base point the nonreal shift is invertible, so the formulas apply
on a genuine open matrix neighborhood. Restricting scalars then gives the
real derivatives used in Gaussian interpolation.
Source: the supplied Cauchy-transform reroute, (comparison-L).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial ContinuousLinearMap
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem isUnit_aeval_shift (ζ : ℂ) (A : M) (hA : A.IsHermitian)
    (hζ : ζ.im ≠ 0) : IsUnit (aeval A (C ζ-X)) := by
  simpa only [map_sub,aeval_C,aeval_X,Algebra.algebraMap_eq_smul_one] using
    hA.isUnit_smul_one_sub_of_im_ne_zero hζ

/-- The actual resolvent has the single-insertion Fréchet derivative on the
nonreal Hermitian domain. Source: the supplied Cauchy-transform reroute.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem hasFDerivAt_resolvent_of_isHermitian (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    HasFDerivAt (fun B : M => resolvent B ζ) (rationalBlockMap 1 (C ζ-X) A A) A := by
  have h := hasFDerivAt_rationalMatrixEval 1 (C ζ-X) A (isUnit_aeval_shift ζ A hA hζ)
  have he : (rationalMatrixEval 1 (C ζ-X) : M → M) = fun B => resolvent B ζ :=
    funext (rationalMatrixEval_resolvent ζ)
  rwa [he] at h

/-- The squared resolvent's actual Fréchet derivative is its diagonal first
insertion map. Source: the supplied Cauchy-transform reroute (comparison-L).
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem hasFDerivAt_resolvent_sq_of_isHermitian (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    HasFDerivAt (fun B : M => (resolvent B ζ)^2)
      (rationalBlockMap 1 ((C ζ-X)^2) A A) A := by
  have hQ : IsUnit (aeval A ((C ζ-X)^2)) := by
    simpa only [map_pow] using (isUnit_aeval_shift ζ A hA hζ).pow 2
  have h := hasFDerivAt_rationalMatrixEval 1 ((C ζ-X)^2) A hQ
  have he : (rationalMatrixEval 1 ((C ζ-X)^2) : M → M) =
      fun B => (resolvent B ζ)^2 := funext (rationalMatrixEval_resolvent_sq ζ)
  rwa [he] at h

/-- Applying the squared resolvent derivative gives exactly the two ordered
three-resolvent words. -/
theorem fderiv_resolvent_sq_apply (ζ : ℂ) (A H : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    fderiv ℂ (fun B : M => (resolvent B ζ)^2) A H =
      resolventSquareDifference ζ A A H := by
  rw [(hasFDerivAt_resolvent_sq_of_isHermitian ζ A hA hζ).fderiv,
    rationalBlockMap_apply,rationalBlockDifference_resolvent_sq ζ A A H hA hA hζ]

/-- The normalized trace derivative as a continuous complex linear map. -/
def traceResolventDerivative (ζ : ℂ) (A : M) : M →L[ℂ] ℂ :=
  (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.comp
    (rationalBlockMap 1 (C ζ-X) A A)

/-- Cyclicity puts the insertion direction in front of the squared resolvent. -/
theorem traceResolventDerivative_apply (ζ : ℂ) (A H : M) :
    traceResolventDerivative ζ A H = normalizedTrace (H * (resolvent A ζ)^2) := by
  simp only [traceResolventDerivative,ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap',normalizedTraceLinearMap_apply,rationalBlockMap_apply]
  rw [rationalBlockDifference_resolvent]
  rw [Matrix.mul_assoc,normalizedTrace_mul_comm (resolvent A ζ) (H*resolvent A ζ),
    pow_two,Matrix.mul_assoc]

/-- The actual normalized trace resolvent has the advertised cyclic derivative.
Source: the supplied Cauchy-transform interpolation.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem hasFDerivAt_normalizedTrace_resolvent (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    HasFDerivAt (fun B : M => normalizedTrace (resolvent B ζ))
      (traceResolventDerivative ζ A) A := by
  exact ((normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.hasFDerivAt).comp A
    (hasFDerivAt_resolvent_of_isHermitian ζ A hA hζ)

/-- Restricting scalars yields the real derivative required by real Gaussian
coordinates, without changing the actual trace-resolvent function. -/
theorem hasFDerivAt_normalizedTrace_resolvent_real (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    HasFDerivAt (fun B : M => normalizedTrace (resolvent B ζ))
      ((traceResolventDerivative ζ A).restrictScalars ℝ) A :=
  (hasFDerivAt_normalizedTrace_resolvent ζ A hA hζ).restrictScalars ℝ

end NLAlib
