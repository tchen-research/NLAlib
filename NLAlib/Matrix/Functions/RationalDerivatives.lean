import NLAlib.Matrix.Functions.RationalBlockMaps
import NLAlib.ForMathlib.Analysis.ContinuousSecant
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Full Fréchet derivatives of rational matrix functions

Exact finite differences and continuity of their linear maps prove both
Fréchet derivatives on the open nonsingular-denominator domain.
The second derivative is the sum of both ordered insertion maps.
Source: matrix-toolkit derivations, F18--F19.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Filter ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n 𝕜
private local instance : ContinuousAdd (M →L[𝕜] M →L[𝕜] M) :=
  (inferInstance : IsTopologicalAddGroup (M →L[𝕜] M →L[𝕜] M)).toContinuousAdd

/-- Rational matrix functions have an open denominator domain. -/
theorem isOpen_rationalMatrixDomain (Q : 𝕜[X]) :
    IsOpen {A : M | IsUnit (aeval A Q)} :=
  Units.isOpen.preimage (continuous_iff_continuousAt.mpr
    (fun A => (Q.hasFDerivAt_aeval_noncomm A).continuousAt))

theorem eventually_isUnit_aeval (Q : 𝕜[X]) (A : M) (hA : IsUnit (aeval A Q)) :
    ∀ᶠ B in 𝓝 A, IsUnit (aeval B Q) :=
  (isOpen_rationalMatrixDomain (n := n) Q).mem_nhds hA

/-- The full Fréchet derivative is the first block difference on the diagonal.
Source: F19.
atlas: matrix-function-block-divided-differences (partial) -/
theorem hasFDerivAt_rationalMatrixEval (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) :
    HasFDerivAt (rationalMatrixEval P Q) (rationalBlockMap P Q A A) A := by
  apply hasFDerivAt_of_continuous_secant (L := fun B => rationalBlockMap P Q B A)
  · simpa only [Function.comp_def] using
      (continuousAt_rationalBlockMap P Q A A hA hA).comp
        (x := A) (f := fun B : M => (B,A)) (continuous_id.prodMk continuous_const).continuousAt
  · filter_upwards [eventually_isUnit_aeval Q A hA] with B hB
    simpa only [rationalBlockMap_apply] using rationalMatrixEval_sub P Q B A hB hA

/-- The continuous bilinear Hessian is the sum of the two insertion orders. -/
def rationalMatrixHessian (P Q : 𝕜[X]) (A : M) : M →L[𝕜] M →L[𝕜] M :=
  rationalSecondBlockMap P Q A A A + (rationalSecondBlockMap P Q A A A).flip

@[simp] theorem rationalMatrixHessian_apply (P Q : 𝕜[X]) (A G H : M) :
    rationalMatrixHessian P Q A G H = rationalSecondBlockDifference P Q A A A G H +
      rationalSecondBlockDifference P Q A A A H G := by
  simp [rationalMatrixHessian]

/-- Differentiating the first difference on its diagonal gives both ordered
second differences, as an operator-norm Fréchet derivative.
Source: F19.
atlas: matrix-function-block-divided-differences (partial) -/
theorem hasFDerivAt_rationalBlockMap_diagonal (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) :
    HasFDerivAt (fun B : M => rationalBlockMap P Q B B) (rationalMatrixHessian P Q A) A := by
  let L : M → M →L[𝕜] M →L[𝕜] M := fun B =>
    rationalSecondBlockMap P Q B A B + (rationalSecondBlockMap P Q A B A).flip
  change HasFDerivAt _ (L A) A
  apply hasFDerivAt_of_continuous_secant
  · have h₁ : ContinuousAt (fun B : M => rationalSecondBlockMap P Q B A B) A := by
      simpa only [Function.comp_def] using
        (continuousAt_rationalSecondBlockMap P Q A A A hA hA hA).comp
          (x := A) (f := fun B : M => (B,A,B))
          (continuous_id.prodMk (continuous_const.prodMk continuous_id)).continuousAt
    have h₂ : ContinuousAt (fun B : M => rationalSecondBlockMap P Q A B A) A := by
      simpa only [Function.comp_def] using
        (continuousAt_rationalSecondBlockMap P Q A A A hA hA hA).comp
          (x := A) (f := fun B : M => (A,B,A))
          (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousAt
    exact h₁.add (continuous_flip_matrixBilinear.continuousAt.comp h₂)
  · filter_upwards [eventually_isUnit_aeval Q A hA] with B hB
    ext H i j
    have h₁ := congrArg (fun D : M => D i j)
      (rationalBlockDifference_sub_left P Q B A B H hB hA hB)
    have h₂ := congrArg (fun D : M => D i j)
      (rationalBlockDifference_sub_right P Q A B A H hA hB hA)
    simp only [Matrix.sub_apply] at h₁ h₂
    simp only [sub_apply, rationalBlockMap_apply, L, add_apply, flip_apply,
      rationalSecondBlockMap_apply, Matrix.add_apply, Matrix.sub_apply]
    calc
      _ = (rationalBlockDifference P Q B B H i j - rationalBlockDifference P Q A B H i j) +
          (rationalBlockDifference P Q A B H i j - rationalBlockDifference P Q A A H i j) := by abel
      _ = _ := by rw [h₁, h₂]

/-- The actual Fréchet derivative of the rational calculus is differentiable,
with Hessian the symmetrized ordered second difference.
Source: F19.
atlas: matrix-function-block-divided-differences (partial) -/
theorem hasFDerivAt_fderiv_rationalMatrixEval (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) :
    HasFDerivAt (fun B : M => fderiv 𝕜 (rationalMatrixEval P Q) B)
      (rationalMatrixHessian P Q A) A := by
  apply (hasFDerivAt_rationalBlockMap_diagonal P Q A hA).congr_of_eventuallyEq
  filter_upwards [eventually_isUnit_aeval Q A hA] with B hB
  exact (hasFDerivAt_rationalMatrixEval P Q B hB).fderiv

/-- Applying the actual first Fréchet derivative gives the triangular block
difference. Source: F19.
atlas: matrix-function-block-divided-differences (partial) -/
theorem fderiv_rationalMatrixEval_apply (P Q : 𝕜[X]) (A H : M)
    (hA : IsUnit (aeval A Q)) :
    fderiv 𝕜 (rationalMatrixEval P Q) A H = rationalBlockDifference P Q A A H := by
  rw [(hasFDerivAt_rationalMatrixEval P Q A hA).fderiv, rationalBlockMap_apply]

/-- The actual second Fréchet derivative is the sum of the two ordered
second block differences. Source: F19.
atlas: matrix-function-block-divided-differences (partial) -/
theorem fderiv_fderiv_rationalMatrixEval_apply (P Q : 𝕜[X]) (A G H : M)
    (hA : IsUnit (aeval A Q)) :
    fderiv 𝕜 (fun B : M => fderiv 𝕜 (rationalMatrixEval P Q) B) A G H =
      rationalSecondBlockDifference P Q A A A G H +
        rationalSecondBlockDifference P Q A A A H G := by
  rw [(hasFDerivAt_fderiv_rationalMatrixEval P Q A hA).fderiv,
    rationalMatrixHessian_apply]

end NLAlib
