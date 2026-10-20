import NLAlib.ForMathlib.Analysis.Matrix.DeterminantDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Actual real Frechet derivative of a complex matrix determinant

The determinant is a finite sum of products of actual continuous matrix
entries. Smoothness supplies its Frechet derivative; the checked Jacobi
path formula identifies that derivative on every matrix direction.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.L2Operator
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- The actual complex determinant is real-smooth in the spectral matrix
norm, in every differentiability order and also for empty dimensions. -/
theorem contDiff_det (k : ℕ∞ω) : ContDiff ℝ k (fun X : M => X.det) := by
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  exact (Matrix.entryLinearMap ℝ ℂ (σ i) i).toContinuousLinearMap.contDiff

/-- The genuine Frechet determinant derivative is the adjugate trace
functional in the actual spectral matrix norm. It includes singular and
empty matrices, with no invertibility assumption. -/
theorem hasFDerivAt_det (A : M) :
    HasFDerivAt (fun X : M => X.det)
      (((Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap).comp
        (ContinuousLinearMap.mul ℝ M A.adjugate)) A := by
  have hd : Differentiable ℝ (fun X : M => X.det) :=
    (contDiff_det (n := n) 1).differentiable one_ne_zero
  have hD := (hd A).hasFDerivAt
  have he : fderiv ℝ (fun X : M => X.det) A =
      ((Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap).comp
        (ContinuousLinearMap.mul ℝ M A.adjugate) := by
    ext H
    have hline : HasDerivAt (fun t : ℝ => A + t • H) H 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add A
    have hDA : HasFDerivAt (fun X : M => X.det)
        (fderiv ℝ (fun X : M => X.det) A) (A + (0 : ℝ) • H) := by
      simpa only [zero_smul, add_zero] using hD
    have h₁ := hDA.comp_hasDerivAt (0 : ℝ) hline
    have h₂ := hline.matrix_det
    simp only [zero_smul, add_zero] at h₁ h₂
    exact h₁.unique h₂
  rwa [he] at hD

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Jacobi's actual Frechet chain rule for arbitrary real normed parameter
spaces, rather than only a scalar line. -/
theorem _root_.HasFDerivAt.matrix_det {f : X → M} {f' : X →L[ℝ] M} {x : X}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => (f y).det)
      ((((Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap).comp
        (ContinuousLinearMap.mul ℝ M (f x).adjugate)).comp f') x :=
  (hasFDerivAt_det (f x)).comp x hf

end Matrix
