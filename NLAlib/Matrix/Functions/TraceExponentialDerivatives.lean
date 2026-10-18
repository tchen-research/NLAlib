import NLAlib.Matrix.Functions.ExpLog
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Multivariate derivatives of the trace exponential

The ordinary directional derivatives of the trace exponential are evaluations
of its real Fréchet derivatives on repeated directions. In particular the
second derivative is a genuine quadratic form, which can be contracted with
all real and imaginary entry covariances in Gaussian replacement arguments.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace exponential is smooth as a function of every real matrix entry,
including at matrices which are not Hermitian. -/
theorem contDiff_traceExp {k : WithTop ℕ∞} :
    ContDiff ℝ k (traceExp : Matrix n n ℂ → ℝ) := by
  have he : ContDiff ℝ k (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) :=
    (show AnalyticOnNhd ℝ NormedSpace.exp Set.univ from
      fun A _ => NormedSpace.exp_analytic A).contDiff
  exact Complex.reCLM.contDiff.comp
    ((Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap.contDiff.comp he)

/-- Every ordinary directional derivative of the trace exponential is its
multilinear Fréchet derivative evaluated on the same direction in each slot.
No self-adjointness hypothesis is required for this differential identity. -/
theorem iteratedDeriv_traceExp_add_smul_eq_iteratedFDeriv
    (A H : Matrix n n ℂ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun x : ℝ => traceExp (A + x • H)) t =
      iteratedFDeriv ℝ k traceExp (A + t • H) (fun _ => H) := by
  let L : ℝ →L[ℝ] Matrix n n ℂ := ContinuousLinearMap.toSpanSingleton ℝ H
  have h := L.iteratedFDeriv_comp_right
    (f := fun B => traceExp (A + B))
    (contDiff_traceExp.comp (contDiff_const.add contDiff_id) : ContDiff ℝ (k : WithTop ℕ∞) _)
    t (i := k) le_rfl
  have he := congrArg (fun T => T (fun _ : Fin k => (1 : ℝ))) h
  simpa only [L, iteratedDeriv_eq_iteratedFDeriv, Function.comp_def,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul,
    iteratedFDeriv_comp_add_left] using he

/-- The ordinary first directional derivative is evaluation of the actual
real Fréchet derivative. -/
theorem deriv_traceExp_add_smul_zero_eq_fderiv
    (A H : Matrix n n ℂ) :
    deriv (fun x : ℝ => traceExp (A + x • H)) 0 = fderiv ℝ traceExp A H := by
  simpa only [iteratedDeriv_one, zero_smul, add_zero, iteratedFDeriv_one_apply] using
    iteratedDeriv_traceExp_add_smul_eq_iteratedFDeriv A H 1 0

/-- The real continuous bilinear Hessian of the trace exponential at `A`.
Its diagonal is the second ordinary derivative in the chosen direction. -/
def traceExpHessian (A : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin1 ℝ (Matrix n n ℂ) ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (iteratedFDeriv ℝ 2 traceExp A).curryLeft

/-- The second directional derivative at zero is the diagonal of the actual
real bilinear Hessian, hence depends quadratically on the entire direction. -/
theorem iteratedDeriv_two_traceExp_add_smul_zero_eq_hessian
    (A H : Matrix n n ℂ) :
    iteratedDeriv 2 (fun x : ℝ => traceExp (A + x • H)) 0 =
      traceExpHessian A H H := by
  rw [iteratedDeriv_traceExp_add_smul_eq_iteratedFDeriv]
  simp only [zero_smul, add_zero, traceExpHessian, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  ext i
  fin_cases i <;> simp

/-- Rescaling the direction multiplies the second trace-exponential
directional derivative by exactly the squared scale. -/
theorem iteratedDeriv_two_traceExp_add_smul_smul_zero
    (A H : Matrix n n ℂ) (c : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • (c • H))) 0 =
      c ^ 2 * iteratedDeriv 2 (fun t : ℝ => traceExp (A + t • H)) 0 := by
  rw [iteratedDeriv_two_traceExp_add_smul_zero_eq_hessian,
    iteratedDeriv_two_traceExp_add_smul_zero_eq_hessian]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end NLAlib
