import NLAlib.Concentration.Matrix.OperatorConvexity.TraceExpBounds
import NLAlib.Concentration.Matrix.Laplace.TailSpectralComparison
import NLAlib.ForMathlib.Analysis.Matrix.Order

/-!
# The actual matrix crossing forces a trace-potential crossing

The norm bound on the random variation is used only at the crossing. Trace monotonicity,
the exact scalar shift, and the existing extremal-eigenvalue comparison keep the constants.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The existing extremal-eigenvalue trace comparison transported to arbitrary finite
labels. Source: Tropp 2015, equation (3.2.3); exact reindexing of the recorded comparison.
Atlas `matrix-freedman` (partial). -/
theorem exp_mul_lambdaMax_le_traceExp_smul_finite (A : Matrix n n ℂ)
    (hA : A.IsHermitian) {θ : ℝ} (hθ : 0 < θ) :
    Real.exp (θ * lambdaMax A) ≤ traceExp (θ • A) := by
  let e := Fintype.equivFin n
  let E := reindexStarAlgEquiv e
  have h := (exp_mul_lambdaMax_lambdaMin_le_traceExp_smul (E A) (hA.reindex e) θ).2.1 hθ
  change Real.exp (θ * lambdaMax (Matrix.reindex e e A)) ≤
    traceExp (θ • Matrix.reindex e e A) at h
  have hs : θ • Matrix.reindex e e A = Matrix.reindex e e (θ • A) := by
    ext i j
    rfl
  rw [hs, lambdaMax_reindex, traceExp_reindex] at h
  exact h

/-- At the original crossing `lambdaMax(Y)≥t` and `‖W‖≤v`, the actual compensated
trace potential is at least `exp(θt-gv)`. No deterministic substitute for the random
variation is assumed outside this event.
Source: operator rederivations Section 3.4, crossing bound;
atlas `matrix-freedman` (partial). -/
theorem exp_sub_le_traceExp_compensated_of_crossing (Y W : Matrix n n ℂ)
    (hY : Y.IsHermitian) (hW : W.IsHermitian) {θ g t v : ℝ}
    (hθ : 0 < θ) (hg : 0 ≤ g) (ht : t ≤ lambdaMax Y) (hv : ‖W‖ ≤ v) :
    Real.exp (θ * t - g * v) ≤ traceExp (θ • Y - g • W) := by
  have hWUpper : W ≤ algebraMap ℝ (Matrix n n ℂ) v := by
    apply le_algebraMap_of_spectrum_le _ hW
    intro x hx
    have hnorm : |x| ≤ ‖W‖ := by simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hx
    exact (le_abs_self x).trans (hnorm.trans hv)
  have hscale := matrix_smul_le_smul_of_nonneg hWUpper hg
  have hscale' : g • W ≤ (g * v) • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, smul_smul] using hscale
  have hLoewner : θ • Y - (g * v) • (1 : Matrix n n ℂ) ≤ θ • Y - g • W :=
    sub_le_sub_left hscale' _
  have hleft : (θ • Y - (g * v) • (1 : Matrix n n ℂ)).IsHermitian :=
    (hY.smul (IsSelfAdjoint.all _)).sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  have hright : (θ • Y - g • W).IsHermitian :=
    (hY.smul (IsSelfAdjoint.all _)).sub (hW.smul (IsSelfAdjoint.all _))
  have hmono := traceExp_le_traceExp_finite _ _ hleft hright hLoewner
  have hshift : traceExp (θ • Y - (g * v) • (1 : Matrix n n ℂ)) =
      Real.exp (-(g * v)) * traceExp (θ • Y) := by
    simpa only [sub_eq_add_neg, neg_smul] using traceExp_add_smul_one_eq_exp_mul (θ • Y) (-(g * v))
  rw [hshift] at hmono
  calc
    Real.exp (θ * t - g * v) = Real.exp (-(g * v)) * Real.exp (θ * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(g * v)) * Real.exp (θ * lambdaMax Y) := by gcongr
    _ ≤ Real.exp (-(g * v)) * traceExp (θ • Y) :=
      mul_le_mul_of_nonneg_left (exp_mul_lambdaMax_le_traceExp_smul_finite Y hY hθ) (Real.exp_pos _).le
    _ ≤ traceExp (θ • Y - g • W) := hmono

end NLAlib
