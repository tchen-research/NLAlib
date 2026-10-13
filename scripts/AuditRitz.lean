import NLAlib.Krylov.Spectral.MeasurableRitz
import NLAlib.Krylov.Processes.ArnoldiProcess
import NLAlib.Estimation.Quadrature.SLQ
import NLAlib.Estimation.Trace.Unbiased
import NLAlib.Polynomial.FunctionApproximation.ChebyshevCoefficients
/-! Ritz regressions: negative spectrum, breakdown, empty space, and trusted bridges. -/
open scoped Matrix
open NLAlib

example (q : ℕ) : lanczosRitzValue (-(1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => 1) (q + 1) = -1 := by
  let A := -(1 : Matrix (Fin 1) (Fin 1) ℝ)
  have hA : A.IsHermitian := Matrix.isHermitian_one.neg
  rw [lanczosRitzValue_eq_sSup_rayleigh hA]
  have hquot : ∀ x : Fin 1 → ℝ, x ≠ 0 → rayleighQuotient A x = -1 := by
    intro x hx
    have hp : x ⬝ᵥ x ≠ 0 := fun h => hx (dotProduct_self_eq_zero.mp h)
    rw [rayleighQuotient_eq_div]
    simp only [A, Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg]
    rw [neg_div, div_self hp]
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ => 1, ⟨self_mem_krylovSpace_succ A (fun _ => 1) q, ?_⟩, ?_⟩
    · intro h
      have h0 := congrFun h 0
      norm_num at h0
    · exact hquot _ (by intro h; have := congrFun h 0; norm_num at this)
  · rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    exact le_of_eq (hquot x hx)

example (A : Matrix (Fin 1) (Fin 1) ℝ) : lanczosRitzValue A (fun _ => 1) 0 = 0 :=
  lanczosRitzValue_eq_zero_of_space_eq_bot _ _ _ (krylovSpace_zero _ _)

example (A : Matrix (Fin 1) (Fin 1) ℝ) (q : ℕ) : lanczosRitzValue A 0 q = 0 :=
  lanczosRitzValue_eq_zero_of_space_eq_bot _ _ _ (krylovSpace_start_zero _ _)

#print axioms NLAlib.lanczosRitzValue_eq_iSup_rat
#print axioms NLAlib.measurable_lanczosRitzValue
#print axioms NLAlib.ritzValues_eq_of_range_eq

#print axioms NLAlib.hasOrthonormalCols_stoppedArnoldiMatrix
#print axioms NLAlib.range_stoppedArnoldiMatrix

#print axioms NLAlib.abs_slqEstimate_sub_hutchinsonEstimate_le
#print axioms NLAlib.integral_hutchPlusPlusEstimate_eq_trace_of_hasLaw_gaussianMatrix
#print axioms NLAlib.chebyshevAnalyticCoeff_eq_chebyshevCoeff
#print axioms NLAlib.chebyshevComplexCoeff_eq_ofReal_chebyshevCoeff
