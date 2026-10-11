import NLAlib.Concentration.Matrix.OperatorConvexity.TraceExpBounds

/-!
# Trace exponential integrability from upper spectral bounds

The actual potential is nonnegative and bounded by a scalar trace exponential. Lower
spectral bounds or integrability of a predictable offset are unnecessary.
-/

noncomputable section

open MeasureTheory Matrix Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace exponential is continuous on all finite complex matrices.
Source: continuous matrix exponential and linear trace; helper for `matrix-freedman` (partial). -/
theorem continuous_traceExp : Continuous (traceExp : Matrix n n ℂ → ℝ) := by
  let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact Complex.continuous_re.comp
    ((Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap.continuous.comp NormedSpace.exp_continuous)

/-- Hermitian trace exponentials are nonnegative, including the empty finite matrix.
Source: positivity of the actual matrix exponential and its trace;
helper for `matrix-freedman` (partial). -/
theorem traceExp_nonneg_of_isHermitian (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    0 ≤ traceExp A := by
  have h := (posDef_matrixExp_and_matrixLog_matrixExp_finite A hA).1.posSemidef.trace_nonneg
  exact (RCLike.nonneg_iff.mp h).1

/-- A scalar identity has trace exponential `card(n) exp(t)` for any finite labels.
Source: the exact scalar exponential identity; helper for `matrix-freedman` (partial). -/
theorem traceExp_smul_one_eq_card_mul_exp (t : ℝ) :
    traceExp (t • (1 : Matrix n n ℂ)) = Fintype.card n * Real.exp t := by
  unfold traceExp
  rw [matrixExp_smul_one_eq_exp_smul_one, Matrix.trace_smul]
  simp only [Matrix.trace_one, Complex.smul_re, Complex.natCast_re, smul_eq_mul, mul_comm]

/-- Actual upper bounds on two Hermitian random matrices give integrability of their
trace-exponential sum. The offsets may have arbitrarily negative eigenvalues.
Source: operator rederivations `eq:potentialbound` and `eq:condlieb` domination;
atlas `matrix-freedman` (partial). -/
theorem integrable_traceExp_add_of_ae_le_algebraMap {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [Nonempty n]
    {H X : Ω → Matrix n n ℂ} (hHMeas : AEStronglyMeasurable H μ)
    (hXMeas : AEStronglyMeasurable X μ)
    (hH : ∀ᵐ ω ∂μ, (H ω).IsHermitian) (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    {h a : ℝ} (hHBound : ∀ᵐ ω ∂μ, H ω ≤ algebraMap ℝ (Matrix n n ℂ) h)
    (hXBound : ∀ᵐ ω ∂μ, X ω ≤ algebraMap ℝ (Matrix n n ℂ) a) :
    Integrable (fun ω => traceExp (H ω + X ω)) μ := by
  refine Integrable.of_bound (continuous_traceExp.comp_aestronglyMeasurable (hHMeas.add hXMeas))
    ((Fintype.card n : ℝ) * Real.exp (h + a)) ?_
  filter_upwards [hH, hX, hHBound, hXBound] with ω hH hX hHb hXb
  have hsum : H ω + X ω ≤ (h + a) • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, add_smul] using add_le_add hHb hXb
  rw [Real.norm_eq_abs, abs_of_nonneg (traceExp_nonneg_of_isHermitian _ (hH.add hX))]
  exact (traceExp_le_traceExp_finite _ _ (hH.add hX)
    (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)) hsum).trans_eq
      (traceExp_smul_one_eq_card_mul_exp (h + a))

end NLAlib
