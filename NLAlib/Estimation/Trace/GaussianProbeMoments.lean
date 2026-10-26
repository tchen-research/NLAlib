import NLAlib.Estimation.Trace.HutchinsonTail

/-!
# Gaussian probe averages: integrability and centered second moments

A Gaussian probe average is the quadratic form of its block diagonal matrix.
The fourth coordinate moments give genuine square integrability, and the existing
Gaussian quadratic-form identities give its mean and exact variance.

Source: Avron--Toledo (2011), Lemma 5, applied to the block diagonal quadratic form.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {n κ Ω : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Fintype κ] [DecidableEq κ] [DecidableEq n] [IsProbabilityMeasure μ] in
/-- A Gaussian quadratic form has a finite second moment. -/
theorem memLp_two_quadForm_of_hasLaw_gaussianVector (A : Matrix n n ℝ)
    {z : Ω → n → ℝ} (hz : HasLaw z (gaussianVector n) μ) :
    MemLp (fun ω => quadForm A (z ω)) 2 μ := by
  have hl := fun i => hz.hasLaw_eval_gaussianReal i
  have h4 (i : n) : MemLp (fun ω => z ω i) 4 μ := by
    have h := memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by simp)
    rw [← (hl i).map_eq] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hl i).aemeasurable).1 h
  simp_rw [quadForm_eq_sum]
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  have hij : MemLp (fun ω => z ω i * z ω j) 2 μ := (h4 j).mul' (h4 i)
  exact hij.const_mul (A i j)

omit [DecidableEq n] [IsProbabilityMeasure μ] in
/-- A Gaussian Hutchinson average has a finite second moment. -/
theorem memLp_two_hutchinsonEstimate_of_hasLaw_gaussianMatrix (A : Matrix n n ℝ)
    {G : Ω → Matrix n κ ℝ} (hG : HasLaw G (gaussianMatrix n κ) μ) :
    MemLp (fun ω => hutchinsonEstimate A (G ω)) 2 μ := by
  simpa only [Function.comp_apply, quadForm_hutchinsonBlock] using
    memLp_two_quadForm_of_hasLaw_gaussianVector (hutchinsonBlock (κ := κ) A)
      (hasLaw_uncurry_gaussianMatrix.comp hG)

omit [DecidableEq n] in
/-- The mean of a nonempty Gaussian probe average is the trace. -/
theorem integral_hutchinsonEstimate_of_hasLaw_gaussianMatrix [Nonempty κ]
    (A : Matrix n n ℝ) {G : Ω → Matrix n κ ℝ}
    (hG : HasLaw G (gaussianMatrix n κ) μ) :
    ∫ ω, hutchinsonEstimate A (G ω) ∂μ = A.trace := by
  simpa only [Function.comp_apply, quadForm_hutchinsonBlock, trace_hutchinsonBlock] using
    integral_quadForm_eq_trace_of_hasLaw_gaussianVector (hutchinsonBlock (κ := κ) A)
      (hasLaw_uncurry_gaussianMatrix.comp hG)

/-- The centered second moment of a symmetric Gaussian probe average is exactly
`2 * frobSq A / card κ`. The matrix dimension may be empty. -/
theorem integral_sq_hutchinsonEstimate_sub_trace_of_hasLaw_gaussianMatrix [Nonempty κ]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {G : Ω → Matrix n κ ℝ}
    (hG : HasLaw G (gaussianMatrix n κ) μ) :
    ∫ ω, (hutchinsonEstimate A (G ω) - A.trace) ^ 2 ∂μ =
      2 * frobSq A / Fintype.card κ := by
  have hB : (hutchinsonBlock (κ := κ) A).IsHermitian :=
    (Matrix.isHermitian_blockDiagonal_iff.mpr (fun _ => hA)).smul (by simp)
  have hv := variance_quadForm_of_isHermitian_of_hasLaw_gaussianVector hB
    (hasLaw_uncurry_gaussianMatrix.comp hG)
  simp only [Function.comp_apply, quadForm_hutchinsonBlock, frobSq_hutchinsonBlock] at hv
  rw [variance_eq_integral
    (memLp_two_hutchinsonEstimate_of_hasLaw_gaussianMatrix A hG).aemeasurable,
    integral_hutchinsonEstimate_of_hasLaw_gaussianMatrix A hG] at hv
  exact hv.trans (by ring)

end NLAlib
