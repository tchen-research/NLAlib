import NLAlib.RandomMatrix.Covariance.WhiteningMoments
import NLAlib.ForMathlib.Probability.SampleAverage

/-!
# Exact moments of an iid sample covariance

The empirical covariance has the same actual second moment as one observation.
Each quadratic probe is an average of independent squared linear marginals,
so its variance is exactly the single-observation variance divided by the
sample count. These facts retain unbounded observations with finite fourth
moments. Source: Tropp (2026), Section 3.3.1.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Matrix

namespace NLAlib

variable {Ω d ι : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d] [Fintype ι]
  {μ : Measure Ω}

omit [DecidableEq d] in
/-- A real sample covariance quadratic probe is the empirical average of
the squared linear probes. The formula also includes an empty sample family. -/
theorem quadForm_sampleCovariance (X : ι → d → ℝ) (u : d → ℝ) :
    quadForm (sampleCovariance X) u =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, (X i ⬝ᵥ u) ^ 2 := by
  change quadFormLinearMap u ((Fintype.card ι : ℝ)⁻¹ • ∑ i, vecMulVec (X i) (star (X i))) = _
  rw [map_smul, map_sum]
  change (Fintype.card ι : ℝ)⁻¹ * ∑ i, quadForm (vecMulVec (X i) (X i)) u = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [quadForm, star_trivial, Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul]
  rw [dotProduct_comm u (X i)]
  ring

open scoped Matrix.Norms.L2Operator in
/-- The actual mean of a nonempty iid sample covariance equals the original
second-moment matrix. No bounded-support assumption is needed. -/
theorem integral_sampleCovariance_pi [Nonempty ι] [IsProbabilityMeasure μ]
    {X : Ω → d → ℝ} (hX : MemLp X 2 μ) :
    (∫ ω : ι → Ω, sampleCovariance (fun i => X (ω i))
      ∂Measure.pi (fun _ => μ)) = ∫ ω, vecMulVec (X ω) (X ω) ∂μ := by
  simpa only [sampleCovariance, star_trivial] using
    integral_inv_card_smul_sum_pi (ι := ι) μ (integrable_vecMulVec_self_of_memLp_two hX)

open scoped Matrix.Norms.L2Operator in
/-- Fourth vector moments give square-integrable squared linear marginals. -/
theorem memLp_two_sq_dotProduct_of_memLp_four {X : Ω → d → ℝ}
    (hX : MemLp X 4 μ) (u : d → ℝ) :
    MemLp (fun ω => (X ω ⬝ᵥ u) ^ 2) 2 μ := by
  have h := (quadFormContinuousLinearMap u).comp_memLp'
    (memLp_two_vecMulVec_self_of_memLp_four hX)
  change MemLp (fun ω => quadForm (vecMulVec (X ω) (X ω)) u) 2 μ at h
  have hp (ω : Ω) : quadForm (vecMulVec (X ω) (X ω)) u = (X ω ⬝ᵥ u) ^ 2 := by
    simp only [quadForm, star_trivial, Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul]
    rw [dotProduct_comm u (X ω)]
    ring
  simpa only [hp] using h

/-- The variance of any iid sample covariance quadratic probe is exactly
the one-observation squared-linear-probe variance divided by the sample count.
Only finite fourth moments are used, and the empty sample family is included.
Source: Tropp (2026), Section 3.3.1.
atlas: sample-covariance-fourth-moment-lower (partial) -/
theorem variance_quadForm_sampleCovariance_pi [IsProbabilityMeasure μ]
    {X : Ω → d → ℝ} (hX : MemLp X 4 μ) (u : d → ℝ) :
    Var[fun ω : ι → Ω => quadForm (sampleCovariance (fun i => X (ω i))) u;
      Measure.pi (fun _ => μ)] =
      (Fintype.card ι : ℝ)⁻¹ * Var[fun ω => (X ω ⬝ᵥ u) ^ 2; μ] := by
  have hq : MemLp (fun ω : Ω => (X ω ⬝ᵥ u) ^ 2) 2 μ :=
    memLp_two_sq_dotProduct_of_memLp_four hX u
  have hv := variance_inv_card_mul_sum_pi (ι := ι) μ hq
  simpa only [quadForm_sampleCovariance] using hv

end NLAlib
