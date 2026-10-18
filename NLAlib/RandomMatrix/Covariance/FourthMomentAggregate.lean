import NLAlib.RandomMatrix.Covariance.FourthMomentSummands
import NLAlib.RandomMatrix.Covariance.SampleCovarianceMoments

/-!
# Moments of the isotropic empirical covariance defect

The full second moments and every real quadratic variance of identity minus
the empirical covariance follow from finite fourth observation moments.
Source: Tropp (2026), Section 3.3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
namespace NLAlib
variable {Ω d ι : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

open scoped Matrix.Norms.L2Operator in
/-- The actual empirical covariance has finite full-entry second moments
under a finite fourth vector moment assumption. -/
theorem memLp_two_sampleCovariance_pi {X : Ω → d → ℝ} (hX : MemLp X 4 μ) :
    MemLp (fun ω : ι → Ω => sampleCovariance (fun i => X (ω i))) 2
      (Measure.pi (fun _ => μ)) := by
  apply Matrix.memLp_iff_entries.mpr
  intro a b
  have hi (i : ι) : MemLp (fun ω : ι → Ω => (X (ω i) a) * (X (ω i) b)) 2
      (Measure.pi (fun _ => μ)) :=
    ((Matrix.memLp_iff_entries.mp (memLp_two_vecMulVec_self_of_memLp_four hX)) a b).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => μ) i)
  have hh := (memLp_finsetSum Finset.univ (fun i _ => hi i)).const_smul ((Fintype.card ι : ℝ)⁻¹)
  have he : ((Fintype.card ι : ℝ)⁻¹ •
      fun ω : ι → Ω => ∑ i, X (ω i) a * X (ω i) b) =
      fun ω => sampleCovariance (fun i => X (ω i)) a b := by
    funext ω
    simp only [sampleCovariance, star_trivial, Matrix.smul_apply,
      Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [he] at hh
  exact hh

open scoped Matrix.Norms.L2Operator in
/-- Isotropy centers the actual empirical covariance defect. -/
theorem integral_one_sub_sampleCovariance_pi_eq_zero [Nonempty ι]
    {X : Ω → d → ℝ} (hX : MemLp X 4 μ)
    (hisotropic : (∫ ω, vecMulVec (X ω) (X ω) ∂μ) = (1 : Matrix d d ℝ)) :
    (∫ ω : ι → Ω, 1 - sampleCovariance (fun i => X (ω i))
      ∂Measure.pi (fun _ => μ)) = 0 := by
  rw [integral_sub (integrable_const _) ((memLp_two_sampleCovariance_pi hX).integrable (by norm_num)),
    integral_sampleCovariance_pi (hX.mono_exponent (by norm_num)), hisotropic]
  simp

open scoped Matrix.Norms.L2Operator in
/-- Every real quadratic probe of the isotropic empirical covariance
defect has variance at most `β² / sampleCount` times the fourth power of
the probe norm. No bounded observation hypothesis is needed. -/
theorem variance_quadForm_one_sub_sampleCovariance_pi_le
    {X : Ω → d → ℝ} {β : ℝ} (hX : MemLp X 4 μ)
    (hisotropic : (∫ ω, vecMulVec (X ω) (X ω) ∂μ) = (1 : Matrix d d ℝ))
    (hfourth : ∀ a : d → ℝ,
      Var[fun ω => (X ω ⬝ᵥ a) ^ 2; μ] ≤
        β ^ 2 * (∫ ω, (X ω ⬝ᵥ a) ^ 2 ∂μ) ^ 2)
    (u : d → ℝ) :
    Var[fun ω : ι → Ω => quadForm (1 - sampleCovariance (fun i => X (ω i))) u;
      Measure.pi (fun _ => μ)] ≤
      (β ^ 2 / (Fintype.card ι : ℝ)) * ‖WithLp.toLp 2 u‖ ^ 4 := by
  have hq : AEStronglyMeasurable
      (fun ω : ι → Ω => quadForm (sampleCovariance (fun i => X (ω i))) u)
      (Measure.pi (fun _ => μ)) :=
    ((quadFormContinuousLinearMap u).comp_memLp' (memLp_two_sampleCovariance_pi hX)).aestronglyMeasurable
  have he : (fun ω : ι → Ω => quadForm (1 - sampleCovariance (fun i => X (ω i))) u) =
      fun ω => quadForm (1 : Matrix d d ℝ) u - quadForm (sampleCovariance (fun i => X (ω i))) u := by
    funext ω
    exact (quadFormLinearMap u).map_sub _ _
  rw [he, variance_const_sub hq, variance_quadForm_sampleCovariance_pi hX]
  have hbound := hfourth u
  rw [integral_dotProduct_sq_eq_norm_sq_of_isotropic (hX.mono_exponent (by norm_num)) hisotropic] at hbound
  calc
    (Fintype.card ι : ℝ)⁻¹ * Var[fun ω => (X ω ⬝ᵥ u) ^ 2; μ] ≤
        (Fintype.card ι : ℝ)⁻¹ * (β ^ 2 * (‖WithLp.toLp 2 u‖ ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

end NLAlib
