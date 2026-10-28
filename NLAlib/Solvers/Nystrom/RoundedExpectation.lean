import NLAlib.Solvers.Nystrom.RoundedBudget
import NLAlib.Solvers.Nystrom.FullCapture

/-!
# Unconditional FTU expectations at the rounded width

The original width `2 ceil(3 d_eff/2)+1` is allowed to exceed the ambient
dimension. Such sketches capture the PSD input exactly almost surely. The
zero-input case is included, so neither an artificial lower bound on effective
dimension nor ambient-dimension capping is required.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The native FTU preconditioner has expected condition number below 28 at
the original rounded effective-dimension width, including zero inputs and
widths above the ambient dimension.
atlas: nystrom-pcg (partial) -/
theorem integrable_and_integral_conditionNumber_nystrom_rounded_lt_28
    {Ωs : Type*} [MeasurableSpace Ωs] {ν : Measure Ωs}
    {n : ℕ} [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ)
    (Ω : Ωs → Matrix (Fin n) (Fin (nystromSketchWidth A μ)) ℝ)
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin (nystromSketchWidth A μ))) ν) :
    Integrable (fun ω => (conditionNumber (nystromPreconditionedMatrix A
      (nystrom A (Ω ω)) (nystromFloor A (Ω ω)) μ)).toReal) ν ∧
      ∫ ω, (conditionNumber (nystromPreconditionedMatrix A
        (nystrom A (Ω ω)) (nystromFloor A (Ω ω)) μ)).toReal ∂ν < 28 := by
  have := hΩ.isProbabilityMeasure
  by_cases hAz : A = 0
  · subst A
    have he (ω : Ωs) := conditionNumber_nystromPreconditionedMatrix_zero_eq_one (Ω ω) hμ
    refine ⟨(integrable_const 1).congr (Filter.Eventually.of_forall fun ω => (he ω).symm), ?_⟩
    rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const,
      probReal_univ, one_smul]
    norm_num
  by_cases hw : nystromSketchWidth A μ ≤ n
  · exact integrable_and_integral_conditionNumber_nystromPreconditionedMatrix_lt_28
      hA hμ (nystromSketchHead_pos_of_ne_zero hAz hμ) hw (le_nystromSketchHead A μ) Ω hΩ
  · have he := ae_conditionNumber_nystromPreconditionedMatrix_eq_one_of_dim_le
      hA Ω hΩ (by omega) hμ
    refine ⟨(integrable_const 1).congr (he.mono fun _ h => h.symm), ?_⟩
    rw [integral_congr_ae he, integral_const, probReal_univ, one_smul]
    norm_num

open scoped Matrix.Norms.L2Operator in
/-- A native residual expectation at the exact rounded width. This supplies a
constant-probability event on which the deterministic PCG energy bound has
constants independent of the condition number of the original system.
atlas: nystrom-pcg (partial) -/
theorem integrable_and_integral_specNorm_sub_nystrom_rounded_le
    {Ωs : Type*} [MeasurableSpace Ωs] {ν : Measure Ωs}
    {n : ℕ} [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ)
    (Ω : Ωs → Matrix (Fin n) (Fin (nystromSketchWidth A μ)) ℝ)
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin (nystromSketchWidth A μ))) ν) :
    Integrable (fun ω => specNorm (A-nystrom A (Ω ω))) ν ∧
      ∫ ω, specNorm (A-nystrom A (Ω ω)) ∂ν ≤ (6+2*Real.exp 1^2)*μ := by
  have := hΩ.isProbabilityMeasure
  have hb : 0 ≤ (6+2*Real.exp 1^2)*μ := by positivity
  by_cases hAz : A = 0
  · subst A
    have he (ω : Ωs) : specNorm ((0 : Matrix (Fin n) (Fin n) ℝ)-nystrom 0 (Ω ω)) = 0 := by
      simp [nystrom, specNorm_zero]
    refine ⟨(integrable_const 0).congr (Filter.Eventually.of_forall fun ω => (he ω).symm), ?_⟩
    rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_zero]
    exact hb
  by_cases hw : nystromSketchWidth A μ ≤ n
  · have hk0 := nystromSketchHead_pos_of_ne_zero hAz hμ
    exact integrable_and_integral_specNorm_sub_nystrom_le_of_effectiveDimension
      hA hμ hk0 (by unfold nystromSketchWidth at hw; omega) (le_nystromSketchHead A μ) Ω hΩ
  · have he : (fun ω => specNorm (A-nystrom A (Ω ω))) =ᵐ[ν] fun _ => 0 := by
      filter_upwards [ae_nystrom_eq_of_dim_le hA Ω hΩ (by omega)] with ω hω
      rw [hω, sub_self, specNorm_zero]
    refine ⟨(integrable_const 0).congr he.symm, ?_⟩
    rw [integral_congr_ae he, integral_zero]
    exact hb

end NLAlib
