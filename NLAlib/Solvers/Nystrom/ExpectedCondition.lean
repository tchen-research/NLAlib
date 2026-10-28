import NLAlib.Solvers.Nystrom.GaussianBudget
import NLAlib.Solvers.Nystrom.Measurability
import NLAlib.Matrix.Perturbation.SpectralContinuity
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Expected FTU condition number from effective dimension

This file integrates the condition number of the actual symmetric preconditioned
matrix. Its measurability is proved through fixed functional calculus, and the
refined native Gaussian residual supplies the bound independent of conditioning.
Source: Frangella--Tropp--Udell 2023, Theorem 5.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
namespace NLAlib

/-- The native Nyström floor is the last of the retained, zero-padded PSD
eigenvalues. This convention includes rank-deficient approximations. -/
def nystromFloor {n ℓ : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Ω : Matrix (Fin n) (Fin ℓ) ℝ) : ℝ := singularValues (nystrom A Ω) (ℓ-1)

open scoped Matrix.Norms.L2Operator in
/-- The ordinary finite FTU condition number is a measurable function of its
Gaussian sketch, including deficient sketches. -/
theorem measurable_conditionNumber_nystromPreconditionedMatrix {n ℓ : ℕ}
    [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ) :
    Measurable (fun Ω : Matrix (Fin n) (Fin ℓ) ℝ =>
      (conditionNumber (nystromPreconditionedMatrix A (nystrom A Ω) (nystromFloor A Ω) μ)).toReal) := by
  have hB := measurable_nystrom (t := Fin ℓ) A
  have ha : Measurable (nystromFloor (ℓ := ℓ) A) :=
    (continuous_singularValues_array (ℓ-1)).measurable.comp hB
  have hBN (Ω : Matrix (Fin n) (Fin ℓ) ℝ) : specNorm (nystrom A Ω) ≤ specNorm A :=
    ((posSemidef_nystrom hA Ω).specNorm_le_iff (specNorm_nonneg A)).mpr
      ((Matrix.le_iff.mpr (posSemidef_sub_nystrom hA Ω)).trans
        ((hA.specNorm_le_iff (specNorm_nonneg A)).mp le_rfl))
  have ha0 (Ω : Matrix (Fin n) (Fin ℓ) ℝ) : 0 ≤ nystromFloor A Ω := singularValues_nonneg _ _
  have haR (Ω : Matrix (Fin n) (Fin ℓ) ℝ) : nystromFloor A Ω ≤ specNorm A :=
    (singularValues_le_specNorm _ _).trans (hBN Ω)
  have hM := measurable_nystromPreconditionedMatrix A hB ha (posSemidef_nystrom hA)
    (specNorm_nonneg A) hBN ha0 haR hμ
  have hPSD (Ω : Matrix (Fin n) (Fin ℓ) ℝ) :=
    nystromPreconditionedMatrix_posDef (posSemidef_nystrom hA Ω)
      (Matrix.le_iff.mpr (posSemidef_sub_nystrom hA Ω)) (ha0 Ω) hμ
  have he : (fun Ω : Matrix (Fin n) (Fin ℓ) ℝ =>
      (conditionNumber (nystromPreconditionedMatrix A (nystrom A Ω) (nystromFloor A Ω) μ)).toReal) =
      fun Ω => specNorm (nystromPreconditionedMatrix A (nystrom A Ω) (nystromFloor A Ω) μ) *
        specNorm (nystromPreconditionedMatrix A (nystrom A Ω) (nystromFloor A Ω) μ)⁻¹ := by
    funext Ω
    exact conditionNumber_toReal_of_isUnit (hPSD Ω).isUnit
  rw [he]
  exact (measurable_specNorm_of_entries (Matrix.measurable_iff_entries.mp hM)).mul
    (measurable_specNorm_of_entries (Matrix.measurable_iff_entries.mp (measurable_matrix_inv.comp hM)))

open scoped Matrix.Norms.L2Operator in
/-- At an integer head cutoff at least `3 d_eff/2` and width `2k+1≤n`, the
actual FTU condition number is integrable and has expectation below 28. The
claim uses the original spectral-floor preconditioner, not a shifted surrogate.
atlas: nystrom-pcg (partial) -/
theorem integrable_and_integral_conditionNumber_nystromPreconditionedMatrix_lt_28
    {Ωs : Type*} [MeasurableSpace Ωs] {ν : Measure Ωs}
    {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ) (hk0 : 0 < k) (hwidth : k+(k+1) ≤ n)
    (hk : 3 * nystromEffectiveDimension A μ / 2 ≤ k)
    (Ω : Ωs → Matrix (Fin n) (Fin (k+(k+1))) ℝ)
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin (k+(k+1)))) ν) :
    Integrable (fun ω => (conditionNumber (nystromPreconditionedMatrix A
      (nystrom A (Ω ω)) (nystromFloor A (Ω ω)) μ)).toReal) ν ∧
      ∫ ω, (conditionNumber (nystromPreconditionedMatrix A
        (nystrom A (Ω ω)) (nystromFloor A (Ω ω)) μ)).toReal ∂ν < 28 := by
  let _ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have := hΩ.isProbabilityMeasure
  let f := fun ω => (conditionNumber (nystromPreconditionedMatrix A
    (nystrom A (Ω ω)) (nystromFloor A (Ω ω)) μ)).toReal
  obtain ⟨hEi, hEb⟩ := integrable_and_integral_specNorm_sub_nystrom_le_of_effectiveDimension
    hA hμ hk0 (by omega : k<n) hk Ω hΩ
  have hD : 0 ≤ nystromEffectiveDimension A μ := by
    unfold nystromEffectiveDimension effectiveDimensionOfSpectrum
    exact Finset.sum_nonneg fun i _ => div_nonneg (singularValues_nonneg A i)
      (add_nonneg (singularValues_nonneg A i) hμ.le)
  have hfloor (ω : Ωs) : nystromFloor A (Ω ω) ≤ μ := by
    change singularValues (nystrom A (Ω ω)) (k+(k+1)-1) ≤ μ
    let j : Fin n := ⟨k+(k+1)-1, by omega⟩
    apply (singularValues_nystrom_le hA (Ω ω) j).trans
    have h := apply_le_mul_of_effectiveDimensionOfSpectrum_le
      (fun i : Fin n => singularValues A i) (fun i => singularValues_nonneg A i)
      (fun i l hil => singularValues_antitone A hil) hμ (by norm_num : (0 : ℝ) < 1) j (by
        change (1 + 1 / (1 : ℝ)) * nystromEffectiveDimension A μ ≤ (j.val : ℝ) + 1
        have hj : j.val = 2*k := by dsimp [j]; omega
        rw [hj]
        push_cast
        linarith)
    simpa using h
  have hb (ω : Ωs) : f ω ≤ 2 + specNorm (A - nystrom A (Ω ω)) / μ := by
    have h := conditionNumber_nystromPreconditionedMatrix_toReal_le
      (a := nystromFloor A (Ω ω)) (posSemidef_nystrom hA (Ω ω))
      (Matrix.le_iff.mpr (posSemidef_sub_nystrom hA (Ω ω)))
      (singularValues_nonneg (nystrom A (Ω ω)) (k+(k+1)-1)) hμ
    apply h.trans
    rw [add_div]
    have h1 := (div_le_one hμ).mpr (hfloor ω)
    linarith
  have hm : AEStronglyMeasurable f ν :=
    ((measurable_conditionNumber_nystromPreconditionedMatrix hA hμ).comp_aemeasurable
      hΩ.aemeasurable).aestronglyMeasurable
  have hf0 (ω : Ωs) : 0 ≤ f ω := ENNReal.toReal_nonneg
  have hi : Integrable f ν := ((integrable_const 2).add (hEi.div_const μ)).mono' hm
    (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 ω), Pi.add_apply] using hb ω)
  refine ⟨hi, ?_⟩
  have hb' := integral_mono_ae hi ((integrable_const 2).add (hEi.div_const μ))
    (Filter.Eventually.of_forall hb)
  simp only [Pi.add_apply] at hb'
  rw [integral_add (integrable_const 2) (hEi.div_const μ), integral_const, integral_div,
    probReal_univ, one_smul] at hb'
  have hE := (div_le_iff₀ hμ).mpr hEb
  have he := Real.exp_one_lt_three
  have he0 := Real.exp_pos (1 : ℝ)
  nlinarith

end NLAlib
