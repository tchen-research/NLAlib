import NLAlib.Sketching.CountSketch

/-!
# Conditional CountSketch second moments

For each fixed hash assignment, the actual Rademacher sign law gives precisely
the two off-diagonal contractions. Averaging the uniform hash collisions then
produces the sharp full Gram-error second moment.
Source: operator manuscript `sh:count-second`; supports `sparse-ose`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped Matrix
namespace NLAlib

variable {ι ρ d : Type*} [Fintype ι] [Fintype ρ] [Fintype d]
variable [DecidableEq ι] [DecidableEq ρ] [DecidableEq d]

omit [Fintype d] in
/-- Under the actual sign law, every embedded CountSketch Gram-error entry
is the corresponding hollow sign quadratic form almost everywhere.
Source: manuscript `sh:count-hollow`; supports `sparse-ose`. -/
theorem ae_countSketch_gram_error_apply_eq_quadForm
    (h : ι → ρ) (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) (a b : d) :
    (fun σ : ι → ℝ =>
      (((countSketchMatrix h σ * U)ᵀ * (countSketchMatrix h σ * U) - 1) : Matrix d d ℝ) a b) =ᵐ[
      Measure.pi (fun _ => rademacherMeasure)]
        fun σ => quadForm (countSketchHollowCoefficient h U a b) σ := by
  have hsign : ∀ i : ι, ∀ᵐ σ : ι → ℝ ∂Measure.pi (fun _ => rademacherMeasure),
      σ i = 1 ∨ σ i = -1 := fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => rademacherMeasure) (i := i)).eventually
      ae_eq_one_or_neg_one_rademacherMeasure
  filter_upwards [Filter.eventually_all.2 hsign] with σ hσ
  rw [countSketch_gram_error_eq h σ U hU]
  apply mul_countSketchGram_sub_one_mul_apply_eq_quadForm
  intro i
  rcases hσ i with hi | hi <;> simp [hi]

omit [Fintype d] in
/-- Every squared CountSketch Gram-error entry is genuinely integrable
under the actual sign law for each fixed hash. Source: the hollow quadratic
form and absolute Rademacher moments; supports `sparse-ose`. -/
theorem integrable_countSketch_gram_error_apply_sq
    (h : ι → ρ) (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) (a b : d) :
    Integrable (fun σ : ι → ℝ =>
      (((countSketchMatrix h σ * U)ᵀ * (countSketchMatrix h σ * U) - 1) : Matrix d d ℝ) a b ^ 2)
      (Measure.pi fun _ => rademacherMeasure) := by
  apply (integrable_quadForm_sq_pi_rademacherMeasure (countSketchHollowCoefficient h U a b)).congr
  exact (ae_countSketch_gram_error_apply_eq_quadForm h U hU a b).symm.mono
    fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx

omit [Fintype d] in
/-- The exact entrywise conditional CountSketch second moment consists of
the two surviving off-diagonal sign contractions. Source: manuscript
`sh:count-second`; supports `sparse-ose`. -/
theorem integral_countSketch_gram_error_apply_sq
    (h : ι → ρ) (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) (a b : d) :
    (∫ σ : ι → ℝ,
      (((countSketchMatrix h σ * U)ᵀ * (countSketchMatrix h σ * U) - 1) : Matrix d d ℝ) a b ^ 2
        ∂Measure.pi (fun _ => rademacherMeasure)) =
      ∑ i, ∑ j, if i = j then 0 else if h i = h j then
        (U i a * U j b) ^ 2 + (U i a * U j b) * (U j a * U i b) else 0 := by
  rw [integral_congr_ae ((ae_countSketch_gram_error_apply_eq_quadForm h U hU a b).mono
    fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx)]
  rw [integral_quadForm_sq_pi_rademacherMeasure_of_diag_zero _
    (countSketchHollowCoefficient_diag h U a b)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst j
    simp [countSketchHollowCoefficient]
  · by_cases hh : h i = h j
    · simp only [countSketchHollowCoefficient, Matrix.of_apply,
        if_neg hij, if_neg (Ne.symm hij), if_pos hh, if_pos hh.symm]
    · simp only [countSketchHollowCoefficient, Matrix.of_apply,
        if_neg hij, if_neg (Ne.symm hij), if_neg hh, if_neg (Ne.symm hh),
        zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]

omit [Fintype d] in
/-- Every conditional CountSketch Gram-error entry has mean zero under its
actual sign law, for each fixed hash assignment. Source: manuscript
`sh:count-hollow`; supports `sparse-ose`. -/
theorem integral_countSketch_gram_error_apply_eq_zero
    (h : ι → ρ) (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) (a b : d) :
    (∫ σ : ι → ℝ,
      (((countSketchMatrix h σ * U)ᵀ * (countSketchMatrix h σ * U) - 1) : Matrix d d ℝ) a b
        ∂Measure.pi (fun _ => rademacherMeasure)) = 0 := by
  rw [integral_congr_ae (ae_countSketch_gram_error_apply_eq_quadForm h U hU a b),
    integral_quadForm_pi_rademacherMeasure]
  simp only [Matrix.trace, Matrix.diag, countSketchHollowCoefficient_diag, Finset.sum_const_zero]

/-- The actual sign law's conditional squared Frobenius Gram-error moment
is the finite sum of the exact entrywise contractions. Source: manuscript
`sh:count-second`; supports `sparse-ose`. -/
theorem integral_frobSq_countSketch_gram_error
    (h : ι → ρ) (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) :
    (∫ σ : ι → ℝ,
      frobSq ((countSketchMatrix h σ * U)ᵀ * (countSketchMatrix h σ * U) - 1)
        ∂Measure.pi (fun _ => rademacherMeasure)) =
      ∑ a, ∑ b, ∑ i, ∑ j, if i = j then 0 else if h i = h j then
        (U i a * U j b) ^ 2 + (U i a * U j b) * (U j a * U i b) else 0 := by
  simp only [frobSq, frobInner, ← pow_two]
  rw [integral_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun b _ => integrable_countSketch_gram_error_apply_sq h U hU a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => integrable_countSketch_gram_error_apply_sq h U hU a b]
  simp_rw [integral_countSketch_gram_error_apply_sq h U hU]

end NLAlib
