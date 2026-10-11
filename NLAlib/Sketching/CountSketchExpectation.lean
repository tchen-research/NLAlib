import NLAlib.Sketching.CountSketchMoments
import NLAlib.ForMathlib.Probability.UniformCollision
import NLAlib.Matrix.FrameFourthContractions
import NLAlib.Sketching.Leverage
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact CountSketch Gram-error expectation

The actual independent uniform hashes and Rademacher signs give the two
off-diagonal contractions with collision factor `1/m`.
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
variable [MeasurableSpace ρ] [MeasurableSingletonClass ρ] [Nonempty ρ]

omit [DecidableEq ι] [Nonempty ρ] in
/-- The actual CountSketch squared Frobenius Gram error is measurable.
Source: finite discrete hashes and polynomial sign entries; supports
`sparse-ose`. -/
theorem measurable_frobSq_countSketch_gram_error (U : Matrix ι d ℝ) :
    Measurable (fun z : (ι → ρ) × (ι → ℝ) =>
      frobSq ((countSketchMatrix z.1 z.2 * U)ᵀ * (countSketchMatrix z.1 z.2 * U) - 1)) := by
  apply measurable_from_prod_countable_right
  intro h
  have hentry (i : ι) (r : ρ) (y : ι → ℝ) :
      (if h i = r then y i else 0) = (if h i = r then (1 : ℝ) else 0) * y i := by
    split_ifs <;> simp
  simp only [frobSq, frobInner, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, countSketchMatrix, Matrix.of_apply]
  simp_rw [hentry]
  fun_prop

/-- All CountSketch squared Gram-error moments are genuine integrals under
the actual product sampling law. Source: polynomial Rademacher moments and
finite hash space; supports `sparse-ose`. -/
theorem integrable_frobSq_countSketch_gram_error
    (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) :
    Integrable (fun z : (ι → ρ) × (ι → ℝ) =>
      frobSq ((countSketchMatrix z.1 z.2 * U)ᵀ * (countSketchMatrix z.1 z.2 * U) - 1))
      (countSketchLaw (ι := ι) (ρ := ρ)) := by
  unfold countSketchLaw
  apply (integrable_prod_iff (measurable_frobSq_countSketch_gram_error U).aestronglyMeasurable).2
  refine ⟨ae_of_all _ (fun h => ?_), Integrable.of_finite⟩
  simp only [frobSq, frobInner, ← pow_two]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    integrable_countSketch_gram_error_apply_sq h U hU a b

/-- Averaging the actual uniform hash law supplies the exact reciprocal-row
collision factor in the conditional sign moment. Source: manuscript
`sh:count-second`; supports `sparse-ose`. -/
theorem integral_frobSq_countSketch_gram_error_eq_scaled_contractions
    (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) :
    (∫ z : (ι → ρ) × (ι → ℝ),
      frobSq ((countSketchMatrix z.1 z.2 * U)ᵀ * (countSketchMatrix z.1 z.2 * U) - 1)
        ∂countSketchLaw) =
      (Fintype.card ρ : ℝ)⁻¹ *
        ∑ a, ∑ b, ∑ i, ∑ j, if i = j then 0 else
          (U i a * U j b) ^ 2 + (U i a * U j b) * (U j a * U i b) := by
  rw [countSketchLaw, integral_prod _ (integrable_frobSq_countSketch_gram_error U hU)]
  simp_rw [integral_frobSq_countSketch_gram_error _ U hU]
  rw [integral_finsetSum _ fun _ _ => Integrable.of_finite]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun _ _ => Integrable.of_finite]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum _ fun _ _ => Integrable.of_finite]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun _ _ => Integrable.of_finite]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · simp only [hij, if_true, integral_zero, mul_zero]
  · simp only [hij, if_false]
    have he (h : ι → ρ) : (if h i = h j then
        (U i a * U j b) ^ 2 + (U i a * U j b) * (U j a * U i b) else 0) =
      (if h i = h j then (1 : ℝ) else 0) *
        ((U i a * U j b) ^ 2 + (U i a * U j b) * (U j a * U i b)) := by
      split_ifs <;> simp
    simp_rw [he, integral_mul_const,
      integral_ite_coordinate_eq_coordinate_pi_uniformOfFintype i j hij]

/-- **Exact CountSketch second moment.** Under the actual independent uniform
hash and Rademacher sign law, the squared Frobenius Gram error equals
`(d²+d−2∑ leverage²)/m`. Source: manuscript `sh:count-second`.
atlas: sparse-ose (partial) -/
theorem integral_frobSq_countSketch_gram_error_eq
    (U : Matrix ι d ℝ) (hU : HasOrthonormalCols U) :
    (∫ z : (ι → ρ) × (ι → ℝ),
      frobSq ((countSketchMatrix z.1 z.2 * U)ᵀ * (countSketchMatrix z.1 z.2 * U) - 1)
        ∂countSketchLaw) =
      ((Fintype.card d : ℝ) ^ 2 + Fintype.card d -
        2 * ∑ i, leverageScore U i ^ 2) / Fintype.card ρ := by
  rw [integral_frobSq_countSketch_gram_error_eq_scaled_contractions U hU,
    sum_offDiagonal_frame_contractions_eq U hU]
  simp_rw [leverageScore_eq_sum_sq_of_self hU]
  rw [div_eq_mul_inv, mul_comm]

end NLAlib
