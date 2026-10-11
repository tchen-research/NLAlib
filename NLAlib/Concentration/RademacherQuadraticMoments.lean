import NLAlib.Concentration.QuadraticMoments
import NLAlib.Concentration.Scalar.RademacherSymmetry
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Quadratic moments of the actual finite Rademacher cube

The coordinate moments and independence needed by the general quadratic-form
identities are derived from the actual product law. These reusable lower-layer
endpoints support the CountSketch second-moment proof.
Source: Hutchinson 1989; operator manuscript `sh:count-second`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {κ : Type*} [Fintype κ]

/-- Coordinates of the actual product Rademacher measure have the required
absolute moments, mean zero and even moments one. Source: the two-sign
support; supports CountSketch `sparse-ose` and quadratic trace identities. -/
theorem rademacher_pi_coordinate_moments (i : κ) :
    MemLp (fun x : κ → ℝ => x i) 2 (Measure.pi fun _ => rademacherMeasure) ∧
    (∫ x : κ → ℝ, x i ∂Measure.pi (fun _ => rademacherMeasure)) = 0 ∧
    (∫ x : κ → ℝ, x i ^ 2 ∂Measure.pi (fun _ => rademacherMeasure)) = 1 ∧
    Integrable (fun x : κ → ℝ => x i ^ 4) (Measure.pi fun _ => rademacherMeasure) ∧
    (∫ x : κ → ℝ, x i ^ 4 ∂Measure.pi (fun _ => rademacherMeasure)) = 1 := by
  have hsign : ∀ᵐ x : κ → ℝ ∂Measure.pi (fun _ => rademacherMeasure),
      x i = 1 ∨ x i = -1 :=
    (Measure.tendsto_eval_ae_ae (μ := fun _ : κ => rademacherMeasure) (i := i)).eventually
      ae_eq_one_or_neg_one_rademacherMeasure
  have hnorm : ∀ᵐ x : κ → ℝ ∂Measure.pi (fun _ => rademacherMeasure), ‖x i‖ ≤ 1 :=
    hsign.mono fun x hx => by rcases hx with h | h <;> simp [h]
  have hsq : (fun x : κ → ℝ => x i ^ 2) =ᵐ[Measure.pi (fun _ => rademacherMeasure)]
      fun _ => (1 : ℝ) := hsign.mono fun x hx => by rcases hx with h | h <;> simp [h]
  have hfour : (fun x : κ → ℝ => x i ^ 4) =ᵐ[Measure.pi (fun _ => rademacherMeasure)]
      fun _ => (1 : ℝ) := hsign.mono fun x hx => by rcases hx with h | h <;> norm_num [h]
  refine ⟨MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable 1 hnorm, ?_, ?_, ?_, ?_⟩
  · rw [integral_eval]
    exact integral_id_rademacherMeasure
  · rw [integral_congr_ae hsq]
    simp
  · exact (integrable_const (1 : ℝ)).congr hfour.symm
  · rw [integral_congr_ae hfour]
    simp

/-- The exact second moment of an arbitrary quadratic form under the actual
product Rademacher law. Source: Hutchinson 1989 and the general fourth-moment
contraction; supports CountSketch `sparse-ose`. -/
theorem integral_quadForm_sq_pi_rademacherMeasure [DecidableEq κ]
    (A : Matrix κ κ ℝ) :
    (∫ x : κ → ℝ, quadForm A x ^ 2 ∂Measure.pi (fun _ => rademacherMeasure)) =
      A.trace ^ 2 + ∑ i, ∑ j, A i j ^ 2 + ∑ i, ∑ j, A i j * A j i -
        2 * ∑ i, A i i ^ 2 := by
  have h := integral_quadForm_sq A
    (fun i => (measurable_pi_apply i).aemeasurable)
    (iIndepFun_pi (fun _ : κ => aemeasurable_id))
    (fun i => (rademacher_pi_coordinate_moments i).2.1)
    (fun i => (rademacher_pi_coordinate_moments i).2.2.1)
    (fun i => (rademacher_pi_coordinate_moments i).2.2.2.1)
    (m₄ := 1) (fun i => (rademacher_pi_coordinate_moments i).2.2.2.2)
  convert h using 1
  ring

/-- The actual product Rademacher law is isotropic, so every quadratic form
has expectation equal to its trace. Source: Hutchinson 1989, obtained here
from the actual coordinate law. Relocated from `Estimation.HutchinsonLaws`
to make the existing endpoint available to CountSketch in the lower layer;
its public statement and import compatibility are preserved.
Supports `hutchinson-unbiased` and CountSketch `sparse-ose`. -/
theorem integral_quadForm_pi_rademacherMeasure
    (A : Matrix κ κ ℝ) :
    (∫ x : κ → ℝ, quadForm A x ∂Measure.pi (fun _ => rademacherMeasure)) = A.trace := by
  classical
  have hind : iIndepFun (fun i (x : κ → ℝ) => x i)
      (Measure.pi fun _ => rademacherMeasure) :=
    iIndepFun_pi (fun _ : κ => aemeasurable_id)
  exact integral_quadForm_eq_trace A
    (fun i => (rademacher_pi_coordinate_moments i).1)
    (fun _ _ hij => hind.indepFun hij)
    (fun i => (rademacher_pi_coordinate_moments i).2.1)
    (fun i => (rademacher_pi_coordinate_moments i).2.2.1)

/-- A zero-diagonal quadratic form has precisely the two off-diagonal
contractions as its Rademacher second moment. Source: manuscript
`sh:count-second`; supports the entrywise CountSketch Gram calculation. -/
theorem integral_quadForm_sq_pi_rademacherMeasure_of_diag_zero [DecidableEq κ]
    (A : Matrix κ κ ℝ) (hdiag : ∀ i, A i i = 0) :
    (∫ x : κ → ℝ, quadForm A x ^ 2 ∂Measure.pi (fun _ => rademacherMeasure)) =
      (∑ i, ∑ j, A i j ^ 2) + ∑ i, ∑ j, A i j * A j i := by
  rw [integral_quadForm_sq_pi_rademacherMeasure]
  simp only [Matrix.trace, Matrix.diag, hdiag, Finset.sum_const_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, mul_zero, sub_zero]

/-- An explicit quadratic-form growth bound in the finite coefficient
supremum norm. Source: the finite quadratic expansion; supports the absolute
integrability needed in CountSketch `sparse-ose`. -/
theorem abs_quadForm_le_sum_abs_mul_one_add_norm_sq
    (A : Matrix κ κ ℝ) (x : κ → ℝ) :
    |quadForm A x| ≤ (∑ i, ∑ j, |A i j|) * (1 + ‖x‖) ^ 2 := by
  rw [quadForm_eq_sum]
  simp only [← mul_assoc]
  calc _ ≤ ∑ i, ∑ j, |A i j * x i * x j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| * (1 + ‖x‖) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_mul, pow_two]
      have hi : |x i| ≤ 1 + ‖x‖ := by
        simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm x i).trans (by linarith : ‖x‖ ≤ 1 + ‖x‖)
      have hj : |x j| ≤ 1 + ‖x‖ := by
        simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm x j).trans (by linarith : ‖x‖ ≤ 1 + ‖x‖)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hi hj (abs_nonneg _) (by positivity)) (abs_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

/-- Squared quadratic forms are genuinely integrable under the actual
Rademacher product law. Source: explicit polynomial growth and bounded sign
support; supports the entrywise CountSketch second moment `sparse-ose`. -/
theorem integrable_quadForm_sq_pi_rademacherMeasure
    (A : Matrix κ κ ℝ) :
    Integrable (fun x : κ → ℝ => quadForm A x ^ 2)
      (Measure.pi fun _ => rademacherMeasure) := by
  apply integrable_pi_rademacherMeasure_of_polynomial_growth _
    (by simp only [quadForm_eq_sum]; fun_prop) ((∑ i, ∑ j, |A i j|) ^ 2) 4
  intro x
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have h := abs_quadForm_le_sum_abs_mul_one_add_norm_sq A x
  calc _ ≤ ((∑ i, ∑ j, |A i j|) * (1 + ‖x‖) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by rw [mul_pow, ← pow_mul]

end NLAlib
