import NLAlib.Probability.Concentration.QuadraticForms.QuadraticMoments
import NLAlib.Probability.Rademacher.RademacherSymmetry

/-!
# Quadratic moments of the Rademacher vector

Second moments and integrability of quadratic forms `quadForm A x` under the Rademacher vector
law `rademacherVector κ`, from the coordinate moments of `Probability/Rademacher/Core` and the
general quadratic-form identities of `QuadraticMoments`. Used by the CountSketch second-moment
proof (`sparse-ose`). Hutchinson 1989; Avron–Toledo 2011, Lemma 6.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {κ : Type*} [Fintype κ]

/-- The second moment of a quadratic form under the Rademacher vector law:
`𝔼 (xᵀ A x)² = (tr A)² + ∑ Aᵢⱼ² + ∑ Aᵢⱼ Aⱼᵢ − 2 ∑ Aᵢᵢ²`. Hutchinson 1989; Avron–Toledo 2011,
Lemma 6. -/
theorem integral_quadForm_sq_rademacherVector [DecidableEq κ]
    (A : Matrix κ κ ℝ) :
    (∫ x : κ → ℝ, quadForm A x ^ 2 ∂(rademacherVector κ)) =
      A.trace ^ 2 + ∑ i, ∑ j, A i j ^ 2 + ∑ i, ∑ j, A i j * A j i -
        2 * ∑ i, A i i ^ 2 := by
  have h := integral_quadForm_sq A
    (fun i => (measurable_pi_apply i).aemeasurable)
    (iIndepFun_eval_rademacherVector κ)
    (fun i => integral_eq_zero_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i))
    (fun i => integral_sq_eq_one_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i))
    (fun i => integrable_pow_four_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i))
    (m₄ := 1)
    (fun i => integral_pow_four_eq_one_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i))
  convert h using 1
  ring

/-- The Rademacher vector law is isotropic, so every quadratic form has expectation equal to
its trace: `𝔼 (xᵀ A x) = tr A`. Hutchinson 1989 (atlas `hutchinson-unbiased`). -/
theorem integral_quadForm_rademacherVector
    (A : Matrix κ κ ℝ) :
    (∫ x : κ → ℝ, quadForm A x ∂(rademacherVector κ)) = A.trace := by
  classical
  have hind : iIndepFun (fun i (x : κ → ℝ) => x i)
      (rademacherVector κ) :=
    iIndepFun_pi (fun _ : κ => aemeasurable_id)
  exact integral_quadForm_eq_trace A
    (fun i => memLp_two_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i))
    (fun _ _ hij => hind.indepFun hij)
    (fun i => integral_eq_zero_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i))
    (fun i => integral_sq_eq_one_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i))

/-- A zero-diagonal quadratic form has the two off-diagonal contractions as its Rademacher
second moment: `𝔼 (xᵀ A x)² = ∑ Aᵢⱼ² + ∑ Aᵢⱼ Aⱼᵢ`. Hutchinson 1989. -/
theorem integral_quadForm_sq_rademacherVector_of_diag_zero [DecidableEq κ]
    (A : Matrix κ κ ℝ) (hdiag : ∀ i, A i i = 0) :
    (∫ x : κ → ℝ, quadForm A x ^ 2 ∂(rademacherVector κ)) =
      (∑ i, ∑ j, A i j ^ 2) + ∑ i, ∑ j, A i j * A j i := by
  rw [integral_quadForm_sq_rademacherVector]
  simp only [Matrix.trace, Matrix.diag, hdiag, Finset.sum_const_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, mul_zero, sub_zero]

/-- Polynomial growth of a quadratic form in the sup norm of its argument:
`|xᵀ A x| ≤ (∑ |Aᵢⱼ|) (1 + ‖x‖)²`. -/
theorem abs_quadForm_le_sum_abs_mul_one_add_norm_sq
    (A : Matrix κ κ ℝ) (x : κ → ℝ) :
    |quadForm A x| ≤ (∑ i, ∑ j, |A i j|) * (1 + ‖x‖) ^ 2 := by
  rw [quadForm_eq_sum]
  simp only [← mul_assoc, star_trivial]
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

/-- Squared quadratic forms are integrable under the Rademacher vector law (polynomial growth
and bounded support). -/
theorem integrable_quadForm_sq_rademacherVector
    (A : Matrix κ κ ℝ) :
    Integrable (fun x : κ → ℝ => quadForm A x ^ 2)
      (rademacherVector κ) := by
  apply integrable_rademacherVector_of_polynomial_growth _
    (by simp only [quadForm_eq_sum, star_trivial]; fun_prop) ((∑ i, ∑ j, |A i j|) ^ 2) 4
  intro x
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have h := abs_quadForm_le_sum_abs_mul_one_add_norm_sq A x
  calc _ ≤ ((∑ i, ∑ j, |A i j|) * (1 + ‖x‖) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by rw [mul_pow, ← pow_mul]

end NLAlib
