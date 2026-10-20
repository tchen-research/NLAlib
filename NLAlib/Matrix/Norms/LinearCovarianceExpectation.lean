import NLAlib.Matrix.Norms.Core
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Actual matrix covariance products from entrywise second moments -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLAlib
variable {Ω d : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- A genuine continuous linear covariance map applied to a random matrix
has its Bochner product bounded by the actual finite entrywise second
moments. No positivity or independence is assumed. -/
theorem specNorm_integral_linearMap_mul_le_card_sq_mul_entry_second_moment
    (S : Matrix d d ℂ →L[ℂ] Matrix d d ℂ)
    (D : Ω → Matrix d d ℂ) (hD : AEStronglyMeasurable D μ)
    (hDi : ∀ a b, Integrable (fun x => ‖D x a b‖^2) μ)
    (V : ℝ) (hV : ∀ a b, (∫ x, ‖D x a b‖^2 ∂μ)≤V) :
    specNorm (∫ x, S (D x)*D x ∂μ)≤(Fintype.card d : ℝ)^2*‖S‖*V := by
  have hFi : Integrable (fun x => frobSq (D x)) μ := by
    simp_rw [frobSq_eq_sum_norm_sq]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hDi a b
  have hb (x : Ω) : ‖S (D x)*D x‖≤‖S‖*frobSq (D x) := by
    calc
      _ ≤ ‖S (D x)‖*‖D x‖ := norm_mul_le _ _
      _ ≤ (‖S‖*‖D x‖)*‖D x‖ := mul_le_mul_of_nonneg_right (S.le_opNorm _) (norm_nonneg _)
      _ = ‖S‖*‖D x‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (specNorm_sq_le_frobSq (D x)) (norm_nonneg _)
  have hi : Integrable (fun x => S (D x)*D x) μ :=
    (hFi.const_mul ‖S‖).mono'
      ((S.continuous.comp_aestronglyMeasurable hD).mul hD) (Filter.Eventually.of_forall hb)
  calc
    _ ≤ ∫ x, ‖S (D x)*D x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖S‖*frobSq (D x) ∂μ := integral_mono hi.norm (hFi.const_mul _) hb
    _ = ‖S‖*∑ a, ∑ b, ∫ x, ‖D x a b‖^2 ∂μ := by
      rw [integral_const_mul]
      congr 1
      simp_rw [frobSq_eq_sum_norm_sq]
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hDi a b]
      apply Finset.sum_congr rfl
      intro a _
      exact integral_finsetSum _ fun b _ => hDi a b
    _ ≤ ‖S‖*∑ _a : d, ∑ _b : d, V := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hV a b
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end NLAlib
