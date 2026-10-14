import NLAlib.Probability.Moments.FiniteWeighted
import NLAlib.Matrix.Norms.Core

/-!
# Lifting directional moments to Euclidean moments

A homogeneous scalar even-moment budget also controls every finite
linear image in terms of its Frobenius norm. Finite Jensen retains the
coefficient norm without an output-dimension factor.
-/

noncomputable section

open MeasureTheory Matrix

namespace NLAlib

/-- A homogeneous directional even-moment bound controls every linear image
by its Frobenius norm, with the same constant. No coordinate independence
is needed. -/
theorem integrable_and_integral_norm_mulVec_pow_two_mul_le
    {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α] [Fintype β]
    {μ : Measure Ω} (z : Ω → α → ℝ) (hz : AEMeasurable z μ)
    {p : ℕ} (hp : 0 < p) {C : ℝ} (hC : 0 ≤ C)
    (hmoment : ∀ a : α → ℝ,
      Integrable (fun ω => (a ⬝ᵥ z ω) ^ (2 * p)) μ ∧
        (∫ ω, (a ⬝ᵥ z ω) ^ (2 * p) ∂μ) ≤ C * ‖WithLp.toLp 2 a‖ ^ (2 * p))
    (T : Matrix β α ℝ) :
    Integrable (fun ω => ‖WithLp.toLp 2 (T *ᵥ z ω)‖ ^ (2 * p)) μ ∧
      (∫ ω, ‖WithLp.toLp 2 (T *ᵥ z ω)‖ ^ (2 * p) ∂μ) ≤ C * frobSq T ^ p := by
  classical
  let c : β → ℝ := fun i => ‖WithLp.toLp 2 (T i)‖
  let u : β → α → ℝ := fun i => (c i)⁻¹ • T i
  let X : β → Ω → ℝ := fun i ω => u i ⬝ᵥ z ω
  have hu (i : β) : ‖WithLp.toLp 2 (u i)‖ ≤ 1 := by
    by_cases hci : c i = 0
    · simp [u, hci]
    · have hc : 0 ≤ c i := norm_nonneg _
      simp only [u, WithLp.toLp_smul, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc)]
      change (c i)⁻¹ * c i ≤ 1
      rw [inv_mul_cancel₀ hci]
  have hXi (i : β) : Integrable (fun ω => X i ω ^ (2 * p)) μ := (hmoment (u i)).1
  have hXm (i : β) : (∫ ω, X i ω ^ (2 * p) ∂μ) ≤ C := by
    apply (hmoment (u i)).2.trans
    exact mul_le_of_le_one_right hC (pow_le_one₀ (norm_nonneg _) (hu i))
  have h := integrable_and_integral_sum_mul_sq_pow_le c X
    (fun i => by dsimp [X]; fun_prop) hp hXi hXm
  have hentry (i : β) (ω : Ω) : c i * X i ω = T i ⬝ᵥ z ω := by
    by_cases hci : c i = 0
    · have hT : T i = 0 := by
        apply WithLp.toLp_injective (p := 2)
        simpa only [WithLp.toLp_zero] using (norm_eq_zero.mp hci)
      simp [hT, hci]
    · simp [X, u, smul_dotProduct, smul_eq_mul, hci]
  have hpoint (ω : Ω) : ‖WithLp.toLp 2 (T *ᵥ z ω)‖ ^ (2 * p) =
      (∑ i, (c i * X i ω) ^ 2) ^ p := by
    rw [pow_mul, norm_toLp_sq_eq_dotProduct_self]
    simp only [dotProduct, mulVec, dotProduct, ← pow_two, hentry]
  have hcoeff : (∑ i, c i ^ 2) = frobSq T := by
    simp only [c, norm_toLp_sq_eq_dotProduct_self, dotProduct, ← pow_two,
      frobSq_eq_sum_sq]
  simpa only [← hpoint, hcoeff] using h

end NLAlib
