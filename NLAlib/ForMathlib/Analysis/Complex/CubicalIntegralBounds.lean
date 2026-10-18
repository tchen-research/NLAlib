import NLAlib.ForMathlib.Analysis.Complex.CubicalCauchy
import NLAlib.ForMathlib.MeasureTheory.CurveIntegralBounds

/-! # Length bounds for actual finite smooth contour cycles

Each signed smooth edge contributes its coefficient's absolute value times
the integral of its actual speed. Triangle inequalities give the usual
length times uniform-norm bound, with exact `1/(2 pi)` normalization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset MeasureTheory
open scoped unitInterval
namespace Complex

/-- The total parameter-speed length of a finite signed smooth one-chain,
counting the absolute value of each integer multiplicity. -/
def cubicalLength {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) : ℝ :=
  Γ.sum (fun γ n => |(n : ℝ)| *
    ∫ t in (0 : ℝ)..1, ‖derivWithin (cubicalPath γ).extend I t‖)

/-- A finite signed smooth cycle has nonnegative actual total length. -/
theorem cubicalLength_nonneg {Ω : Set ℂ} (Γ : Cubical.OneChain Ω) : 0 ≤ cubicalLength Γ := by
  apply sum_nonneg
  intro γ _
  exact mul_nonneg (abs_nonneg _) (intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun _ => norm_nonneg _))

/-- A uniform scalar bound along the actual contour controls its native
integral by its actual total speed length. -/
theorem norm_cubicalCurveIntegral_le_length_mul {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) (g : ℂ → ℂ) {C : ℝ}
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hg : ∀ γ ∈ Γ.support, ∀ r, ‖g (γ r : ℂ)‖ ≤ C) :
    ‖cubicalCurveIntegral g Γ‖ ≤ cubicalLength Γ * C := by
  unfold cubicalCurveIntegral cubicalLength
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  apply (norm_sum_le _ _).trans
  rw [sum_mul]
  apply sum_le_sum
  intro γ hγ
  rw [norm_zsmul ℝ, Real.norm_eq_abs]
  have h := norm_curveIntegral_le_mul_integral_norm_derivWithin_of_contDiffOn
    (fun z => g z • ContinuousLinearMap.id ℂ ℂ) (cubicalPath γ)
    (C := C) (fun t ht => by
      rw [(cubicalPath γ).extend_apply ht]
      simp only [norm_smul, ContinuousLinearMap.norm_id, mul_one]
      change ‖g (γ ⟨t, ht⟩ : ℂ)‖ ≤ C
      exact hg γ hγ ⟨t, ht⟩) (hΓ γ hγ)
  calc
    _ ≤ |(Γ γ : ℝ)| * (C * ∫ t in (0 : ℝ)..1,
        ‖derivWithin (cubicalPath γ).extend I t‖) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

/-- The actual normalized integral over a finite signed smooth contour has
the standard total-length bound, without a Cauchy or homology hypothesis. -/
theorem norm_two_pi_i_inv_mul_cubicalCurveIntegral_le_length_mul {Ω : Set ℂ}
    (Γ : Cubical.OneChain Ω) (g : ℂ → ℂ) {C : ℝ}
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hg : ∀ γ ∈ Γ.support, ∀ r, ‖g (γ r : ℂ)‖ ≤ C) :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ * cubicalCurveIntegral g Γ‖ ≤
      cubicalLength Γ / (2 * Real.pi) * C := by
  rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_I, mul_one,
    norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num only [norm_ofNat]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (cubicalLength Γ * C) :=
      mul_le_mul_of_nonneg_left (norm_cubicalCurveIntegral_le_length_mul Γ g hΓ hg)
        (inv_nonneg.mpr (by positivity))
    _ = _ := by ring

end Complex
