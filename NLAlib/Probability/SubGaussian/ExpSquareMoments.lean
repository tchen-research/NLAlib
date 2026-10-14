import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import NLAlib.Matrix.Norms.Core

/-!
# Even moments from a square-exponential bound

A finite nonnegative exponential-square integral gives all even moments
without a centering assumption. This direct estimate is useful for vector
factors whose coordinates may be dependent.
-/

noncomputable section

open MeasureTheory Matrix

namespace NLAlib

/-- A square-exponential bound gives finite even moments with the factorial
budget `2 p! K^(2p)`. The variable need not have mean zero. The nonnegative
integral hypothesis also proves integrability of each moment. -/
theorem integrable_and_integral_pow_two_mul_le_of_lintegral_exp_sq_le_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {K : ℝ} (hK : 0 < K)
    (hpsi : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / K) ^ 2)) ∂μ ≤ 2)
    (p : ℕ) :
    Integrable (fun ω => X ω ^ (2 * p)) μ ∧
      (∫ ω, X ω ^ (2 * p) ∂μ) ≤ 2 * (p.factorial : ℝ) * K ^ (2 * p) := by
  let F : Ω → ℝ := fun ω => Real.exp ((X ω / K) ^ 2)
  have hFnonneg : 0 ≤ᵐ[μ] F := ae_of_all _ fun _ => (Real.exp_pos _).le
  have hFi : Integrable F μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (hX.div_const K |>.pow_const 2 |>.exp |>.aestronglyMeasurable) hFnonneg).1
    exact ne_of_lt (hpsi.trans_lt (by norm_num))
  have hFb : (∫ ω, F ω ∂μ) ≤ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).1
    rw [ofReal_integral_eq_lintegral_ofReal hFi hFnonneg]
    simpa [F] using hpsi
  let C : ℝ := (p.factorial : ℝ) * K ^ (2 * p)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (ω : Ω) : X ω ^ (2 * p) ≤ C * F ω := by
    have ht := Real.pow_div_factorial_le_exp ((X ω / K) ^ 2) (sq_nonneg _) p
    have hfac : (0 : ℝ) < p.factorial := by exact_mod_cast p.factorial_pos
    have ht' := (div_le_iff₀ hfac).1 ht
    have hm := mul_le_mul_of_nonneg_left ht' (pow_nonneg hK.le (2 * p))
    have hid : K ^ (2 * p) * ((X ω / K) ^ 2) ^ p = X ω ^ (2 * p) := by
      rw [← pow_mul, div_pow]
      field_simp
    rw [hid] at hm
    simpa [C, F, mul_assoc, mul_left_comm, mul_comm] using hm
  have hi : Integrable (fun ω => X ω ^ (2 * p)) μ := by
    apply (hFi.const_mul C).mono_nonneg (hX.pow_const _).aestronglyMeasurable
    · exact ae_of_all _ fun _ => Even.pow_nonneg (even_two.mul_right p) _
    · exact ae_of_all _ hpoint
  refine ⟨hi, ?_⟩
  calc
    (∫ ω, X ω ^ (2 * p) ∂μ) ≤ ∫ ω, C * F ω ∂μ :=
      integral_mono hi (hFi.const_mul C) hpoint
    _ = C * ∫ ω, F ω ∂μ := integral_const_mul _ _
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hFb hC
    _ = 2 * (p.factorial : ℝ) * K ^ (2 * p) := by dsimp [C]; ring

/-- A directional square-exponential bound implies the homogeneous even
moment budget `2 p! K^(2p) ‖a‖^(2p)`, also for noncentered vector laws.
This is the unoptimized factorial form of Heidary, Lemma 2.2. -/
theorem integrable_and_integral_pow_two_mul_dotProduct_le_of_directional_exp_sq
    {α : Type*} [Fintype α] (ν : Measure (α → ℝ)) [IsProbabilityMeasure ν]
    {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ u : α → ℝ, ‖WithLp.toLp 2 u‖ = 1 →
      ∫⁻ g, ENNReal.ofReal (Real.exp ((u ⬝ᵥ g / K) ^ 2)) ∂ν ≤ 2)
    (p : ℕ) (a : α → ℝ) :
    Integrable (fun g => (a ⬝ᵥ g) ^ (2 * p)) ν ∧
      (∫ g, (a ⬝ᵥ g) ^ (2 * p) ∂ν) ≤
        2 * (p.factorial : ℝ) * K ^ (2 * p) * ‖WithLp.toLp 2 a‖ ^ (2 * p) := by
  classical
  let s : ℝ := ‖WithLp.toLp 2 a‖
  by_cases hs : s = 0
  · have ha : a = 0 := by
      apply WithLp.toLp_injective (p := 2)
      simpa only [WithLp.toLp_zero] using (norm_eq_zero.mp hs)
    subst a
    by_cases hp : p = 0
    · subst p
      simp
    · have hp' : 2 * p ≠ 0 := Nat.mul_ne_zero (by norm_num) hp
      simp [hp']
  have hspos : 0 < s := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs)
  let u : α → ℝ := s⁻¹ • a
  have hu : ‖WithLp.toLp 2 u‖ = 1 := by
    simp only [u, WithLp.toLp_smul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hspos.le)]
    change s⁻¹ * s = 1
    exact inv_mul_cancel₀ hs
  have h := integrable_and_integral_pow_two_mul_le_of_lintegral_exp_sq_le_two
    (X := fun g => u ⬝ᵥ g) (by fun_prop) hK (hpsi u hu) p
  have hpoint (g : α → ℝ) :
      (a ⬝ᵥ g) ^ (2 * p) = s ^ (2 * p) * (u ⬝ᵥ g) ^ (2 * p) := by
    simp only [u, smul_dotProduct, smul_eq_mul, mul_pow, inv_pow]
    field_simp
  refine ⟨?_, ?_⟩
  · simpa only [← hpoint] using h.1.const_mul (s ^ (2 * p))
  · calc
      (∫ g, (a ⬝ᵥ g) ^ (2 * p) ∂ν) =
          s ^ (2 * p) * ∫ g, (u ⬝ᵥ g) ^ (2 * p) ∂ν := by
            simp_rw [hpoint]
            rw [integral_const_mul]
      _ ≤ s ^ (2 * p) * (2 * (p.factorial : ℝ) * K ^ (2 * p)) :=
        mul_le_mul_of_nonneg_left h.2 (pow_nonneg hspos.le _)
      _ = _ := by dsimp [s]; ring

end NLAlib
