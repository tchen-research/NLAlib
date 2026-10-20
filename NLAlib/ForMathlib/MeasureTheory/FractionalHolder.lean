import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A fractional-power Hölder endpoint

The observable needs only a first moment; its fractional power lies in the
conjugate Lebesgue space. This is the scalar expectation endpoint used after
the pointwise trace-word bound for independent-sum spectrum universality.
The estimate holds on an arbitrary measure space.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A nonnegative first-moment observable pairs with an `Lˢ` mass by Hölder,
with fractional exponent `(s - 1) / s`. Both integrability of the product
and its expectation bound follow from the two supplied moments. No
independence or probability normalization is needed. -/
theorem integrable_and_integral_mul_rpow_le_lpNorm
    {M U : Ω → ℝ} {s : ℝ} (hs : 1 < s)
    (hM : MemLp M (ENNReal.ofReal s) μ) (hU : Integrable U μ)
    (hMnn : ∀ᵐ ω ∂μ, 0 ≤ M ω) (hUnn : ∀ᵐ ω ∂μ, 0 ≤ U ω) :
    Integrable (fun ω => M ω * U ω ^ ((s - 1) / s)) μ ∧
      (∫ ω, M ω * U ω ^ ((s - 1) / s) ∂μ) ≤
        lpNorm M (ENNReal.ofReal s) μ * (∫ ω, U ω ∂μ) ^ ((s - 1) / s) := by
  let t : ℝ := s / (s - 1)
  let a : ℝ := (s - 1) / s
  let V : Ω → ℝ := fun ω => U ω ^ a
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hsm1 : 0 < s - 1 := sub_pos.mpr hs
  have ht : 0 < t := div_pos hs0 hsm1
  have hat : a * t = 1 := by
    dsimp [a, t]
    field_simp [hs0.ne', hsm1.ne']
  have hit : 1 / t = a := by
    dsimp [a, t]
    field_simp [hs0.ne', hsm1.ne']
  have hst : s.HolderConjugate t :=
    (Real.holderConjugate_iff_eq_conjExponent hs).mpr rfl
  have hVmeas : AEStronglyMeasurable V μ :=
    (hU.aemeasurable.pow_const a).aestronglyMeasurable
  have hVnn : ∀ᵐ ω ∂μ, 0 ≤ V ω := by
    filter_upwards [hUnn] with ω hω
    exact Real.rpow_nonneg hω a
  have hVpow : (fun ω => V ω ^ t) =ᵐ[μ] U := by
    filter_upwards [hUnn] with ω hω
    dsimp [V]
    rw [← Real.rpow_mul hω, hat, Real.rpow_one]
  have hV : MemLp V (ENNReal.ofReal t) μ := by
    apply (integrable_norm_rpow_iff hVmeas (by simp [ht]) (by simp)).mp
    refine hU.congr ?_
    filter_upwards [hVnn, hVpow] with ω hω hpow
    rw [ENNReal.toReal_ofReal ht.le, Real.norm_of_nonneg hω, hpow]
  have : ENNReal.HolderTriple (ENNReal.ofReal s) (ENNReal.ofReal t) 1 :=
    hst.ennrealOfReal
  have hProd : Integrable (fun ω => M ω * V ω) μ := hM.integrable_mul hV
  have hMnorm : lpNorm M (ENNReal.ofReal s) μ =
      (∫ ω, M ω ^ s ∂μ) ^ (1 / s) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by simp [hs0]) (by simp) hM.1,
      ENNReal.toReal_ofReal hs0.le]
    simp only [one_div]
    congr 1
    exact integral_congr_ae (hMnn.mono fun ω hω => by
      change ‖M ω‖ ^ s = M ω ^ s
      rw [Real.norm_of_nonneg hω])
  have hBound := integral_mul_le_Lp_mul_Lq_of_nonneg hst hMnn hVnn hM hV
  rw [integral_congr_ae hVpow, ← hMnorm, hit] at hBound
  exact ⟨hProd, hBound⟩

/-- The Hölder endpoint at the even integer moment `2p`, including `p = 1`.
Only the square mass needs an even higher moment; the other observable
needs its ordinary expectation. -/
theorem integrable_and_integral_mul_rpow_le_lpNorm_two_mul
    {M U : Ω → ℝ} (p : ℕ) (hp : 0 < p)
    (hM : MemLp M (2 * (p : ℝ≥0∞)) μ) (hU : Integrable U μ)
    (hMnn : ∀ᵐ ω ∂μ, 0 ≤ M ω) (hUnn : ∀ᵐ ω ∂μ, 0 ≤ U ω) :
    Integrable (fun ω => M ω * U ω ^ ((2 * (p : ℝ) - 1) / (2 * p))) μ ∧
      (∫ ω, M ω * U ω ^ ((2 * (p : ℝ) - 1) / (2 * p)) ∂μ) ≤
        lpNorm M (2 * (p : ℝ≥0∞)) μ *
          (∫ ω, U ω ∂μ) ^ ((2 * (p : ℝ) - 1) / (2 * p)) := by
  have hp1 : (1 : ℝ) ≤ p := by
    exact_mod_cast (Nat.succ_le_iff.mpr hp : 1 ≤ p)
  have hcast : ENNReal.ofReal (2 * (p : ℝ)) = 2 * (p : ℝ≥0∞) := by
    simp [ENNReal.ofReal_mul]
  simpa only [hcast] using
    (integrable_and_integral_mul_rpow_le_lpNorm (by linarith : 1 < 2 * (p : ℝ))
      (hcast.symm ▸ hM) hU hMnn hUnn)

end MeasureTheory
