/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.LowRank.RangeFinding.SpectralRangeFinder

/-!
# Squared Gaussian block moments for Nyström

The squared conditioned Chevet estimate and the native inverse-Wishart moment
control the Nyström spectral error. The block variables have their actual joint
Gaussian law. Source: Frangella–Tropp–Udell 2023, Theorem 5.1 proof;
Tropp–Webber 2023, Appendix B. The conditioning proof follows the native
`SpectralRangeFinder.lean` first-moment argument.
Atlas: `nystrom-pcg` (Gaussian residual kernel).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- A squared spectral pseudoinverse moment, including zero rows. This is the native
inverse-Wishart moment at exponent one transported by the Gram identity. -/
theorem integrable_and_integral_specNorm_sq_pinvR_gaussianMatrix_le {r t : ℕ}
    (hrt : r + 2 ≤ t) :
    Integrable (fun G : Matrix (Fin r) (Fin t) ℝ => specNorm (pinvR G) ^ 2)
      (gaussianMatrix (Fin r) (Fin t)) ∧
    ∫ G, specNorm (pinvR G) ^ 2 ∂gaussianMatrix (Fin r) (Fin t) ≤
      Real.exp 1 ^ 2 * ((t : ℝ) + r) / (2 * ((t : ℝ) - r) ^ 2) := by
  obtain ⟨hi, hv⟩ :=
    integrable_and_integral_specNorm_inv_self_mul_transpose_pow_gaussianMatrix_le
      (r := r) (k := t) (p := 1) (by omega) (by omega) (by omega)
  simp only [pow_one] at hi hv
  have he : (fun G : Matrix (Fin r) (Fin t) ℝ => specNorm (pinvR G) ^ 2)
      =ᵐ[gaussianMatrix (Fin r) (Fin t)] fun G => specNorm (G * Gᵀ)⁻¹ := by
    filter_upwards [gaussianMatrix_ae_isUnit_mul_transpose (show r ≤ t by omega)] with G hG
    exact specNorm_pinvR_sq G hG
  exact ⟨hi.congr he.symm, (integral_congr_ae he).trans_le hv⟩

/-- **Squared conditioned Chevet bound.** The orthogonal Gaussian blocks are independent.
The oversampling assumption is sufficient for both inverse moments; no positive-rank
assumption is required. -/
theorem integrable_and_integral_specNorm_sq_mul_block_mul_pinvR_block_le
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {n k p r r' : ℕ} (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin (k + p))) μ)
    {V₁ : Matrix (Fin n) (Fin k) ℝ} {V₂ : Matrix (Fin n) (Fin r') ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (S₂ : Matrix (Fin r) (Fin r') ℝ) (hp : 2 ≤ p) :
    Integrable (fun ω => specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ^ 2) μ ∧
    ∫ ω, specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ^ 2 ∂μ ≤
      2 * specNorm S₂ ^ 2 * (k / ((p : ℝ) - 1)) +
        frobSq S₂ * (Real.exp 1 ^ 2 * (2 * k + p) / p ^ 2) := by
  set X : Ωs → Matrix (Fin k) (Fin (k + p)) ℝ := fun ω => V₁ᵀ * Ω ω with hXdef
  set Y : Ωs → Matrix (Fin r') (Fin (k + p)) ℝ := fun ω => V₂ᵀ * Ω ω with hYdef
  have hXlaw : HasLaw X (gaussianMatrix (Fin k) (Fin (k + p))) μ :=
    hasLaw_gaussianMatrix_block_of_hasLaw hΩ V₁ hV₁
  have hYlaw : HasLaw Y (gaussianMatrix (Fin r') (Fin (k + p))) μ :=
    hasLaw_gaussianMatrix_block_of_hasLaw hΩ V₂ hV₂
  have hind : IndepFun X Y μ := gaussianMatrix_indepFun_block_of_hasLaw hΩ V₁ V₂ hV₁ hV₂ hV
  have hXm := hXlaw.aemeasurable
  have hYm := hYlaw.aemeasurable
  set g : Matrix (Fin k) (Fin (k + p)) ℝ → Matrix (Fin r') (Fin (k + p)) ℝ → ℝ :=
    fun x y => specNorm (S₂ * y * pinvR x) ^ 2 with hgdef
  have hfg : (fun ω => specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ^ 2) =
      fun ω => g (X ω) (Y ω) := rfl
  have hgm : Measurable fun q : Matrix (Fin k) (Fin (k + p)) ℝ × Matrix (Fin r') (Fin (k + p)) ℝ =>
      g q.1 q.2 :=
    (measurable_specNorm_of_entries (Matrix.measurable_iff_entries.mp
      ((measurable_const.matrix_mul measurable_snd).matrix_mul
        ((Matrix.measurable_iff_entries.mpr measurable_pinvR_entry).comp measurable_fst)))).pow_const 2
  -- The deterministic bound after integrating out `Ω₂`.
  set B : (Matrix (Fin k) (Fin (k + p)) ℝ) → ℝ := fun x =>
    2 * specNorm S₂ ^ 2 * frobSq (pinvR x) + 2 * frobSq S₂ * specNorm (pinvR x) ^ 2
    with hBdef
  obtain ⟨hFi, hFv⟩ := integrable_and_integral_frobSq_pinvR_gaussianMatrix (r := k) (k := k + p) (by omega)
  obtain ⟨hSi, hSv⟩ := integrable_and_integral_specNorm_sq_pinvR_gaussianMatrix_le
    (r := k) (t := k + p) (by omega)
  have hBi : Integrable B (gaussianMatrix (Fin k) (Fin (k + p))) :=
    (hFi.const_mul _).add (hSi.const_mul _)
  have hS0 := frobSq_nonneg S₂
  have hB0 : ∀ x, 0 ≤ B x := fun x =>
    by
      have hx0 := frobSq_nonneg (pinvR x)
      dsimp [B]
      positivity
  set bound := 2 * specNorm S₂ ^ 2 * (k / ((p : ℝ) - 1)) +
    frobSq S₂ * (Real.exp 1 ^ 2 * (2 * k + p) / p ^ 2) with hbound
  have hbound0 : 0 ≤ bound :=
    by
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
      have hp1 : 0 ≤ (p : ℝ) - 1 := by linarith
      dsimp [bound]
      positivity
  have hBint : ∫ x, B x ∂(gaussianMatrix (Fin k) (Fin (k + p))) ≤ bound := by
    rw [hBdef, integral_add (hFi.const_mul _) (hSi.const_mul _), integral_const_mul,
      integral_const_mul]
    push_cast at hFv hSv
    have heq : (↑k + ↑p - ↑k - 1 : ℝ) = p - 1 := by ring
    rw [heq] at hFv
    rw [hFv]
    have hh := mul_le_mul_of_nonneg_left hSv (show 0 ≤ 2 * frobSq S₂ by positivity)
    have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    calc
      _ ≤ 2 * specNorm S₂ ^ 2 * (k / ((p : ℝ) - 1)) +
          2 * frobSq S₂ * (Real.exp 1 ^ 2 * (k + p + k) / (2 * (k + p - k) ^ 2)) :=
        add_le_add le_rfl hh
      _ = bound := by
        dsimp [bound]
        rw [show ((k : ℝ) + p - k) = p by ring]
        congr 1
        field_simp [ne_of_gt hpR]
        ring
  have hL : ∫⁻ ω, ENNReal.ofReal (g (X ω) (Y ω)) ∂μ ≤ ENNReal.ofReal bound := by
    rw [lintegral_of_indepFun hXm hYm hind (g := fun x y => ENNReal.ofReal (g x y))
      (ENNReal.measurable_ofReal.comp hgm).aemeasurable, hXlaw.map_eq, hYlaw.map_eq]
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y) ∂gaussianMatrix (Fin r') (Fin (k + p))
          ∂gaussianMatrix (Fin k) (Fin (k + p))
        ≤ ∫⁻ x, ENNReal.ofReal (B x) ∂gaussianMatrix (Fin k) (Fin (k + p)) := by
          refine lintegral_mono fun x => ?_
          obtain ⟨hci, hcv⟩ :=
            integrable_and_integral_specNorm_sq_mul_gaussianMatrix_mul_le S₂ (pinvR x)
          rw [← ofReal_integral_eq_lintegral_ofReal hci (ae_of_all _ fun _ => sq_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          apply hcv.trans
          dsimp [B]
          have h1 := frobNorm_sq (pinvR x)
          have h2 := frobNorm_sq S₂
          nlinarith [sq_nonneg (specNorm S₂ * frobNorm (pinvR x) -
            frobNorm S₂ * specNorm (pinvR x))]
      _ = ENNReal.ofReal (∫ x, B x ∂gaussianMatrix (Fin k) (Fin (k + p))) :=
          (ofReal_integral_eq_lintegral_ofReal hBi (ae_of_all _ hB0)).symm
      _ ≤ ENNReal.ofReal bound := ENNReal.ofReal_le_ofReal hBint
  have hf0 : 0 ≤ᵐ[μ] fun ω => g (X ω) (Y ω) := ae_of_all _ fun _ => sq_nonneg _
  have hfm : AEStronglyMeasurable (fun ω => g (X ω) (Y ω)) μ :=
    (hgm.comp_aemeasurable (hXm.prodMk hYm)).aestronglyMeasurable
  have hfi : Integrable (fun ω => g (X ω) (Y ω)) μ :=
    ⟨hfm, (hasFiniteIntegral_iff_ofReal hf0).2 (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  rw [hfg]
  refine ⟨hfi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hfm]
  exact ENNReal.toReal_le_of_le_ofReal hbound0 hL

end NLAlib
