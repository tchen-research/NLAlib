import NLAlib.LowRank.GaussianSketch

/-!
# Rank-sensitive generalized Nyström error

This module retains the exact Gaussian completion factor q/(s-q-1),
requires only s ≥ q+2 for the second sketch, and proves integrability
of the actual squared error. Atlas: `gn-expected-error`.
The orthonormal frame is supplied as a measurable function of the first sketch.
The general-pseudoinverse raw-sketch formulation is a separate bridge.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib
variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
variable {m n k r r' t s q : ℕ}

/-- The generalized Nyström squared error is integrable and obeys the
rank-sensitive Gaussian bound with completion factor q/(s-q-1).
The second sketch needs s ≥ q+2, independently of t.
Adapted from NLAlib `gn_main_gaussian` at commit d4d0a69 and the
Gaussian completion identity (Tropp–Webber 2023, proof of Theorem 5.1).
Atlas: `gn-expected-error`. -/
theorem integrable_and_integral_frobSq_sub_sketchedOutput_le_rank_factor_gaussian
    {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t) (hqs : q + 2 ≤ s) (hq : 1 ≤ q)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ) (Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t)
    (hΨ : μ.map (fun ω => Matrix.of.symm (Ψ ω)) = gaussianMatrix m s)
    (hind : IndepFun (fun ω => Matrix.of.symm (Ω ω)) (fun ω => Matrix.of.symm (Ψ ω)) μ)
    (Q : Ωs → Matrix (Fin m) (Fin q) ℝ) (Qf : (Fin n → Fin t → ℝ) → Matrix (Fin m) (Fin q) ℝ)
    (hQf : ∀ i j, Measurable fun x => Qf x i j) (hQ : ∀ ω, Q ω = Qf (Matrix.of.symm (Ω ω)))
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω) :
    Integrable (fun ω => frobSq (A - sketchedOutput (Q ω) (Ψ ω) A)) μ ∧
    ∫ ω, frobSq (A - sketchedOutput (Q ω) (Ψ ω) A) ∂μ
      ≤ (1 + (q : ℝ) / (s - q - 1)) * ((1 + (k : ℝ) / (t - k - 1)) * frobSq S₂) := by
  have hQ' : Q = fun ω => Qf (Matrix.of.symm (Ω ω)) := funext hQ
  subst hQ'
  obtain ⟨hunit, hinv, hZi⟩ := rsvd_gaussian_inputs S₂ hV₁ hV₂ hV hkt Ω hΩ
  have hc0 : 0 ≤ 1 + (q : ℝ) / (s - q - 1) := by
    have : (q : ℝ) + 2 ≤ s := by exact_mod_cast hqs
    have : 0 ≤ (q : ℝ) / (s - q - 1) := div_nonneg (Nat.cast_nonneg q) (by linarith)
    linarith
  have hXm : AEMeasurable (fun ω => Matrix.of.symm (Ω ω)) μ :=
    aemeasurable_of_map_eq_gaussianMatrix hΩ
  have hYm : AEMeasurable (fun ω => Matrix.of.symm (Ψ ω)) μ :=
    aemeasurable_of_map_eq_gaussianMatrix hΨ
  have hres : Measurable fun x => frobSq (residual (Qf x) A) :=
    measurable_frobSq_residual_of A hQf
  have hYi : Integrable (fun ω => frobSq (residual (Qf (Matrix.of.symm (Ω ω))) A)) μ := by
    refine (integrable_const (frobSq A)).mono' (hres.comp_aemeasurable hXm).aestronglyMeasurable ?_
    filter_upwards [hQo] with ω h
    rw [Real.norm_of_nonneg (frobSq_nonneg _)]
    exact frobSq_residual_le h A
  have hgm : Measurable fun p : (Fin n → Fin t → ℝ) × (Fin m → Fin s → ℝ) =>
      frobSq (A - sketchedOutput (Qf p.1) (Matrix.of p.2) A) :=
    measurable_frobSq_sub_sketchedOutput A (fun i j => (hQf i j).comp measurable_fst)
      (fun i j => by simp only [Matrix.of_apply]; fun_prop)
  have hL : ∫⁻ ω, ENNReal.ofReal
        (frobSq (A - sketchedOutput (Qf (Matrix.of.symm (Ω ω))) (Ψ ω) A)) ∂μ
      = ∫⁻ ω, ENNReal.ofReal ((1 + (q : ℝ) / (s - q - 1))
          * frobSq (residual (Qf (Matrix.of.symm (Ω ω))) A)) ∂μ := by
    refine (lintegral_of_indepFun hXm hYm hind
      (g := fun x y => ENNReal.ofReal (frobSq (A - sketchedOutput (Qf x) (Matrix.of y) A)))
      (ENNReal.measurable_ofReal.comp hgm).aemeasurable).trans ?_
    rw [hΨ, lintegral_map' ?_ hXm]
    · apply lintegral_congr_ae
      filter_upwards [hQo] with ω hω
      obtain ⟨hi, hv⟩ := completion_gaussian_of_orthonormal (s := s) _ A hω hq hqs
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => frobSq_nonneg _), hv]
    · exact (Measurable.lintegral_prod_right' (ENNReal.measurable_ofReal.comp hgm)).aemeasurable
  have hcond : ∫ ω, frobSq (A - sketchedOutput (Qf (Matrix.of.symm (Ω ω))) (Ψ ω) A) ∂μ
      = ∫ ω, (1 + (q : ℝ) / (s - q - 1))
          * frobSq (residual (Qf (Matrix.of.symm (Ω ω))) A) ∂μ := by
    have hLm : AEStronglyMeasurable
        (fun ω => frobSq (A - sketchedOutput (Qf (Matrix.of.symm (Ω ω))) (Ψ ω) A)) μ :=
      (hgm.comp_aemeasurable (hXm.prodMk hYm)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => frobSq_nonneg _) hLm,
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun _ => mul_nonneg hc0 (frobSq_nonneg _))
        (hYi.const_mul _).aestronglyMeasurable, hL]
  have hLm : AEStronglyMeasurable
      (fun ω => frobSq (A - sketchedOutput (Qf (Matrix.of.symm (Ω ω))) (Ψ ω) A)) μ :=
    (hgm.comp_aemeasurable (hXm.prodMk hYm)).aestronglyMeasurable
  have hFinite : ∫⁻ ω, ENNReal.ofReal
      (frobSq (A - sketchedOutput (Qf (Matrix.of.symm (Ω ω))) (Ψ ω) A)) ∂μ < ⊤ := by
    rw [hL, ← ofReal_integral_eq_lintegral_ofReal (hYi.const_mul _)
      (ae_of_all _ fun _ => mul_nonneg hc0 (frobSq_nonneg _))]
    exact ENNReal.ofReal_lt_top
  have hIntegrable : Integrable
      (fun ω => frobSq (A - sketchedOutput (Qf (Matrix.of.symm (Ω ω))) (Ψ ω) A)) μ :=
    ⟨hLm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => frobSq_nonneg _)).2 hFinite⟩
  refine ⟨hIntegrable, ?_⟩
  rw [hcond, integral_const_mul]
  have hRange := rsvd_main_gaussian hA hU₂ hV₁ hV₂ hV hkt Ω hΩ
    (fun ω => Qf (Matrix.of.symm (Ω ω))) hQo hQr
  apply mul_le_mul_of_nonneg_left _ hc0
  simpa only [residual] using hRange

end NLAlib
