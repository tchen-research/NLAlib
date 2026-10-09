import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Integrals: resampling one coordinate, Cauchy–Schwarz, linear-growth integrability

General integration facts that are not about NLAlib's objects; candidates for upstreaming to
`Mathlib/MeasureTheory/Integral/` and `Mathlib/MeasureTheory/Constructions/Pi.lean`.

* One-coordinate Fubini for a product of probability measures `⊗ⱼ μⱼ`:
  `measurePreserving_update_pi` (`(x, t) ↦ update x i t` maps `(⊗ⱼ μⱼ) ⊗ μᵢ` to `⊗ⱼ μⱼ`),
  `integrable_comp_update_pi`, `integral_integral_update_pi`, `ae_integrable_comp_update_pi`,
  `integrable_integral_update_pi`. Used by tensorization of entropy and the multivariate
  log-Sobolev inequality (atlas `entropy-tensorization`, `gaussian-log-sobolev`).
* `sq_integral_le_integral_div_mul_integral`: Cauchy–Schwarz as `(∫ a)² ≤ (∫ a²/b) (∫ b)` for
  `b ≥ δ > 0` on a probability space (atlas `gaussian-log-sobolev`).
* `integrable_comp_of_abs_le_sum_abs`: `g(X)` is integrable when `|g x| ≤ ∑ₜ |xₜ| + K` and the
  coordinates of `X` are integrable (atlas `sudakov-fernique`, `gordon-minimax`).
-/

noncomputable section

open MeasureTheory

namespace NLAlib

/-! ### Resampling one coordinate of a product measure -/

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]

/-- Resampling one coordinate preserves a product measure: `(x, t) ↦ update x i t` maps
`(⊗ⱼ μⱼ) ⊗ μᵢ` to `⊗ⱼ μⱼ`. Atlas: `entropy-tensorization` (helper). Ported from Prove2me
solution `GaussianMatrix.entropy_tensorization`. -/
theorem measurePreserving_update_pi (i : ι) :
    MeasurePreserving (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  refine ⟨measurable_update', ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi (Function.update s i Set.univ) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · have := h j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · have := h1 j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : (fun j => μ j (Function.update s i Set.univ j))
      = Function.update (fun j => μ j (s j)) i 1 := by
    ext1 j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [this, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    ← Finset.mul_prod_erase Finset.univ (fun j => μ j (s j)) (Finset.mem_univ i), mul_comm,
    Finset.sdiff_singleton_eq_erase]

/-- Integrability of `F ∘ update` on `(⊗ⱼ μⱼ) ⊗ μᵢ` for `F ∈ L¹(⊗ⱼ μⱼ)`.
Atlas: `entropy-tensorization` (helper). Ported from Prove2me solution
`GaussianMatrix.entropy_tensorization`. -/
theorem integrable_comp_update_pi (i : ι) {F : (ι → Ω) → ℝ} (hF : Integrable F (Measure.pi μ)) :
    Integrable (fun p : (ι → Ω) × Ω => F (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) :=
  ((measurePreserving_update_pi μ i).integrable_comp hF.aestronglyMeasurable).2 hF

/-- Fubini for resampling one coordinate:
`∫ (∫ F(update x i t) dμᵢ(t)) d(⊗ⱼ μⱼ)(x) = ∫ F d(⊗ⱼ μⱼ)`. Atlas: `entropy-tensorization`
(helper). Ported from Prove2me solution `GaussianMatrix.entropy_tensorization`. -/
theorem integral_integral_update_pi (i : ι) {F : (ι → Ω) → ℝ}
    (hF : Integrable F (Measure.pi μ)) :
    ∫ x, ∫ t, F (Function.update x i t) ∂(μ i) ∂(Measure.pi μ) = ∫ x, F x ∂(Measure.pi μ) := by
  have hmp := measurePreserving_update_pi μ i
  rw [← integral_prod _ (integrable_comp_update_pi μ i hF)]
  calc ∫ p, F (Function.update p.1 i p.2) ∂((Measure.pi μ).prod (μ i))
      = ∫ x, F x ∂(Measure.map (fun p : (ι → Ω) × Ω => Function.update p.1 i p.2)
          ((Measure.pi μ).prod (μ i))) :=
        (integral_map hmp.measurable.aemeasurable
          (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)).symm
    _ = ∫ x, F x ∂(Measure.pi μ) := by rw [hmp.map_eq]

/-- For `F ∈ L¹(⊗ⱼ μⱼ)`, almost every one-coordinate section `t ↦ F(update x i t)` is
`μᵢ`-integrable. Atlas: `entropy-tensorization` (helper). Ported from Prove2me solution
`GaussianMatrix.entropy_tensorization`. -/
theorem ae_integrable_comp_update_pi (i : ι) {F : (ι → Ω) → ℝ}
    (hF : Integrable F (Measure.pi μ)) :
    ∀ᵐ x ∂(Measure.pi μ), Integrable (fun t => F (Function.update x i t)) (μ i) :=
  (integrable_comp_update_pi μ i hF).prod_right_ae

/-- For `F ∈ L¹(⊗ⱼ μⱼ)`, `x ↦ ∫ F(update x i t) dμᵢ(t)` is integrable. Atlas:
`entropy-tensorization` (helper). Ported from Prove2me solution
`GaussianMatrix.entropy_tensorization`. -/
theorem integrable_integral_update_pi (i : ι) {F : (ι → Ω) → ℝ}
    (hF : Integrable F (Measure.pi μ)) :
    Integrable (fun x => ∫ t, F (Function.update x i t) ∂(μ i)) (Measure.pi μ) :=
  (integrable_comp_update_pi μ i hF).integral_prod_left

end Product

/-! ### Cauchy–Schwarz and integrability under linear growth -/

/-- Cauchy–Schwarz in the form `(∫ a)² ≤ (∫ a²/b) (∫ b)` for `b ≥ δ > 0` on a probability
space. Atlas: `gaussian-log-sobolev` (helper). Ported from Prove2me solution
`GaussianMatrix.gaussian_logsobolev_bounded_below`. -/
theorem sq_integral_le_integral_div_mul_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (a b : α → ℝ) (δ : ℝ) (hδ : 0 < δ) (hb : ∀ x, δ ≤ b x)
    (ha : Integrable a μ) (hbi : Integrable b μ) (hab : Integrable (fun x => a x ^ 2 / b x) μ) :
    (∫ x, a x ∂μ) ^ 2 ≤ (∫ x, a x ^ 2 / b x ∂μ) * (∫ x, b x ∂μ) := by
  set A := ∫ x, a x ∂μ
  set B := ∫ x, b x ∂μ
  set Q := ∫ x, a x ^ 2 / b x ∂μ
  have hB : δ ≤ B := by
    have := integral_mono (integrable_const δ) hbi hb
    simpa using this
  have hBpos : 0 < B := lt_of_lt_of_le hδ hB
  set l := A / B
  have hpt : ∀ x, (a x - l * b x) ^ 2 / b x = a x ^ 2 / b x - 2 * l * a x + l ^ 2 * b x := by
    intro x
    have : b x ≠ 0 := (lt_of_lt_of_le hδ (hb x)).ne'
    field_simp
    ring
  have hnonneg : 0 ≤ ∫ x, (a x - l * b x) ^ 2 / b x ∂μ := by
    refine integral_nonneg (fun x => div_nonneg (sq_nonneg _) (hδ.le.trans (hb x)))
  have hcalc : ∫ x, (a x - l * b x) ^ 2 / b x ∂μ = Q - 2 * l * A + l ^ 2 * B := by
    simp_rw [hpt]
    have h1 : Integrable (fun x => a x ^ 2 / b x - 2 * l * a x) μ := hab.sub (ha.const_mul _)
    have h2 : Integrable (fun x => l ^ 2 * b x) μ := hbi.const_mul _
    have h3 : Integrable (fun x => 2 * l * a x) μ := ha.const_mul _
    rw [integral_add h1 h2, integral_sub hab h3, integral_const_mul, integral_const_mul]
  rw [hcalc] at hnonneg
  have : Q - 2 * l * A + l ^ 2 * B = Q - A ^ 2 / B := by
    simp only [l]; field_simp; ring
  rw [this, sub_nonneg, div_le_iff₀ hBpos] at hnonneg
  exact hnonneg

/-- A function of a random vector with integrable coordinates is integrable as soon as it is
measurable and grows at most like `∑ₜ |xₜ| + K`. Atlas: helper of `sudakov-fernique`,
`gordon-minimax`. Ported from Prove2me solutions `GaussianMatrix.sudakov_fernique`,
`GaussianMatrix.gordon_minimax` (helper `integrable_of_abs_le`). -/
theorem integrable_comp_of_abs_le_sum_abs {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (X : ι → Ω → ℝ) (hXi : ∀ t, Integrable (X t) P)
    (g : (ι → ℝ) → ℝ) (hg : Measurable g) (hXae : AEMeasurable (fun ω t => X t ω) P) (K : ℝ)
    (hb : ∀ x, |g x| ≤ ∑ t, |x t| + K) :
    Integrable (fun ω => g (fun t => X t ω)) P := by
  refine Integrable.mono' ((integrable_finsetSum Finset.univ fun t _ => (hXi t).abs).add
    (integrable_const K)) (hg.comp_aemeasurable hXae).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  simpa using hb (fun t => X t ω)

end NLAlib
