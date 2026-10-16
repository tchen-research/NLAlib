import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Bilinear covariance identities for exchangeable pairs

Conditional regression and equality of the actual swapped joint laws give
discrete integration by parts for continuous real bilinear maps. The second
moments imply all product integrability needed in the argument.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLAlib

variable {Ω E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- An actual exchangeable pair with linear conditional regression satisfies
bilinear discrete integration by parts. The conditioning sigma algebra may be
any sub-sigma algebra making `f ∘ X` measurable. This includes conditioning on
`X` itself. Source: Tropp (2026), §6.3; atlas `exchangeable-matrix-covariance`.
atlas: exchangeable-matrix-covariance (partial) -/
theorem integral_bilin_exchangeable
    {m mΩ : MeasurableSpace Ω} {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ] {X X' : Ω → E}
    (hex : IdentDistrib (fun ω => (X ω, X' ω)) (fun ω => (X' ω, X ω)) μ μ)
    (hX : MemLp X 2 μ) (f : E → F) (hf : Measurable f)
    (hfX : MemLp (f ∘ X) 2 μ)
    (hm : m ≤ mΩ)
    (hfm : AEStronglyMeasurable[m] (f ∘ X) μ)
    (α : ℝ) (hα : α ≠ 0)
    (hreg : μ[X - X' | m] =ᵐ[μ] fun ω => α • (X ω - ∫ t, X t ∂μ))
    (B : E →L[ℝ] F →L[ℝ] G) :
    (∫ ω, B (X ω - ∫ t, X t ∂μ) (f (X ω)) ∂μ) =
      (2 * α)⁻¹ • ∫ ω, B (X ω - X' ω) (f (X ω) - f (X' ω)) ∂μ := by
  have hXp : MemLp X' 2 μ := (hex.comp measurable_fst).memLp_snd hX
  have hfXp : MemLp (f ∘ X') 2 μ :=
    (hex.comp (hf.comp measurable_fst)).memLp_snd hfX
  have hD : MemLp (X - X') 2 μ := hX.sub hXp
  have hC : MemLp (fun ω => X ω - ∫ t, X t ∂μ) 2 μ := hX.sub (memLp_const _)
  have hU : Integrable (fun ω => B (X ω - X' ω) (f (X ω))) μ :=
    (B.memLp_of_bilin 1 hD hfX).integrable le_rfl
  have hV : Integrable (fun ω => B (X ω - X' ω) (f (X' ω))) μ :=
    (B.memLp_of_bilin 1 hD hfXp).integrable le_rfl
  have hL : Integrable (fun ω => B (X ω - ∫ t, X t ∂μ) (f (X ω))) μ :=
    (B.memLp_of_bilin 1 hC hfX).integrable le_rfl
  have hce := condExp_bilin_of_aestronglyMeasurable_right B hfm hU
    (hD.integrable one_le_two)
  simp only [Function.comp_def] at hce
  have hfirst : (∫ ω, B (X ω - X' ω) (f (X ω)) ∂μ) =
      α • ∫ ω, B (X ω - ∫ t, X t ∂μ) (f (X ω)) ∂μ := by
    calc
      _ = ∫ ω, μ[fun ω => B (X ω - X' ω) (f (X ω)) | m] ω ∂μ :=
        (integral_condExp hm).symm
      _ = ∫ ω, α • B (X ω - ∫ t, X t ∂μ) (f (X ω)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hce, hreg] with ω hc hr
        change μ[(fun t => X t - X' t) | m] ω = _ at hr
        rw [hc, hr]
        simp
      _ = _ := integral_smul _ _
  have hswap : (∫ ω, B (X ω - X' ω) (f (X ω)) ∂μ) =
      -(∫ ω, B (X ω - X' ω) (f (X' ω)) ∂μ) := by
    have hmeas : Measurable (fun p : E × E => B (p.1 - p.2) (f p.1)) :=
      (B.continuous₂.measurable.comp ((measurable_fst.sub measurable_snd).prodMk
        (hf.comp measurable_fst)))
    have he := (hex.comp hmeas).integral_eq
    calc
      _ = ∫ ω, B (X' ω - X ω) (f (X' ω)) ∂μ := he
      _ = ∫ ω, -(B (X ω - X' ω) (f (X' ω))) ∂μ := by
        congr 1
        funext ω
        rw [← neg_sub]
        simp
      _ = _ := integral_neg _
  have hv : (∫ ω, B (X ω - X' ω) (f (X' ω)) ∂μ) =
      -(∫ ω, B (X ω - X' ω) (f (X ω)) ∂μ) := by rw [hswap, neg_neg]
  have he : (∫ ω, B (X ω - X' ω) (f (X ω) - f (X' ω)) ∂μ) =
      (2 * α) • ∫ ω, B (X ω - ∫ t, X t ∂μ) (f (X ω)) ∂μ := by
    have hpoint (ω : Ω) : B (X ω - X' ω) (f (X ω) - f (X' ω)) =
        B (X ω - X' ω) (f (X ω)) - B (X ω - X' ω) (f (X' ω)) := (B _).map_sub _ _
    simp_rw [hpoint]
    rw [integral_sub hU hV, hv, sub_neg_eq_add,
      hfirst, ← add_smul]
    congr 1
    ring
  rw [he, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero hα), one_smul]

/-- Every pair of real continuous linear coordinates satisfies the covariance
tensor identity. Taking the coordinates of any finite real basis gives the
entire bilinear real covariance tensor, including mixed real/imaginary entry
coordinates for complex Hermitian matrices. Source: Tropp (2026), §6.3; atlas
`exchangeable-matrix-covariance`.
atlas: exchangeable-matrix-covariance (partial) -/
theorem integral_coordinate_covariance_exchangeable
    {m mΩ : MeasurableSpace Ω} {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {X X' : Ω → E}
    (hex : IdentDistrib (fun ω => (X ω, X' ω)) (fun ω => (X' ω, X ω)) μ μ)
    (hX : MemLp X 2 μ) (hm : m ≤ mΩ) (hXm : StronglyMeasurable[m] X)
    (α : ℝ) (hα : α ≠ 0)
    (hreg : μ[X - X' | m] =ᵐ[μ] fun ω => α • (X ω - ∫ t, X t ∂μ))
    (u v : E →L[ℝ] ℝ) :
    (∫ ω, u (X ω - ∫ t, X t ∂μ) * v (X ω - ∫ t, X t ∂μ) ∂μ) =
      (2 * α)⁻¹ * ∫ ω, u (X ω - X' ω) * v (X ω - X' ω) ∂μ := by
  let f : E → E := fun x => x - ∫ t, X t ∂μ
  have hf : Measurable f := measurable_id.sub measurable_const
  have hfX : MemLp (f ∘ X) 2 μ := hX.sub (memLp_const _)
  have hfm : AEStronglyMeasurable[m] (f ∘ X) μ :=
    (hXm.sub stronglyMeasurable_const).aestronglyMeasurable
  have h := integral_bilin_exchangeable hex hX f hf hfX hm hfm α hα hreg
    ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp u v)
  change (∫ ω, u (X ω - ∫ t, X t ∂μ) * v (X ω - ∫ t, X t ∂μ) ∂μ) =
    (2 * α)⁻¹ • ∫ ω, u (X ω - X' ω) *
      v ((X ω - ∫ t, X t ∂μ) - (X' ω - ∫ t, X t ∂μ)) ∂μ at h
  simpa only [sub_sub_sub_cancel_right, smul_eq_mul] using h

end NLAlib
