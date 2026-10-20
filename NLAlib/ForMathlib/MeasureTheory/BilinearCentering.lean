import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Centering the genuine Bochner expectation of a bilinear test

This elementary identity expands the actual centered product. It is valid
for Banach-valued bilinear tests and does not use an independence assumption.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace ContinuousLinearMap
variable {Ω F G 𝕜 : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [RCLike 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Subtracting the actual mean in both slots of a Bochner-integrable
bilinear product subtracts exactly the bilinear product of its means. All
cross-term integrability follows from the genuine continuous linear maps. -/
theorem integral_bilinear_sub_integral
    (B : F →L[𝕜] F →L[𝕜] G) (f : Ω → F)
    (hf : Integrable f μ) (hBf : Integrable (fun x => B (f x) (f x)) μ) :
    (∫ x, B (f x-∫ y, f y ∂μ) (f x-∫ y, f y ∂μ) ∂μ)=
      (∫ x, B (f x) (f x) ∂μ)-B (∫ y, f y ∂μ) (∫ y, f y ∂μ) := by
  let m := ∫ y, f y ∂μ
  have hleft : Integrable (fun x => B (f x) m) μ := (B.flip m).integrable_comp hf
  have hright : Integrable (fun x => B m (f x)) μ := (B m).integrable_comp hf
  have heq (x : Ω) : B (f x-m) (f x-m)=
      B (f x) (f x)-B (f x) m-B m (f x)+B m m := by
    simp only [map_sub,sub_apply]
    abel
  change (∫ x, B (f x-m) (f x-m) ∂μ)=(∫ x, B (f x) (f x) ∂μ)-B m m
  simp_rw [heq]
  have hadd := integral_add ((hBf.sub hleft).sub hright)
    (integrable_const (B m m) : Integrable (fun _ : Ω => B m m) μ)
  have hsub := integral_sub (hBf.sub hleft) hright
  have hsub' := integral_sub hBf hleft
  simp only [Pi.sub_apply] at hadd hsub hsub'
  have hleftMean : (∫ x, B (f x) m ∂μ)=B m m := (B.flip m).integral_comp_comm hf
  have hrightMean : (∫ x, B m (f x) ∂μ)=B m m := (B m).integral_comp_comm hf
  rw [hadd,hsub,hsub',
    hleftMean,hrightMean,
    integral_const,probReal_univ,one_smul]
  change (∫ x, B (f x) (f x) ∂μ)-B m m-B m m+B m m=_
  abel

end ContinuousLinearMap
