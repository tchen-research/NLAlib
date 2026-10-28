import NLAlib.Matrix.Measurability.GramPseudoinverse
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Native product contraction for the Haar Gaussian representation

Fubini transfers a fixed Gaussian sandwich moment to a random independent
matrix factor. Integrability follows from the actual finite inverse moment;
no conditional Gaussian or matrix-Beta law is assumed.
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace NLAlib

/-- A fixed right-factor second moment extends to any measurable independent
random right factor with finite squared Frobenius mean. -/
theorem integrable_and_integral_frobSq_mul_random_prod
    {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {r s t : Type*} [Fintype r] [Fintype s] [Fintype t]
    {μ : Measure α} {ν : Measure (Matrix s r 𝕜)} [SFinite μ] [SFinite ν]
    (T : α → Matrix r t 𝕜) (hT : Measurable T)
    (hi : Integrable (fun a => frobSq (T a)) μ) (c : ℝ)
    (hfix : ∀ W : Matrix r t 𝕜,
      Integrable (fun Z => frobSq (Z*W)) ν ∧ ∫ Z, frobSq (Z*W) ∂ν = c*frobSq W) :
    Integrable (fun p : α × Matrix s r 𝕜 => frobSq (p.2*T p.1)) (μ.prod ν) ∧
      ∫ p : α × Matrix s r 𝕜, frobSq (p.2*T p.1) ∂μ.prod ν =
        c*∫ a, frobSq (T a) ∂μ := by
  have hm : Measurable (fun p : α × Matrix s r 𝕜 => frobSq (p.2*T p.1)) :=
    measurable_frobSq.comp (measurable_snd.matrix_mul (hT.comp measurable_fst))
  have hp : Integrable (fun p : α × Matrix s r 𝕜 => frobSq (p.2*T p.1)) (μ.prod ν) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun a => (hfix (T a)).1)
    · simpa only [Real.norm_of_nonneg (frobSq_nonneg _),(hfix _).2] using hi.const_mul c
  refine ⟨hp,?_⟩
  rw [integral_prod _ hp]
  simp_rw [(hfix _).2]
  exact integral_const_mul c _

end NLAlib
