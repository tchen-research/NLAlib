import NLAlib.ForMathlib.MeasureTheory.Matrix
import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Functions.HermitianCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of continuous matrix functional calculus

A measurable Hermitian matrix with spectrum in a fixed compact set can be
composed with any continuous scalar function on that set. No eigenvector
selection is needed, so repeated eigenvalues and rank changes are included.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {𝕜 n Ω : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- Continuous scalar calculus preserves measurability along Hermitian inputs
whose spectra lie in a fixed compact set. -/
theorem measurable_cfc_of_spectrum_subset {M : Ω → Matrix n n 𝕜}
    (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    {s : Set ℝ} (hs : IsCompact s) (hS : ∀ ω, spectrum ℝ (M ω) ⊆ s)
    (f : ℝ → ℝ) (hf : ContinuousOn f s) :
    Measurable (fun ω => cfc f (M ω)) := by
  let _ := normedAlgebraRealMatrix (𝕜 := 𝕜) (d := n)
  let T := {B : Matrix n n 𝕜 | IsSelfAdjoint B ∧ spectrum ℝ B ⊆ s}
  have hc : Continuous (fun B : T => cfc f (B : Matrix n n 𝕜)) :=
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_cfc (Matrix n n 𝕜) hs f hf)
  exact hc.measurable.comp (hM.subtype_mk (h := fun ω => ⟨hH ω, hS ω⟩))

open scoped Matrix.Norms.L2Operator in
/-- A uniform spectral-norm bound is enough to use the previous measurability
theorem on the corresponding closed real interval. -/
theorem measurable_cfc_of_specNorm_le {M : Ω → Matrix n n 𝕜}
    (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian)
    {R : ℝ} (hR : ∀ ω, specNorm (M ω) ≤ R)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-R) R)) :
    Measurable (fun ω => cfc f (M ω)) := by
  let _ := normedAlgebraRealMatrix (𝕜 := 𝕜) (d := n)
  rcases isEmpty_or_nonempty n with hn | hn
  · have he : (fun ω => cfc f (M ω)) = fun _ => (0 : Matrix n n 𝕜) :=
      funext fun _ => Subsingleton.elim _ _
    rw [he]
    exact measurable_const
  apply measurable_cfc_of_spectrum_subset hM hH isCompact_Icc (fun ω x hx => ?_) f hf
  have h := (spectrum.norm_le_norm_of_mem hx).trans (by simpa only [← specNorm_eq_norm] using hR ω)
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using h)

end NLAlib
