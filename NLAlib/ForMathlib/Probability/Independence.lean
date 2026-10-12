import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini for independent random variables

If `X` and `Y` are independent, `E g(X, Y) = ∫ (∫ g(x, y) d(law Y)(y)) d(law X)(x)`:
`lintegral_of_indepFun` (`ℝ≥0∞`-valued `g`, only a.e.-measurability needed) and
`integral_of_indepFun` (Bochner, `g` integrable for the product of the laws). Both are
`indepFun_iff_map_prod_eq_prod_map_map` followed by Fubini; candidates for upstreaming to
`Mathlib/Probability/Independence/`. Used by the Gaussian conditioning arguments (atlas
`gaussian-conditioning`) and the trace estimators.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]

/-- **Fubini for independent random variables, `ℝ≥0∞` version.** If `X` and `Y` are independent,
`E g(X, Y) = ∫ (∫ g(x, y) d(law Y)(y)) d(law X)(x)`. Only a.e.-measurability of `g` for the
product of the laws is needed.

Standard (e.g. Durrett, *Probability*, Thm 2.1.12 / Kallenberg Lemma 3.11). Helper of atlas
`gaussian-conditioning`. -/
theorem lintegral_of_indepFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X : Ωs → α} {Y : Ωs → β} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : IndepFun X Y μ) {g : α → β → ℝ≥0∞}
    (hg : AEMeasurable (Function.uncurry g) ((μ.map X).prod (μ.map Y))) :
    ∫⁻ ω, g (X ω) (Y ω) ∂μ = ∫⁻ x, ∫⁻ y, g x y ∂(μ.map Y) ∂(μ.map X) := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY
  have hg' : AEMeasurable (Function.uncurry g) (μ.map fun ω => (X ω, Y ω)) := by rwa [h]
  calc ∫⁻ ω, g (X ω) (Y ω) ∂μ
      = ∫⁻ p, Function.uncurry g p ∂(μ.map fun ω => (X ω, Y ω)) :=
        (lintegral_map' hg' (hX.prodMk hY)).symm
    _ = ∫⁻ p, Function.uncurry g p ∂((μ.map X).prod (μ.map Y)) := by rw [h]
    _ = _ := lintegral_prod _ hg

/-- **Fubini for independent random variables, Bochner version.** If `X` and `Y` are
independent and `(x, y) ↦ g x y` is integrable for the product of the laws, then
`E g(X, Y) = ∫ (∫ g(x, y) d(law Y)(y)) d(law X)(x)`.

Standard (e.g. Durrett, *Probability*, Thm 2.1.12). Helper of atlas `gaussian-conditioning`
(a Mathlib-level fact, not itself an atlas result). -/
theorem integral_of_indepFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X : Ωs → α} {Y : Ωs → β} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : IndepFun X Y μ) {g : α → β → ℝ}
    (hg : Integrable (fun p : α × β => g p.1 p.2) ((μ.map X).prod (μ.map Y))) :
    ∫ ω, g (X ω) (Y ω) ∂μ = ∫ x, ∫ y, g x y ∂(μ.map Y) ∂(μ.map X) := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY
  have hg' : AEStronglyMeasurable (fun p : α × β => g p.1 p.2)
      (μ.map fun ω => (X ω, Y ω)) := by rw [h]; exact hg.aestronglyMeasurable
  calc ∫ ω, g (X ω) (Y ω) ∂μ
      = ∫ p : α × β, g p.1 p.2 ∂(μ.map fun ω => (X ω, Y ω)) :=
        (integral_map (hX.prodMk hY) hg').symm
    _ = ∫ p : α × β, g p.1 p.2 ∂((μ.map X).prod (μ.map Y)) := by rw [h]
    _ = _ := integral_prod _ hg

end NLAlib
