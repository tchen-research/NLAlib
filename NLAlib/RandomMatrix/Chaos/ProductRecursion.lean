import NLAlib.RandomMatrix.Chaos.Integrability
import NLAlib.RandomMatrix.Chaos.SumRecursion

/-!
# Product-law recursion of the expected chaos norm

Splitting off the last independent coordinate group is a measure-preserving
finite coordinate reindexing followed by ordinary product integration.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace NLAlib

variable {τ ι m n : Type*} [Fintype τ] [Fintype ι] [DecidableEq τ] [DecidableEq ι]

/-- Join the old coordinate groups and the last coordinate group. -/
def chaosExtendSamples (x : τ × ι → ℝ) (y : ι → ℝ) : (τ ⊕ Unit) × ι → ℝ :=
  fun ti => match ti.1 with
    | Sum.inl t => x (t, ti.2)
    | Sum.inr _ => y ti.2

private def groupPairEquiv : ((τ ⊕ Unit) × ι) ≃ ((τ × ι) ⊕ ι) where
  toFun ti := match ti.1 with
    | Sum.inl t => Sum.inl (t, ti.2)
    | Sum.inr _ => Sum.inr ti.2
  invFun ti := match ti with
    | Sum.inl ti => (Sum.inl ti.1, ti.2)
    | Sum.inr i => (Sum.inr (), i)
  left_inv ti := by
    rcases ti with ⟨t | u, i⟩
    · rfl
    · cases u
      rfl
  right_inv ti := by rcases ti with ti | i <;> rfl

variable (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

/-- Joining independent old and last groups gives the complete decoupled
coordinate product law. -/
theorem hasLaw_chaosExtendSamples :
    HasLaw (fun xy : (τ × ι → ℝ) × (ι → ℝ) => chaosExtendSamples xy.1 xy.2)
      (Measure.pi (fun ti : (τ ⊕ Unit) × ι => ν ti.2))
      ((Measure.pi (fun ti : τ × ι => ν ti.2)).prod (Measure.pi ν)) := by
  let η : (τ × ι) ⊕ ι → Measure ℝ := Sum.elim (fun ti => ν ti.2) ν
  haveI : ∀ ti, IsProbabilityMeasure (η ti) := by
    intro ti
    rcases ti with ti | i
    · exact inferInstanceAs (IsProbabilityMeasure (ν ti.2))
    · exact inferInstanceAs (IsProbabilityMeasure (ν i))
  have hs := (measurePreserving_sumPiEquivProdPi_symm η).hasLaw
  have hm := (measurePreserving_piCongrLeft
    (fun ti : (τ ⊕ Unit) × ι => ν ti.2) (groupPairEquiv (τ := τ) (ι := ι)).symm).hasLaw
  have he : (fun ti : (τ × ι) ⊕ ι => ν (groupPairEquiv.symm ti).2) = η := by
    funext ti
    rcases ti with ti | i <;> rfl
  rw [he] at hm
  convert hm.comp hs using 1
  · funext xy ti
    rcases ti with ⟨t | u, i⟩
    · rfl
    · cases u
      rfl
  · rfl

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Expected chaos norms split as an iterated expectation of an actual linear
matrix series in the last group. Integrability follows from coordinate first
moments, so this is genuine Fubini rather than a formal conditional bound. -/
theorem integral_specNorm_decoupledMatrixChaos_sum_recursion
    (A : ((τ ⊕ Unit) → ι) → Matrix m n ℝ) (hν : ∀ i, Integrable id (ν i)) :
    (∫ z : (τ ⊕ Unit) × ι → ℝ,
      specNorm (decoupledMatrixChaos A (fun t i => z (t, i)))
        ∂Measure.pi (fun ti : (τ ⊕ Unit) × ι => ν ti.2)) =
      ∫ x : τ × ι → ℝ, ∫ y : ι → ℝ,
        specNorm (∑ j, y j • decoupledMatrixChaos
          (fun z => A (chaosAppendTuple z j)) (fun t i => x (t, i)))
          ∂Measure.pi ν ∂Measure.pi (fun ti : τ × ι => ν ti.2) := by
  let Y : (((τ ⊕ Unit) × ι) → ℝ) → Matrix m n ℝ :=
    fun z => decoupledMatrixChaos A (fun t i => z (t, i))
  have hY : Integrable Y (Measure.pi (fun ti : (τ ⊕ Unit) × ι => ν ti.2)) :=
    integrable_decoupledMatrixChaos ν A hν
  have hlaw := hasLaw_chaosExtendSamples (τ := τ) ν
  have hm := hlaw.measurePreserving (by
    apply measurable_pi_lambda
    intro ti
    unfold chaosExtendSamples
    rcases ti with ⟨t | u, i⟩ <;> fun_prop)
  have hj := hm.integrable_comp_of_integrable hY
  calc
    _ = ∫ xy : (τ × ι → ℝ) × (ι → ℝ), ‖Y (chaosExtendSamples xy.1 xy.2)‖
        ∂((Measure.pi (fun ti : τ × ι => ν ti.2)).prod (Measure.pi ν)) := by
      simpa only [specNorm_eq_norm, Function.comp_apply] using
        (hlaw.integral_comp hY.norm.aestronglyMeasurable).symm
    _ = ∫ x : τ × ι → ℝ, ∫ y : ι → ℝ, ‖Y (chaosExtendSamples x y)‖
        ∂Measure.pi ν ∂Measure.pi (fun ti : τ × ι => ν ti.2) := integral_prod _ hj.norm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      have hsamp : (fun t i => chaosExtendSamples x y (t, i)) =
          Sum.elim (fun t i => x (t, i)) (fun _ => y) := by
        funext t i
        rcases t with t | u <;> rfl
      change specNorm (Y (chaosExtendSamples x y)) = _
      dsimp only [Y]
      rw [hsamp, decoupledMatrixChaos_sum_recursion]

end NLAlib
