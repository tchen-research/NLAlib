import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Circular complex Gaussian product laws

The convention is `xi + I*eta`, with independent real `xi, eta ~ N(0,1)`.
Thus both real coordinates have variance one, and the complex second absolute
moment is two. No normalization by `sqrt 2` is included.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- A circular complex Gaussian with independent standard real and imaginary
parts: `xi + I*eta`, rather than the variance-one complex normalization. -/
def circularComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))

private theorem measurable_mk : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.measurable

instance isProbabilityMeasure_circularComplexGaussian :
    IsProbabilityMeasure circularComplexGaussian := by
  unfold circularComplexGaussian
  exact Measure.isProbabilityMeasure_map measurable_mk.aemeasurable

/-- The real and imaginary parts have the exact joint law of two independent
real `N(0,1)` variables, fixing the normalization of this complex Gaussian. -/
theorem hasLaw_re_im_circularComplexGaussian :
    HasLaw (fun z : ℂ => (z.re, z.im))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) circularComplexGaussian := by
  refine ⟨(by fun_prop : Measurable (fun z : ℂ => (z.re, z.im))).aemeasurable, ?_⟩
  rw [circularComplexGaussian, Measure.map_map (by fun_prop) measurable_mk]
  exact Measure.map_id

/-- The finite product of independent circular complex Gaussians, each with
independent real and imaginary `N(0,1)` coordinates. -/
abbrev circularComplexGaussianVector (n : Type*) [Fintype n] : Measure (n → ℂ) :=
  Measure.pi fun _ => circularComplexGaussian

/-- Combine two real coordinate copies into their actual complex vector. -/
def complexifyVector {n : Type*} (x : n ⊕ n → ℝ) : n → ℂ :=
  fun i => ⟨x (.inl i), x (.inr i)⟩

/-- Combining real and imaginary coordinate copies is measurable. -/
@[fun_prop] theorem measurable_complexifyVector {n : Type*} :
    Measurable (complexifyVector : (n ⊕ n → ℝ) → n → ℂ) := by
  apply measurable_pi_lambda
  intro i
  have hp : Measurable (fun x : n ⊕ n → ℝ => (x (.inl i), x (.inr i))) :=
    (measurable_pi_apply (Sum.inl i)).prodMk (measurable_pi_apply (Sum.inr i))
  exact measurable_mk.comp hp

/-- Complexification of two independent real Gaussian coordinate copies has
exactly the complex product law, not merely its separate marginal laws. -/
theorem hasLaw_complexifyVector_gaussianVector {n : Type*} [Fintype n] :
    HasLaw (complexifyVector : (n ⊕ n → ℝ) → n → ℂ)
      (circularComplexGaussianVector n) (gaussianVector (n ⊕ n)) := by
  have hs := measurePreserving_sumPiEquivProdPi
    (fun _ : n ⊕ n => gaussianReal 0 1)
  have hp := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ n
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).symm
  have hc : MeasurePreserving (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) circularComplexGaussian :=
    ⟨measurable_mk, rfl⟩
  have hv := measurePreserving_pi
    (fun _ : n => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ => circularComplexGaussian) (fun _ => hc)
  exact (hv.comp (hp.comp hs)).hasLaw

/-- Extract every real and imaginary coordinate into two disjoint index copies. -/
def realifyVector {n : Type*} (z : n → ℂ) : n ⊕ n → ℝ :=
  Sum.elim (fun i => (z i).re) (fun i => (z i).im)

/-- Real and imaginary coordinate extraction is measurable. -/
@[fun_prop] theorem measurable_realifyVector {n : Type*} :
    Measurable (realifyVector : (n → ℂ) → n ⊕ n → ℝ) := by
  apply measurable_pi_lambda
  intro i
  cases i <;> dsimp only [realifyVector, Sum.elim_inl, Sum.elim_inr] <;> fun_prop

/-- The entire real-imaginary coordinate family has the real Gaussian product
law. This certifies independence of all `2*card n` real coordinates. -/
theorem hasLaw_realifyVector_circularComplexGaussianVector {n : Type*} [Fintype n] :
    HasLaw (realifyVector : (n → ℂ) → n ⊕ n → ℝ)
      (gaussianVector (n ⊕ n)) (circularComplexGaussianVector n) := by
  refine ⟨measurable_realifyVector.aemeasurable, ?_⟩
  rw [← (hasLaw_complexifyVector_gaussianVector (n := n)).map_eq,
    Measure.map_map measurable_realifyVector measurable_complexifyVector]
  have hf : (realifyVector ∘ complexifyVector : (n ⊕ n → ℝ) → n ⊕ n → ℝ) = id := by
    funext x i
    cases i <;> rfl
  rw [hf, Measure.map_id]

/-- Each coordinate has the stated circular complex Gaussian law. -/
theorem hasLaw_eval_circularComplexGaussianVector {n : Type*} [Fintype n] (i : n) :
    HasLaw (fun x : n → ℂ => x i) circularComplexGaussian (circularComplexGaussianVector n) :=
  (measurePreserving_eval (fun _ : n => circularComplexGaussian) i).hasLaw

/-- The complex product-law coordinates are independent as complex-valued
random variables, including both real coordinates at each index. -/
theorem iIndepFun_eval_circularComplexGaussianVector (n : Type*) [Fintype n] :
    iIndepFun (fun i (x : n → ℂ) => x i) (circularComplexGaussianVector n) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

/-- Circular complex Gaussian joint laws transport coordinate marginals to an
arbitrary sample space. -/
theorem _root_.ProbabilityTheory.HasLaw.hasLaw_eval_circularComplexGaussian
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    {Z : Ω → n → ℂ} (hZ : HasLaw Z (circularComplexGaussianVector n) μ) (i : n) :
    HasLaw (fun ω => Z ω i) circularComplexGaussian μ :=
  (hasLaw_eval_circularComplexGaussianVector i).comp hZ

/-- A circular complex Gaussian product joint law implies independence of all
complex coordinates on the given sample space. -/
theorem _root_.ProbabilityTheory.HasLaw.iIndepFun_eval_of_circularComplexGaussianVector
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    {Z : Ω → n → ℂ} (hZ : HasLaw Z (circularComplexGaussianVector n) μ) :
    iIndepFun (fun i ω => Z ω i) μ := by
  have := hZ.isProbabilityMeasure
  exact (iIndepFun_iff_hasLaw_pi_pi
    (fun i => hZ.hasLaw_eval_circularComplexGaussian i)).2 hZ

end NLAlib
