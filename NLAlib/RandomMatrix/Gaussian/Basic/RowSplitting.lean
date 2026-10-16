import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Splitting a Gaussian matrix row

Measure-preserving coordinate splitting and its expectation identities, used
when a comparison process combines two independent Gaussian vectors.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

/-- Splitting a standard Gaussian row into two coordinate groups preserves the product law. -/
theorem measurePreserving_gaussianVector_split (n N : ℕ) :
    MeasurePreserving
      (fun x : Fin (n + N) → ℝ => ((fun j : Fin n => x (Fin.castAdd N j)),
        (fun i : Fin N => x (Fin.natAdd n i))))
      (Measure.pi fun _ : Fin (n + N) => gaussianReal 0 1)
      ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
  have h1 := (measurePreserving_piCongrLeft (α := fun _ : Fin (n + N) => ℝ)
    (fun _ : Fin (n + N) => gaussianReal 0 1) finSumFinEquiv).symm
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin N => ℝ)
    (fun _ => gaussianReal 0 1)
  have h3 := h2.comp h1
  convert h3 using 1
  funext x
  simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft_symm_apply]

private theorem gl_mp_row (n N : ℕ) :
    MeasurePreserving (fun H : Matrix (Fin 1) (Fin (n + N)) ℝ => H 0) (gaussianMatrix (Fin 1) (Fin (n + N)))
      (Measure.pi fun _ : Fin (n + N) => gaussianReal 0 1) :=
  measurePreserving_gaussianMatrix_row 0

/-- Integrating a function of the first coordinates of a Gaussian row gives the shorter vector expectation. -/
theorem integral_gaussianMatrix_row_castAdd (n N : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) :
    ∫ H, f (fun j => H 0 (Fin.castAdd N j)) ∂(gaussianMatrix (Fin 1) (Fin (n + N)))
      = ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have h := (measurePreserving_fst (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N => gaussianReal 0 1)).comp
      ((measurePreserving_gaussianVector_split n N).comp (gl_mp_row n N))
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hf.aestronglyMeasurable]
  rfl

/-- Integrating a function of the last coordinates of a Gaussian row gives the shorter vector expectation. -/
theorem integral_gaussianMatrix_row_natAdd (n N : ℕ) (f : (Fin N → ℝ) → ℝ) (hf : Measurable f) :
    ∫ H, f (fun i => H 0 (Fin.natAdd n i)) ∂(gaussianMatrix (Fin 1) (Fin (n + N)))
      = ∫ x, f x ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  have h := (measurePreserving_snd (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N => gaussianReal 0 1)).comp
      ((measurePreserving_gaussianVector_split n N).comp (gl_mp_row n N))
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hf.aestronglyMeasurable]
  rfl



end NLAlib
