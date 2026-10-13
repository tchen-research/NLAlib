import NLAlib.Sketching.Sparse.FiniteLaw.Uniform
import NLAlib.ForMathlib.Probability.PMF
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.HasLaw

/-!
# Native probability measures for the explicit finite-law proof interface

The finite weighted-sum interface ported from the sparse-Fock proof is
identified with Mathlib's actual PMFs and measures. Its expectations are
genuine Bochner integrals and its event probabilities are measure masses.
Source: pinned sparse-Fock artifact b9da2b5d96e5fd70252e9c6551aefc92643e7d0b;
supports `sparse-ose`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib.SparseSketch.FiniteLaw

variable {α : Type*} [Fintype α]

/-- The native Mathlib PMF with precisely the finite law's nonnegative
normalized weights. Source: finite-law bridge for the pinned sparse-Fock
artifact; supports `sparse-ose`. -/
def toPMF (μ : FiniteLaw α) : PMF α :=
  PMF.ofFintype (fun x => ENNReal.ofReal (μ.weight x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => μ.weight_nonneg x),
      μ.sum_weight, ENNReal.ofReal_one])

/-- The native PMF has the original finite law's exact pointwise mass.
Source: the explicit PMF construction; supports `sparse-ose`. -/
@[simp] theorem toPMF_apply (μ : FiniteLaw α) (x : α) :
    μ.toPMF x = ENNReal.ofReal (μ.weight x) := rfl

/-- View a native finite PMF through the finite-sum proof interface. No new law is chosen. -/
def ofPMF (p : PMF α) : FiniteLaw α where
  weight x := (p x).toReal
  weight_nonneg _ := ENNReal.toReal_nonneg
  sum_weight := p.sum_toReal

/-- Returning to native probability preserves the original PMF. -/
@[simp] theorem toPMF_ofPMF (p : PMF α) : (ofPMF p).toPMF = p := by
  ext x
  exact ENNReal.ofReal_toReal (p.apply_ne_top x)

/-- Returning to the finite-sum interface preserves the original weights. -/
@[simp] theorem ofPMF_toPMF (μ : FiniteLaw α) : ofPMF μ.toPMF = μ := by
  have h : (ofPMF μ.toPMF).weight = μ.weight := by
    funext x
    exact ENNReal.toReal_ofReal (μ.weight_nonneg x)
  exact ext_weight h

/-- The actual probability measure specified by the explicit finite law.
Source: the native PMF bridge; supports `sparse-ose`. -/
def toMeasure [MeasurableSpace α] (μ : FiniteLaw α) : Measure α :=
  μ.toPMF.toMeasure

/-- The bridge produces a normalized probability measure.
Source: Mathlib's PMF normalization; supports `sparse-ose`. -/
instance toMeasure_isProbabilityMeasure [MeasurableSpace α]
    (μ : FiniteLaw α) : IsProbabilityMeasure μ.toMeasure := by
  unfold toMeasure
  infer_instance

/-- Every finite-law expectation is the actual Bochner integral under its
native measure. Source: PMF finite integration; supports `sparse-ose`. -/
theorem integral_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : FiniteLaw α) (f : α → ℝ) :
    (∫ x, f x ∂μ.toMeasure) = μ.expect f := by
  rw [toMeasure, PMF.integral_eq_sum]
  simp only [toPMF_apply, ENNReal.toReal_ofReal (μ.weight_nonneg _), smul_eq_mul, FiniteLaw.expect]

/-- The finite law's event probability is the real mass under its actual
native probability measure. Source: PMF finite integration and indicators;
supports `sparse-ose`. -/
theorem real_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : FiniteLaw α) (s : Set α) :
    μ.toMeasure.real s = μ.prob s := by
  have hs : MeasurableSet s := s.toFinite.measurableSet
  rw [← integral_indicator_one hs, integral_toMeasure, prob]
  congr 1

/-- A random variable with the finite law has precisely its event masses,
on an arbitrary underlying measurable space. Source: Mathlib's pushforward
measure identity and the finite PMF bridge; supports `sparse-ose`. -/
theorem real_preimage_of_hasLaw
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : FiniteLaw α)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Z : Ω → α) (hlaw : HasLaw Z ν.toMeasure μ) (s : Set α) :
    μ.real (Z ⁻¹' s) = ν.prob s := by
  rw [← real_toMeasure]
  exact hlaw.measureReal_eq s.toFinite.measurableSet

end NLAlib.SparseSketch.FiniteLaw
