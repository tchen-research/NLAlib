import NLAlib.ForMathlib.MeasureTheory.CompactExponential

/-!
# Finite atomic exponential representations

The weights are `exp (a i)` and the atom locations are `b i`. This is the
representing measure for a commuting Hermitian matrix pencil after simultaneous
diagonalization. Empty index types give the zero measure automatically.
Source: Stahl, *Proof of the BMV conjecture*, §1.3.1, formula (1.3).
Atlas: `trace-exponential-stahl` (commuting specialization).
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal

namespace NLAlib

variable {ι : Type*} [Fintype ι]

/-- The positive finite atomic measure with weight `exp (a i)` at `b i`.
Source: Stahl, formula (1.3); atlas `trace-exponential-stahl` (helper). -/
def exponentialAtomicMeasure (a b : ι → ℝ) : FiniteMeasure ℝ :=
  ⟨∑ i, Real.toNNReal (Real.exp (a i)) • Measure.dirac (b i),
    by infer_instance⟩

/-- Unfolding the atomic measure gives a finite sum of scaled Dirac measures.
Source: Stahl, formula (1.3); atlas `trace-exponential-stahl` (helper). -/
theorem exponentialAtomicMeasure_toMeasure (a b : ι → ℝ) :
    (exponentialAtomicMeasure a b : Measure ℝ) =
      ∑ i, ENNReal.ofReal (Real.exp (a i)) • Measure.dirac (b i) := by
  simp [exponentialAtomicMeasure, ENNReal.ofReal]

/-- Integrating any real function against these atoms gives its weighted sum.
No separate integrability premise is needed for a finite atomic measure.
Source: finite atomic integration; atlas `trace-exponential-stahl` (helper). -/
theorem integral_exponentialAtomicMeasure (a b : ι → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(exponentialAtomicMeasure a b : Measure ℝ)) =
      ∑ i, Real.exp (a i) * f (b i) := by
  rw [exponentialAtomicMeasure_toMeasure, integral_finsetSum_measure]
  · simp [integral_smul_measure, ENNReal.toReal_ofReal, (Real.exp_pos _).le]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Atoms inside `[l,u]` give a compactly supported exponential representation.
Source: Stahl, formula (1.3); atlas `trace-exponential-stahl` (commuting case). -/
theorem isCompactExpRepresentation_exponentialAtomicMeasure (a b : ι → ℝ)
    {l u : ℝ} (hb : ∀ i, b i ∈ Icc l u) :
    IsCompactExpRepresentation (exponentialAtomicMeasure a b)
      (fun t => ∑ i, Real.exp (a i + t * b i)) l u := by
  constructor
  · rw [exponentialAtomicMeasure_toMeasure, ae_finsetSum_measure_iff]
    intro i _
    exact Measure.ae_smul_measure (by simpa using hb i) _
  · intro t
    rw [integral_exponentialAtomicMeasure]
    simp only [Real.exp_add]

end NLAlib
