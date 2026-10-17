import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import NLAlib.ForMathlib.MeasureTheory.CompactLaplaceLimit

/-!
# Compactly supported positive exponential representations

The measure in this interface is an finite positive Borel measure. The
interface does not assert that a given function admits such a measure. Once a
representation is constructed, its mass, derivatives and even-derivative bounds
follow from Mathlib's moment-generating-function calculus.

Source: Stahl, *Proof of the BMV conjecture*, Theorems 1–2 and compact-support
differentiation. Atlas: `trace-exponential-stahl` (consequences only).
-/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped Topology

namespace NLAlib

/-- An finite positive measure represents `F` by exponentials and is
concentrated on `[a,b]`. This records a representation, not its existence.
Source: Stahl, Theorems 1–2; atlas `trace-exponential-stahl` (interface). -/
structure IsCompactExpRepresentation (ν : FiniteMeasure ℝ) (F : ℝ → ℝ) (a b : ℝ) : Prop where
  /-- The representing measure is concentrated on the specified interval.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
  ae_mem_Icc : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc a b
  /-- The exponential transform is the represented function at every real parameter.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
  integral_exp : ∀ t : ℝ, (∫ x, Real.exp (t * x) ∂(ν : Measure ℝ)) = F t

namespace IsCompactExpRepresentation

variable {ν : FiniteMeasure ℝ} {F : ℝ → ℝ} {a b : ℝ}
variable (h : IsCompactExpRepresentation ν F a b)
include h

/-- Compact support gives exponential integrability at every real parameter.
Source: boundedness on an interval; atlas `trace-exponential-stahl` (helper). -/
theorem integrable_exp (t : ℝ) :
    Integrable (fun x => Real.exp (t * x)) (ν : Measure ℝ) :=
  integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable h.ae_mem_Icc

/-- The full real line lies in the interior of the exponential-integrability set.
Source: compact support; atlas `trace-exponential-stahl` (helper). -/
theorem mem_interior_integrableExpSet (t : ℝ) :
    t ∈ interior (integrableExpSet (id : ℝ → ℝ) (ν : Measure ℝ)) := by
  have heq : integrableExpSet (id : ℝ → ℝ) (ν : Measure ℝ) = univ := by
    ext s
    simp only [mem_univ, iff_true]
    exact h.integrable_exp s
  simp [heq]

/-- Evaluation at zero identifies the total mass, including the zero measure.
Source: Stahl, Theorems 1–2; atlas `trace-exponential-stahl` (consequence). -/
theorem measureReal_univ_eq : (ν : Measure ℝ).real univ = F 0 := by
  simpa using h.integral_exp 0

/-- Every derivative is the corresponding exponentially tilted moment. No
probability normalization is required. Source: compact-support differentiation
in Stahl's representation; atlas `trace-exponential-stahl` (consequence).
atlas: trace-exponential-stahl (partial) -/
theorem iteratedDeriv_eq_integral (k : ℕ) (t : ℝ) :
    iteratedDeriv k F t = ∫ x, x ^ k * Real.exp (t * x) ∂(ν : Measure ℝ) := by
  have heq : F = mgf (id : ℝ → ℝ) (ν : Measure ℝ) := by
    funext s
    exact (h.integral_exp s).symm
  rw [heq]
  exact iteratedDeriv_mgf (h.mem_interior_integrableExpSet t) k

/-- The moment integrands are integrable for every derivative order and real
parameter. Source: compact support; atlas `trace-exponential-stahl` (helper). -/
theorem integrable_pow_mul_exp (k : ℕ) (t : ℝ) :
    Integrable (fun x => x ^ k * Real.exp (t * x)) (ν : Measure ℝ) :=
  integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (h.mem_interior_integrableExpSet t) k

/-- All even derivatives of a positive exponential representation are nonnegative.
Source: Stahl's representation; atlas `trace-exponential-stahl` (consequence). -/
theorem iteratedDeriv_even_nonneg (r : ℕ) (t : ℝ) :
    0 ≤ iteratedDeriv (2 * r) F t := by
  rw [h.iteratedDeriv_eq_integral]
  apply integral_nonneg
  intro x
  exact mul_nonneg ((even_two_mul r).pow_nonneg x) (Real.exp_pos _).le

/-- For nonnegative time the lower support endpoint bounds every even derivative
from below. Source: Stahl's representation; atlas `trace-exponential-stahl`
(consequence).
atlas: trace-exponential-stahl (partial) -/
theorem exp_mul_iteratedDeriv_even_zero_le (r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (t * a) * iteratedDeriv (2 * r) F 0 ≤ iteratedDeriv (2 * r) F t := by
  rw [h.iteratedDeriv_eq_integral, h.iteratedDeriv_eq_integral]
  simp only [zero_mul, Real.exp_zero, mul_one]
  rw [← integral_const_mul]
  apply integral_mono_ae
    (((h.integrable_pow_mul_exp (2 * r) 0).congr (by simp)).const_mul _)
    (h.integrable_pow_mul_exp (2 * r) t)
  filter_upwards [h.ae_mem_Icc] with x hx
  have hp : 0 ≤ x ^ (2 * r) := (even_two_mul r).pow_nonneg x
  have he : Real.exp (t * a) ≤ Real.exp (t * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.1 ht)
  nlinarith

/-- For nonnegative time the upper support endpoint bounds every even derivative
from above. Source: Stahl's representation; atlas `trace-exponential-stahl`
(consequence).
atlas: trace-exponential-stahl (partial) -/
theorem iteratedDeriv_even_le_exp_mul_zero (r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv (2 * r) F t ≤ Real.exp (t * b) * iteratedDeriv (2 * r) F 0 := by
  rw [h.iteratedDeriv_eq_integral, h.iteratedDeriv_eq_integral]
  simp only [zero_mul, Real.exp_zero, mul_one]
  rw [← integral_const_mul]
  apply integral_mono_ae (h.integrable_pow_mul_exp (2 * r) t)
    (((h.integrable_pow_mul_exp (2 * r) 0).congr (by simp)).const_mul _)
  filter_upwards [h.ae_mem_Icc] with x hx
  have hp : 0 ≤ x ^ (2 * r) := (even_two_mul r).pow_nonneg x
  have he : Real.exp (t * x) ≤ Real.exp (t * b) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 ht)
  nlinarith

/-- The represented function is real analytic at every real parameter.
Source: compact-support exponential integrability and Mathlib's analytic MGF
theorem; atlas `trace-exponential-stahl` (consequence). -/
theorem analyticAt (t : ℝ) : AnalyticAt ℝ F t := by
  have heq : F = mgf (id : ℝ → ℝ) (ν : Measure ℝ) := by
    funext s
    exact (h.integral_exp s).symm
  rw [heq]
  exact analyticAt_mgf (h.mem_interior_integrableExpSet t)

/-- Widening the support interval preserves an representation.
Source: monotonicity of concentration; atlas `trace-exponential-stahl` (helper). -/
theorem mono {c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    IsCompactExpRepresentation ν F c d := by
  refine ⟨?_, h.integral_exp⟩
  filter_upwards [h.ae_mem_Icc] with x hx
  exact ⟨hca.trans hx.1, hx.2.trans hbd⟩

end IsCompactExpRepresentation

/-- Limits of functions with positive exponential representations on a common
compact interval have a positive representation on that interval. Mass bounds
follow from convergence at zero, rather than being added as hypotheses.
Source: Stahl's compactness reduction; atlas `trace-exponential-stahl` (partial). -/
theorem exists_isCompactExpRepresentation_of_tendsto
    {I : Type*} {l : Filter I} [l.NeBot] (a b : ℝ)
    (F : I → ℝ → ℝ) (f : ℝ → ℝ)
    (hrep : ∀ᶠ i in l, ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν (F i) a b)
    (hlim : ∀ t, Filter.Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν f a b := by
  have hrep' : ∀ᶠ i in l, ∃ ν : FiniteMeasure ℝ,
      (∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc a b) ∧
        ∀ t, (∫ x, Real.exp (t * x) ∂(ν : Measure ℝ)) = F i t := by
    filter_upwards [hrep] with i hi
    obtain ⟨ν, hν⟩ := hi
    exact ⟨ν, hν.ae_mem_Icc, hν.integral_exp⟩
  obtain ⟨ν, hsupp, heq⟩ := exists_finiteMeasure_exp_mul_eq_of_tendsto a b F f hrep' hlim
  exact ⟨ν, hsupp, heq⟩
end NLAlib
