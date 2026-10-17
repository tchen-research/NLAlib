import NLAlib.Matrix.Functions.TraceExponentialContourPositivity
import NLAlib.Matrix.Functions.TraceExponentialSimpleSpectrumLimit

/-!
# Positive-measure representation of the trace exponential

Stahl's theorem for arbitrary finite Hermitian matrices: the trace exponential
of an affine Hermitian pencil is the exponential transform of a finite positive
Borel measure supported on the exact spectral interval of its direction.
The proof combines the planar upper-root-sum positivity argument, the explicit
atom-plus-density identity, and compactness within the original spectral interval.
Source: Stahl, *Proof of the BMV conjecture*, Theorems 1 and 2; Eremenko's
exposition, reorganized using the planar root-sum argument.
-/

noncomputable section

open MeasureTheory
open scoped Matrix

namespace NLAlib

/-- Every finite Hermitian pencil has a finite positive representing measure
supported on the direction's exact spectral interval, with the trace-exponential
identity valid for every real parameter. No commutation, simple-spectrum, or
positive-definiteness hypothesis is required. Empty dimension gives the zero
measure through the commuting specialization.
Source: Stahl (2013), Theorems 1 and 2, via the planar root-sum proof.
atlas: trace-exponential-stahl -/
theorem exists_isCompactExpRepresentation_traceExp
    {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => traceExp (A + t • H)) (lambdaMin H) (lambdaMax H) := by
  apply exists_isCompactExpRepresentation_traceExp_of_diagonal_simple A H hA hH
  intro C hC b hb l u hlu hbu
  have heq (t : ℝ) : C + t • Matrix.diagonal (fun i => (b i : ℂ)) =
      C + (t : ℂ) • Matrix.diagonal (fun i => (b i : ℂ)) := by
    congr 1
  simpa only [heq] using
    exists_isCompactExpRepresentation_traceExp_diagonal_of_injective hC b hb hlu hbu

/-- Stahl's representation together with its total mass, every tilted-moment
derivative identity, and both spectral-endpoint bounds on even derivatives.
This is the full statement of the library card, with no representation premise.
Source: Stahl (2013), Theorems 1 and 2; Tropp (2026), Proposition 4.4.
atlas: trace-exponential-stahl -/
theorem exists_isCompactExpRepresentation_traceExp_with_derivatives
    {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) :
    ∃ ν : FiniteMeasure ℝ,
      IsCompactExpRepresentation ν (fun t : ℝ => traceExp (A + t • H))
        (lambdaMin H) (lambdaMax H) ∧
      (ν : Measure ℝ).real Set.univ = traceExp A ∧
      (∀ k : ℕ, ∀ t : ℝ,
        iteratedDeriv k (fun x : ℝ => traceExp (A + x • H)) t =
          ∫ x, x ^ k * Real.exp (t * x) ∂(ν : Measure ℝ)) ∧
      ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t →
        0 ≤ Real.exp (t * lambdaMin H) *
          iteratedDeriv (2 * r) (fun x : ℝ => traceExp (A + x • H)) 0 ∧
        Real.exp (t * lambdaMin H) *
          iteratedDeriv (2 * r) (fun x : ℝ => traceExp (A + x • H)) 0 ≤
          iteratedDeriv (2 * r) (fun x : ℝ => traceExp (A + x • H)) t ∧
        iteratedDeriv (2 * r) (fun x : ℝ => traceExp (A + x • H)) t ≤
          Real.exp (t * lambdaMax H) *
            iteratedDeriv (2 * r) (fun x : ℝ => traceExp (A + x • H)) 0 := by
  obtain ⟨ν, hν⟩ := exists_isCompactExpRepresentation_traceExp A H hA hH
  refine ⟨ν, hν, ?_, hν.iteratedDeriv_eq_integral, ?_⟩
  · simpa only [zero_smul, add_zero] using hν.measureReal_univ_eq
  · intro r t ht
    exact ⟨mul_nonneg (Real.exp_pos _).le (hν.iteratedDeriv_even_nonneg r 0),
      hν.exp_mul_iteratedDeriv_even_zero_le r ht, hν.iteratedDeriv_even_le_exp_mul_zero r ht⟩

end NLAlib
