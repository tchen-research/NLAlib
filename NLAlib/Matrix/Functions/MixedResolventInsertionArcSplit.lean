import NLAlib.Matrix.Functions.MixedResolventArcSplit
import NLAlib.Matrix.Functions.MixedResolventHessian

/-! # Positive-arc form of the actual cyclic trace insertion

Finite distributivity puts the two genuine derivative insertion sums into
the exact coefficient sandwich form used by Gaussian covariance.
Source: arXiv:2108.06312v2, Lemmas 6.2--6.3.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib
open scoped Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The actual cyclic mixed-trace derivative insertion is precisely its
finite positive-arc coefficient sandwich sum; no coefficient commutation
or extra derivative identity is assumed. -/
theorem mixedResolventTraceInsertion_eq_sum_split
    (X H : Matrix d d ℂ) (ζ : ℂ) (a b : ℕ) :
    mixedResolventTraceInsertion X H H ζ (star ζ) a b =
      ∑ j : Fin (a + b), normalizedTrace
        (H * (resolvent X ζ ^ (mixedResolventSplitLeft a b j).1 *
          resolvent X (star ζ) ^ (mixedResolventSplitLeft a b j).2) * H *
            (resolvent X ζ ^ (mixedResolventSplitRight a b j).1 *
              resolvent X (star ζ) ^ (mixedResolventSplitRight a b j).2)) := by
  have h := congrArg (fun U : Matrix d d ℂ => normalizedTrace (H * U))
    (mixed_power_insertion_sum_eq_sum_split (resolvent X ζ) (resolvent X (star ζ)) H a b)
  simpa only [mixedResolventTraceInsertion, Matrix.mul_add, Finset.mul_sum,
    normalizedTrace, Matrix.trace_add, Matrix.trace_sum, mul_add,
    Finset.mul_sum, Matrix.mul_assoc] using h

end NLAlib
