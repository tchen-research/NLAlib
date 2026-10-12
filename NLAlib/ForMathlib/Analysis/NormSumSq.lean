import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Group.Basic

/-!
# The squared norm of a finite sum

`‖∑ a ∈ s, z a‖ ^ 2 ≤ #s * ∑ a ∈ s, ‖z a‖ ^ 2` in any seminormed additive group
(`norm_sum_sq_le_card_mul_sum_norm_sq`): the triangle inequality followed by the Cauchy--Schwarz
bound `sq_sum_le_card_mul_sum_sq` on the norms.

Source: generalises `SparseFockFormal.DirectionalConcrete.normSq_sum_le_card` (stated there for
Euclidean coordinates), commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

set_option autoImplicit false
open scoped BigOperators
namespace NLAlib

/-- The squared norm of a finite sum is at most the number of terms times the sum of the squared
norms.

Source: generalises `SparseFockFormal.DirectionalConcrete.normSq_sum_le_card`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {α E : Type*} [SeminormedAddCommGroup E]
    (s : Finset α) (z : α → E) :
    ‖∑ a ∈ s, z a‖ ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, ‖z a‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s z) 2).trans sq_sum_le_card_mul_sum_sq

end NLAlib
