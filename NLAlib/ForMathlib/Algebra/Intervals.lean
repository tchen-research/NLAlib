import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.Ring

/-!
# Alternating affine sums on even ranges

Pairing adjacent signs in a finite range gives the exact scalar sum used in the sawtooth
square-wave integral for sharp Jackson.
-/

noncomputable section

open Finset

namespace NLAlib

/-- Pairing consecutive signs sums an affine sequence exactly:
`∑_{j<2N} (-1)^j(α-(j+1/2)β)=Nβ`.
Source: the finite calculation in operator rederivations `rt:sawtooth`;
general finite-sum helper for `jackson-lipschitz`. -/
theorem sum_alternating_affine_two_mul {R : Type*} [Field R] (N : ℕ) (α β : R) :
    (∑ j ∈ range (2 * N), (-1 : R) ^ j * (α - ((j : R) + 1 / 2) * β)) = (N : R) * β := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega, sum_range_succ, sum_range_succ, ih]
    have heven : (-1 : R) ^ (2 * N) = 1 := by rw [pow_mul]; norm_num
    have hodd : (-1 : R) ^ (2 * N + 1) = -1 := by rw [pow_succ, heven]; norm_num
    rw [heven, hodd]
    push_cast
    ring

end NLAlib
