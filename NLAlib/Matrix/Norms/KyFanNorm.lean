import Mathlib.Analysis.InnerProductSpace.SingularValues
import NLAlib.Matrix.Inequalities.MajorizationProperties

/-!
# Ky Fan norms and the nuclear norm

Definitions only, over `ℝ` or `ℂ` (any `[RCLike 𝕜]`).

* `NLAlib.kyFanNorm A k`: the sum of the `k` largest singular values of `A`, defined as
  `sumLargest` of the singular-value vector of length `min (card m) (card n)`; since
  `singularValues` is sorted and zero-padded this is the prefix sum
  `∑ i < k, singularValues A i` for every `k` (`kyFanNorm_eq_sum_range`);
* `NLAlib.nuclearNorm A`: the sum of all singular values, `kyFanNorm A (min m n)`.

Both are real-valued for every `𝕜`. The norm axioms, the Ky Fan maximum principle and the
duality with the spectral norm are in `NLAlib.Matrix.Inequalities.KyFan` and
`NLAlib.Matrix.Norms.NuclearNorm`. Source: Horn–Johnson (1991), §3.4. Atlas: `ky-fan-norms-def`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The Ky Fan `k`-norm of a matrix over `ℝ` or `ℂ`: the sum of its `k` largest singular values
(`sumLargest` of the singular-value vector). For `1 ≤ k ≤ min m n` it is a norm; at `k = 0` it is
the zero seminorm, and for `k ≥ min m n` it is the nuclear norm. Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def -/
def kyFanNorm (A : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  sumLargest (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i) k

/-- The nuclear norm of a matrix over `ℝ` or `ℂ` is the sum of all singular values (the Ky Fan
norm at `k = min m n`), including matrices with an empty dimension. Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def -/
def nuclearNorm (A : Matrix m n 𝕜) : ℝ :=
  kyFanNorm A (min (Fintype.card m) (Fintype.card n))

/-- The Ky Fan `k`-norm is the prefix sum of the sorted, zero-padded singular values, for every
`k` (beyond `min m n` the padded values are `0`). -/
theorem kyFanNorm_eq_sum_range (A : Matrix m n 𝕜) (k : ℕ) :
    kyFanNorm A k = ∑ i ∈ Finset.range k, singularValues A i := by
  set N := min (Fintype.card m) (Fintype.card n) with hN
  rw [kyFanNorm, sumLargest_eq_prefix_of_antitone _ (fun i j hij => singularValues_antitone A hij),
    show (∑ i : Fin N, if (i : ℕ) < k then singularValues A i else 0) =
      ∑ i ∈ Finset.range N, (if i < k then singularValues A i else 0) from
      Fin.sum_univ_eq_sum_range (fun i => if i < k then singularValues A i else 0) N,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilt : (Finset.range N).filter (fun i => i < k) = Finset.range (min N k) := by
    ext i; simp [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  rw [hfilt]
  symm
  apply Finset.sum_subset (Finset.range_mono (min_le_right _ _))
  intro i hi hni
  simp only [Finset.mem_range, lt_min_iff, not_and] at hi hni
  exact singularValues_eq_zero_of_min_le A (by rw [← hN]; exact not_lt.mp (hni hi))

/-- The nuclear norm is the sum of the first `min m n` singular values. -/
theorem nuclearNorm_eq_sum_range (A : Matrix m n 𝕜) :
    nuclearNorm A = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i :=
  kyFanNorm_eq_sum_range A _

end NLAlib
