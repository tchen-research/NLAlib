/- Copyright (c) 2026 Diar Heidary. Adapted under the MIT license. -/
import NLAlib.Matrix.Norms
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Spectral norm and symmetric quadratic forms

Atlas: `ose-def`, `norms-frob-spec`. The Rayleigh quotient argument is adapted
from `SparseFock.MatrixTail.opNorm_le_iff_quadraticForm` in
Nelson-Nguyen-conjecture-upper-bound-palomar, commit
`3fdbf2cbb26c10c18bc799fa63fbd3a768f6f0e2` (MIT, Diar Heidary).
Only Mathlib and NLAlib are imported; the donor probability development is
not needed. All finite index types, including empty types, are covered.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real symmetric matrix has spectral norm at most a nonnegative `ε`
exactly when its quadratic form is bounded by `ε ‖x‖²` for every vector.
Atlas: `ose-def`, `norms-frob-spec`. Adapted from the MIT-licensed donor
`SparseFock.MatrixTail.opNorm_le_iff_quadraticForm`, commit
`3fdbf2cbb26c10c18bc799fa63fbd3a768f6f0e2`. -/
theorem specNorm_le_iff_abs_dotProduct_mulVec_le (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (ε : ℝ) (hε : 0 ≤ ε) :
    specNorm A ≤ ε ↔ ∀ x : n → ℝ, |x ⬝ᵥ (A *ᵥ x)| ≤ ε * (x ⬝ᵥ x) := by
  constructor
  · intro h x
    exact (abs_dotProduct_mulVec_le_specNorm A x).trans
      (mul_le_mul_of_nonneg_right h (dotProduct_self_nonneg x))
  · intro hquad
    let T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
      Matrix.toEuclideanCLM (𝕜 := ℝ) A
    have hT : (T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n).IsSymmetric := by
      change (Matrix.toEuclideanLin A).IsSymmetric
      exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    change ‖T‖ ≤ ε
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hε
    · have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      rw [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, abs_div,
        abs_of_nonneg hxpos.le]
      apply (div_le_iff₀ hxpos).2
      have hnorm : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [dotProduct, sq]
      simpa [T, real_inner_comm, Matrix.inner_toEuclideanCLM,
        hnorm] using hquad x.ofLp

end NLAlib
