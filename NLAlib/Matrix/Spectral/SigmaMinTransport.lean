import NLAlib.Matrix.Spectral.SpectralBounds
import NLAlib.Matrix.Spectral.SingularValueInvariance
import NLAlib.Matrix.Basic.Gram
/-!
# The smallest singular value of square matrices

For a nonempty square real matrix the variational smallest singular value is invariant under
transposition (`sigmaMin_transpose_eq`) and is positive exactly when the matrix is invertible
(`sigmaMin_pos_iff_isUnit_of_nonempty`). Both follow from the identification of `sigmaMin`
with the last native singular value (`sigmaMin_eq_singularValues_last`, in `SpectralBounds`).
Source: Horn--Johnson, Section 2.6; supports `principal-angles-def` and
`ostrowski-congruence-eigenvalues`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The smallest singular value of a nonempty square matrix is preserved
by transposition. Singular-value invariance; helper for
`ostrowski-congruence-eigenvalues`. -/
theorem sigmaMin_transpose_eq (S : Matrix n n ℝ) (hn : 0 < Fintype.card n) :
    sigmaMin Sᵀ = sigmaMin S := by
  rw [sigmaMin_eq_singularValues_last Sᵀ hn, sigmaMin_eq_singularValues_last S hn,
    singularValues_transpose]

/-- A nonempty square real matrix has positive variational minimum exactly
when it is invertible. Empty squares are handled separately by consumers.
Horn--Johnson, Section 2.6; supports `principal-angles-def`. -/
theorem sigmaMin_pos_iff_isUnit_of_nonempty [Nonempty n] (C : Matrix n n ℝ) :
    0 < sigmaMin C ↔ IsUnit C := by
  rw [sigmaMin_pos_iff_rank_eq_width C Fintype.card_pos]
  exact ⟨fun hRank => (Matrix.isUnit_iff_isUnit_det C).mpr
    (isUnit_iff_ne_zero.mpr (det_ne_zero_of_rank_eq C hRank)), Matrix.rank_of_isUnit C⟩

end NLAlib
