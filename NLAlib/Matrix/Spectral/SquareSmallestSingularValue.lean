import NLAlib.Matrix.Spectral.SpectralBounds
/-!
# The smallest singular value of a square matrix

For a square matrix on a nonempty index type the last singular value
`singularValues C (card n - 1)` is positive exactly when the matrix is invertible
(`singularValues_last_pos_iff_isUnit`). Source: Horn–Johnson 2013, §2.6; supports
`principal-angles-def` and `ostrowski-congruence-eigenvalues`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A square matrix on a nonempty index type has positive smallest singular value exactly when it
is invertible. Horn–Johnson 2013, §2.6. -/
theorem singularValues_last_pos_iff_isUnit [Nonempty n] (C : Matrix n n 𝕜) :
    0 < singularValues C (Fintype.card n - 1) ↔ IsUnit C := by
  rw [singularValues_last_pos_iff_rank_eq_card C Fintype.card_pos]
  refine ⟨fun hRank => ?_, Matrix.rank_of_isUnit C⟩
  refine (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr fun hdet => ?_)
  obtain ⟨v, hv, hCv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hrn := LinearMap.finrank_range_add_finrank_ker C.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hr : Module.finrank 𝕜 (LinearMap.range C.mulVecLin) = Fintype.card n := hRank
  have hker : Module.finrank 𝕜 (LinearMap.ker C.mulVecLin) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hker
  have hmem : v ∈ LinearMap.ker C.mulVecLin := by simpa [LinearMap.mem_ker] using hCv
  rw [hker, Submodule.mem_bot] at hmem
  exact hv hmem

end NLAlib
