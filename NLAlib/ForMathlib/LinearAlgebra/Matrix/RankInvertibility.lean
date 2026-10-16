import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Full rank and matrix invertibility over a field

The reverse of `Matrix.rank_of_isUnit` follows from rank–nullity, over
any field. Empty square matrices are included.
-/
noncomputable section
namespace Matrix

/-- A square matrix of full rank is invertible, over an arbitrary field. -/
theorem isUnit_of_rank_eq_card {𝕜 n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕜) (hA : A.rank = Fintype.card n) : IsUnit A := by
  apply (Matrix.isUnit_iff_isUnit_det A).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hker : v ∈ LinearMap.ker A.mulVecLin := by simpa using hAv
  have hp : 0 < Module.finrank 𝕜 (LinearMap.ker A.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hker⟩, by simpa using hv⟩
  have hn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Matrix.rank] at hA
  simp only [Module.finrank_fintype_fun_eq_card] at hn
  omega

end Matrix
