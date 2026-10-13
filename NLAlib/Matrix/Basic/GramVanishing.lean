import Mathlib.Analysis.Matrix.Order

/-!
# Vanishing rows of positive semidefinite matrices

* A zero diagonal entry of a positive semidefinite matrix over `ℝ` or `ℂ` (any `RCLike` field)
  kills its column and its row (`apply_eq_zero_of_posSemidef_of_apply_self_eq_zero` and its
  primed row version). This handles zero pivots in the Cholesky recursion and zero-probability
  pivots in finite Cholesky transition sums.
* A matrix of rank zero over a field is zero (`eq_zero_of_matrix_rank_eq_zero`).
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib

section ZeroDiagonal

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

/-- A zero diagonal entry of a positive semidefinite matrix kills its column: `aᵢᵢ = 0` gives
`aⱼᵢ = 0` for every `j` (from `eᵢᴴ A eᵢ = 0 ⟹ A eᵢ = 0`,
`Matrix.PosSemidef.dotProduct_mulVec_zero_iff`). Stated over any `RCLike` field (real and complex
matrices). Horn–Johnson 2013, Obs. 7.1.10. -/
theorem apply_eq_zero_of_posSemidef_of_apply_self_eq_zero {A : Matrix m m 𝕜}
    (hA : A.PosSemidef) {i : m} (h : A i i = 0) (j : m) : A j i = 0 := by
  have h0 : star (Pi.single i 1 : m → 𝕜) ⬝ᵥ A *ᵥ Pi.single i 1 = 0 := by
    simp [h]
  have := congrFun ((hA.dotProduct_mulVec_zero_iff _).1 h0) j
  simpa using this

/-- A zero diagonal entry of a positive semidefinite matrix kills its row. -/
theorem apply_eq_zero_of_posSemidef_of_apply_self_eq_zero' {A : Matrix m m 𝕜}
    (hA : A.PosSemidef) {i : m} (h : A i i = 0) (j : m) : A i j = 0 := by
  have hs : A i j = star (A j i) := by
    have := congrFun (congrFun hA.isHermitian i) j
    simpa using this.symm
  rw [hs, apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hA h j, star_zero]

end ZeroDiagonal

/-- A finite matrix of rank zero over a field is zero (`rank = finrank (range)`). -/
theorem eq_zero_of_matrix_rank_eq_zero {K : Type*} [Field K] {m n : Type*} [Fintype m]
    [Fintype n] {R : Matrix m n K} (hR : R.rank = 0) : R = 0 := by
  have hrange : LinearMap.range R.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hR
  ext i j
  have hj : R.col j ∈ LinearMap.range R.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  rw [hrange, Submodule.mem_bot] at hj
  exact congrFun hj i

end NLAlib
