import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.RCLike.Basic

/-!
# Rank factorizations with a prescribed generator size

A matrix of rank at most `r` factors through `Fin r`, including empty matrices
and `r = 0`. This is the algebraic generator construction used by displacement
and hierarchical matrix representations.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- A rank bound is equivalent to a factorization through the requested number
of columns; unused coordinates are permitted. -/
theorem rank_le_iff_exists_mul {K m n : Type*} [Field K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n K) (r : ℕ) :
    A.rank ≤ r ↔ ∃ (M : Matrix m (Fin r) K) (N : Matrix (Fin r) n K), A = M * N := by
  classical
  constructor
  · intro h
    have hdim : Module.finrank K (LinearMap.range A.mulVecLin) ≤
        Module.finrank K (Fin r → K) := by simpa [Matrix.rank] using h
    obtain ⟨e, he⟩ := finrank_le_iff_exists_linearMap.mp hdim
    obtain ⟨l, hl⟩ := e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr he)
    let f := (LinearMap.range A.mulVecLin).subtype.comp l
    let g := e.comp A.mulVecLin.rangeRestrict
    refine ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g, ?_⟩
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    funext i
    exact (congrArg (fun z : LinearMap.range A.mulVecLin => z.val i)
      (DFunLike.congr_fun hl (A.mulVecLin.rangeRestrict x))).symm
  · rintro ⟨M, N, rfl⟩
    exact (Matrix.rank_mul_le_left M N).trans (by simpa using M.rank_le_card_width)

/-- Complex or real generators use a conjugate transpose on the right.
Source: the low-rank generator characterization of Sylvester displacement.
atlas: displacement-rank-def (partial) -/
theorem rank_le_iff_exists_mul_conjTranspose {K m n : Type*} [RCLike K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n K) (r : ℕ) :
    A.rank ≤ r ↔ ∃ (M : Matrix m (Fin r) K) (N : Matrix n (Fin r) K), A = M * Nᴴ := by
  constructor
  · rintro h
    obtain ⟨M, N, hMN⟩ := (rank_le_iff_exists_mul A r).mp h
    exact ⟨M, Nᴴ, by simpa using hMN⟩
  · rintro ⟨M, N, hMN⟩
    exact (rank_le_iff_exists_mul A r).mpr ⟨M, Nᴴ, hMN⟩

end NLAlib
