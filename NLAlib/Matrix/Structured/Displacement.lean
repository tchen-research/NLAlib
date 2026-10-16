import NLAlib.Matrix.Basic.RankFactorization
import NLAlib.Matrix.Spectral.SylvesterQualitative

/-!
# Sylvester displacement generators

Low displacement rank is exactly the existence of generators of the requested
width. The definition uses the library's Sylvester linear map.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The Sylvester displacement rank of `X` with respect to the two operators. -/
def displacementRank {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m K) (B : Matrix n n K)
    (X : Matrix m n K) : ℕ := (sylvesterLinearMap A B X).rank

/-- Sylvester displacement rank at most `r` is equivalent to a generator pair
with `r` columns. This includes zero rank and empty row or column types.
Source: user derivations, displacement generators.
atlas: displacement-rank-def -/
theorem displacementRank_le_iff_exists_generators {K m n : Type*} [RCLike K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix n n K) (X : Matrix m n K) (r : ℕ) :
    displacementRank A B X ≤ r ↔
      ∃ (M : Matrix m (Fin r) K) (N : Matrix n (Fin r) K), A * X - X * B = M * Nᴴ :=
  rank_le_iff_exists_mul_conjTranspose (A * X - X * B) r

end NLAlib
