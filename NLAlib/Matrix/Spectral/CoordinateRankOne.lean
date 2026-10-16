import NLAlib.Matrix.Spectral.ThinSingularFunctions
import NLAlib.Matrix.Subspaces.CoordinateFrames
import NLAlib.Matrix.Spectral.SpectralBounds

/-! # Coordinate rank-one matrices and their actual singular values

Every positive scalar is realized by an actual rank-one matrix in any fixed
nonempty rectangular shape. Source: Horn–Johnson, §7.3.
-/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

/-- A rank-one matrix in a single coordinate, with literal coordinate singular vectors. -/
def coordinateRankOneMatrix (i₀ : m) (j₀ : n) (x : ℝ) : Matrix m n 𝕜 :=
  thinSingularMatrix (coordinateColumn i₀) (coordinateColumn j₀) (fun _ : Unit => x)

/-- The coordinate rank-one witness has its prescribed positive singular value. -/
theorem isThinSVD_coordinateRankOneMatrix (i₀ : m) (j₀ : n) {x : ℝ} (hx : 0 < x) :
    IsThinSVD (coordinateRankOneMatrix (𝕜 := 𝕜) i₀ j₀ x) (coordinateColumn i₀)
      (coordinateColumn j₀) (fun _ : Unit => x) :=
  ⟨hasOrthonormalCols_coordinateColumn i₀, hasOrthonormalCols_coordinateColumn j₀,
    fun _ => hx, rfl⟩

open scoped Matrix.Norms.L2Operator in
/-- Every actual positive singular value of the coordinate rank-one matrix
is exactly the prescribed scalar. -/
theorem singularValues_coordinateRankOneMatrix_of_pos (i₀ : m) (j₀ : n)
    {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < singularValues (coordinateRankOneMatrix (𝕜 := 𝕜) i₀ j₀ x) k) :
    singularValues (coordinateRankOneMatrix (𝕜 := 𝕜) i₀ j₀ x) k = x := by
  have ht := isThinSVD_coordinateRankOneMatrix (𝕜 := 𝕜) i₀ j₀ hx
  have hr : (coordinateRankOneMatrix (𝕜 := 𝕜) i₀ j₀ x).rank = 1 := by
    simpa using ht.rank_eq_card
  have hkr := (singularValues_pos_iff _ _).mp hk
  have hzero : k = 0 := by omega
  subst k
  rw [singularValues_zero_eq_specNorm, coordinateRankOneMatrix,
    specNorm_thinSingularMatrix _ _ (hasOrthonormalCols_coordinateColumn i₀)
      (hasOrthonormalCols_coordinateColumn j₀), pi_norm_const, Real.norm_eq_abs,
    abs_of_pos hx]

end NLAlib
