import NLAlib.Matrix.Spectral.SVD
import NLAlib.Matrix.Spectral.SpectralBounds

/-!
# Spectral norm under real scalar extension

The existing singular-value scalar-extension theorem gives exact equality of
the rectangular spectral norms, including empty dimensions.
-/

noncomputable section
namespace NLAlib

/-- Extending a real matrix to an RCLike field preserves its spectral norm,
because it preserves every singular value. -/
theorem specNorm_map_ofReal {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [RCLike 𝕜] (A : Matrix m n ℝ) :
    specNorm (A.map (algebraMap ℝ 𝕜)) = specNorm A := by
  rw [← singularValues_zero_eq_specNorm, ← singularValues_zero_eq_specNorm]
  exact singularValues_map_ofReal (𝕜 := 𝕜) A 0

end NLAlib
