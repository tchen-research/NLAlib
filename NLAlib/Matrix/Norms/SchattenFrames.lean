import NLAlib.Matrix.Norms.Schatten

/-!
# Schatten invariance in full singular frames

Full orthonormal frames may use positional `Fin (card n)` indices different
from the ambient matrix indices. Their left and right multiplication
preserves every finite singular-value power sum.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Full orthonormal frames preserve finite Schatten power sums, also when
ambient and positional frame indices differ. -/
theorem schattenNormReal_isometry_mul_mul_conjTranspose
    {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {U : Matrix m (Fin (Fintype.card m)) 𝕜}
    {V : Matrix n (Fin (Fintype.card n)) 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (A : Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) 𝕜) (p : ℝ) :
    schattenNormReal (U * A * Vᴴ) p = schattenNormReal A p := by
  simp only [schattenNormReal, singularValues_mul_isometry_conjTranspose hV,
    singularValues_isometry_mul hU, Fintype.card_fin]

end NLAlib
