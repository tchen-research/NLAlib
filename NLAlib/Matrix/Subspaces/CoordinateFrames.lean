import NLAlib.Matrix.Subspaces.OrthogonalProducts

/-! # Coordinate selection as finite orthonormal frames

Injective coordinate selection gives an orthonormal frame whose adjoint
extracts the selected rows. A single coordinate column is its one-column
specialization. Source: Horn–Johnson, §2.1.
-/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 n r : Type*} [RCLike 𝕜]
variable [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- Coordinate vectors associated with the selected indices. -/
def coordinateFrame (indices : r → n) : Matrix n r 𝕜 :=
  (1 : Matrix n n 𝕜).submatrix id indices

/-- Distinct selected coordinates form an orthonormal frame. -/
theorem hasOrthonormalCols_coordinateFrame {indices : r → n}
    (h : Function.Injective indices) : HasOrthonormalCols (coordinateFrame (𝕜 := 𝕜) indices) :=
  hasOrthonormalCols_one.submatrix_cols ⟨indices, h⟩

/-- The adjoint coordinate frame extracts exactly the selected rows. -/
theorem coordinateFrame_conjTranspose_mul (indices : r → n) (U : Matrix n r 𝕜) :
    (coordinateFrame indices)ᴴ * U = U.submatrix indices id := by
  ext i j
  simp [coordinateFrame, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A single standard coordinate vector, regarded as a one-column matrix. -/
def coordinateColumn (i₀ : m) : Matrix m Unit 𝕜 :=
  coordinateFrame (fun _ : Unit => i₀)

/-- The one-column specialization retains the literal coordinate-vector formula. -/
@[simp] theorem coordinateColumn_apply (i₀ i : m) (j : Unit) :
    coordinateColumn (𝕜 := 𝕜) i₀ i j = if i = i₀ then 1 else 0 := by
  simp [coordinateColumn, coordinateFrame, Matrix.one_apply]

/-- Coordinate columns are orthonormal, without a dimension normalization. -/
theorem hasOrthonormalCols_coordinateColumn (i₀ : m) :
    HasOrthonormalCols (coordinateColumn (𝕜 := 𝕜) i₀) :=
  hasOrthonormalCols_coordinateFrame (fun _ _ _ => Subsingleton.elim _ _)

end NLAlib
