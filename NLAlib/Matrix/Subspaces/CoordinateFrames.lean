import NLAlib.Matrix.Basic.CoordinateSelector
import NLAlib.Matrix.Basic.MoorePenroseTransformations
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

omit [Fintype r] [DecidableEq r] in
/-- The adjoint coordinate frame extracts exactly the selected rows. -/
theorem coordinateFrame_conjTranspose_mul {p : Type*} (indices : r → n) (U : Matrix n p 𝕜) :
    (coordinateFrame indices)ᴴ * U = U.submatrix indices id := by
  ext i j
  simp [coordinateFrame, Matrix.mul_apply, Matrix.one_apply]

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A single standard coordinate vector, regarded as a one-column matrix. -/
def coordinateColumn (i₀ : m) : Matrix m Unit 𝕜 :=
  coordinateFrame (fun _ : Unit => i₀)

omit [Fintype m] in
/-- The one-column specialization retains the literal coordinate-vector formula. -/
@[simp] theorem coordinateColumn_apply (i₀ i : m) (j : Unit) :
    coordinateColumn (𝕜 := 𝕜) i₀ i j = if i = i₀ then 1 else 0 := by
  simp [coordinateColumn, coordinateFrame, Matrix.one_apply]

/-- Coordinate columns are orthonormal, without a dimension normalization. -/
theorem hasOrthonormalCols_coordinateColumn (i₀ : m) :
    HasOrthonormalCols (coordinateColumn (𝕜 := 𝕜) i₀) :=
  hasOrthonormalCols_coordinateFrame (fun _ _ _ => Subsingleton.elim _ _)

end NLAlib

namespace NLAlib

variable {𝕜 n d r : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

omit [Fintype n] [DecidableEq d] in
/-- The coordinate frame's row Gram matrix is the diagonal projection onto
exactly its selected coordinate labels. -/
theorem one_submatrix_mul_conjTranspose (e : d ↪ n) :
    (1 : Matrix n n 𝕜).submatrix id e * ((1 : Matrix n n 𝕜).submatrix id e)ᴴ =
      coordinateSelector (Finset.univ.map e) := by
  classical
  ext i j
  by_cases hi : i ∈ Finset.univ.map e
  · obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
      Function.id_def]
    rw [Finset.sum_eq_single a]
    · by_cases haj : e a = j
      · subst j
        rw [Matrix.one_apply_eq, star_one, one_mul, coordinateSelector,
          Matrix.diagonal_apply_eq, if_pos hi]
      · simp [Matrix.one_apply_ne (Ne.symm haj), coordinateSelector, haj]
    · intro b _ hba
      have hab : e a ≠ e b := fun h => hba (e.injective h).symm
      rw [Matrix.one_apply_ne hab, zero_mul]
    · simp
  · have he : ∀ a, i ≠ e a := by
      intro a hea
      exact hi (hea ▸ Finset.mem_map.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    have hrow : ∀ a : d, (1 : Matrix n n 𝕜) i (e a) = 0 := by
      intro a
      exact Matrix.one_apply_ne (he a)
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Function.id_def,
      hrow, zero_mul, Finset.sum_const_zero]
    by_cases hij : i = j
    · subst j
      rw [coordinateSelector, Matrix.diagonal_apply_eq, if_neg hi]
    · simp [coordinateSelector, hij]

omit [DecidableEq d] in
/-- Padding a selected square matrix with zero rows is multiplication by its
coordinate frame. -/
theorem coordinateSelector_mul_eq_one_submatrix_mul (X : Matrix n r 𝕜) (e : d ↪ n) :
    (coordinateSelector (Finset.univ.map e) : Matrix n n 𝕜) * X =
      (1 : Matrix n n 𝕜).submatrix id e * X.submatrix e id := by
  rw [← one_submatrix_mul_conjTranspose e, Matrix.mul_assoc]
  congr 1
  exact coordinateFrame_conjTranspose_mul e X

/-- For a nonsingular square selected restriction, its ambient padded
Moore–Penrose solution is precisely the inverse-selected-row solution. -/
theorem moorePenroseInverse_coordinateSelector_mul_mul (X : Matrix n d 𝕜)
    (e : d ↪ n) (hX : IsUnit (X.submatrix e id)) (Y : Matrix n r 𝕜) :
    moorePenroseInverse ((coordinateSelector (Finset.univ.map e) : Matrix n n 𝕜) * X) * Y =
      (X.submatrix e id)⁻¹ * Y.submatrix e id := by
  rw [coordinateSelector_mul_eq_one_submatrix_mul]
  change moorePenroseInverse (coordinateFrame e * X.submatrix e id) * Y = _
  rw [
    moorePenroseInverse_mul_left_of_hasOrthonormalCols _ _ (hasOrthonormalCols_coordinateFrame e.injective),
    moorePenroseInverse_eq_inv_of_isUnit _ hX, Matrix.mul_assoc]
  congr 1
  exact coordinateFrame_conjTranspose_mul e Y

end NLAlib
