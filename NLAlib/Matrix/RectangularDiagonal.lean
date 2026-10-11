import NLAlib.Matrix.SingularValueScaling
import NLAlib.Matrix.Projections
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fintype

/-!
# Rectangular diagonal embeddings

Finite thin vectors embed linearly and injectively into a matrix of a specified
rectangular shape. Independent signs and permutations are implemented by actual
left and right orthogonal matrices. Source: Bhatia (1997), Theorem IV.2.1.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib

/-- A finite thin vector embedded into the corresponding rectangular diagonal,
using the existing zero-padded `rectDiag` vocabulary. -/
def rectangularDiagonal {m n : ℕ} (x : Fin (min m n) → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  rectDiag (fun i => if hi : i < min m n then x ⟨i, hi⟩ else 0)

/-- Thin diagonal coordinates recover the embedded vector exactly. -/
@[simp] theorem rectangularDiagonal_apply_castLE {m n : ℕ} (x : Fin (min m n) → ℝ)
    (i j : Fin (min m n)) :
    rectangularDiagonal x (Fin.castLE (min_le_left m n) i) (Fin.castLE (min_le_right m n) j) =
      if i = j then x i else 0 := by
  have hi : i.val < m ∧ i.val < n := lt_min_iff.mp i.isLt
  simp [rectangularDiagonal, rectDiag_apply, Fin.val_inj, hi.1, hi.2]

/-- The rectangular diagonal embedding is injective, also for empty shapes. -/
theorem rectangularDiagonal_injective {m n : ℕ} :
    Function.Injective (rectangularDiagonal (m := m) (n := n)) := by
  intro x y hxy
  funext i
  have h := congrArg (fun M : Matrix (Fin m) (Fin n) ℝ =>
    M (Fin.castLE (min_le_left m n) i) (Fin.castLE (min_le_right m n) i)) hxy
  simpa using h

/-- Rectangular diagonal embedding as a real linear map. -/
def rectangularDiagonalLinear (m n : ℕ) : (Fin (min m n) → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ where
  toFun := rectangularDiagonal
  map_add' x y := by
    ext i j
    simp only [rectangularDiagonal, rectDiag_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    ext i j
    simp only [rectangularDiagonal, rectDiag_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

/-- The linear embedding evaluates to the specified rectangular diagonal. -/
@[simp] theorem rectangularDiagonalLinear_apply {m n : ℕ} (x : Fin (min m n) → ℝ) :
    rectangularDiagonalLinear m n x = rectangularDiagonal x := rfl

/-- A unit-sign diagonal matrix is orthogonal. -/
theorem hasOrthonormalCols_diagonal_of_abs_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) : HasOrthonormalCols (Matrix.diagonal ε) := by
  change (Matrix.diagonal ε)ᵀ * Matrix.diagonal ε = 1
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have h := congrArg (fun t : ℝ => t ^ 2) (hε i)
    have hsq : ε i ^ 2 = 1 := by simpa only [sq_abs, one_pow] using h
    simpa only [pow_two] using hsq
  · simp [hij]

/-- Independent signs on a thin vector are implemented by an actual left
orthogonal diagonal matrix, extended by ones on unused row coordinates. -/
theorem exists_orthogonal_rectangularDiagonal_sign {m n : ℕ}
    (x ε : Fin (min m n) → ℝ) (hε : ∀ i, |ε i| = 1) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ, HasOrthonormalCols U ∧
      U * rectangularDiagonal x = rectangularDiagonal (fun i => ε i * x i) := by
  let s : Fin m → ℝ := fun i => if hi : i.val < min m n then ε ⟨i.val, hi⟩ else 1
  refine ⟨Matrix.diagonal s, hasOrthonormalCols_diagonal_of_abs_eq_one s (fun i => ?_), ?_⟩
  · dsimp [s]
    split_ifs with hi
    · exact hε _
    · norm_num
  · ext i j
    rw [Matrix.diagonal_mul]
    simp only [rectangularDiagonal, rectDiag_apply, s]
    split_ifs <;> simp_all

/-- A real permutation matrix is orthogonal. -/
theorem hasOrthonormalCols_permMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : HasOrthonormalCols (σ.permMatrix ℝ) := by
  change (σ.permMatrix ℝ)ᵀ * σ.permMatrix ℝ = 1
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

/-- Extend a prefix permutation by the identity on every unused coordinate. -/
def prefixPermutation {k m : ℕ} (σ : Equiv.Perm (Fin k)) (hk : k ≤ m) : Equiv.Perm (Fin m) :=
  σ.viaFintypeEmbedding (Fin.castLEEmb hk)

/-- A prefix permutation acts on each embedded prefix coordinate as specified. -/
theorem prefixPermutation_apply_of_lt {k m : ℕ} (σ : Equiv.Perm (Fin k)) (hk : k ≤ m)
    (i : Fin m) (hi : i.val < k) :
    prefixPermutation σ hk i = Fin.castLE hk (σ ⟨i.val, hi⟩) := by
  have he : (Fin.castLEEmb hk) (⟨i.val, hi⟩ : Fin k) = i := Fin.ext rfl
  conv_lhs => rw [prefixPermutation, ← he, Equiv.Perm.viaFintypeEmbedding_apply_image]
  rfl

/-- A prefix permutation fixes every coordinate outside its prefix. -/
theorem prefixPermutation_apply_of_not_lt {k m : ℕ} (σ : Equiv.Perm (Fin k)) (hk : k ≤ m)
    (i : Fin m) (hi : ¬ i.val < k) : prefixPermutation σ hk i = i := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨j, hj⟩
  exact hi (by rw [← hj]; exact j.isLt)

end NLAlib
