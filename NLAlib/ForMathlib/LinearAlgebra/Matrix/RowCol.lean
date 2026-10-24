import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.List.OfFn

/-! # Gram matrices of finite row lists and zero-row insertion

These are finite matrix identities for row-stream algorithms. Replacing a zero row
adds exactly the incoming row Gram matrix; no rank or nonzero condition is needed.
-/

noncomputable section
open scoped Matrix
namespace Matrix

/-- Interpret a finite row list as its positional rectangular matrix. -/
def ofRowList {n α : Type*} (rows : List (n → α)) : Matrix (Fin rows.length) n α :=
  fun i => rows.get i

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- The Gram matrix of a row list is the finite sum of its individual row Grams. -/
theorem conjTranspose_ofRowList_mul_ofRowList (rows : List (n → 𝕜)) :
    (ofRowList rows)ᴴ * ofRowList rows =
      (rows.map (fun a => vecMulVec (star a) a)).sum := by
  have hm : (rows.map (fun a => vecMulVec (star a) a)).sum =
      ∑ i : Fin rows.length, vecMulVec (star (rows.get i)) (rows.get i) := by
    rw [← List.ofFn_getElem_eq_map rows (fun a => vecMulVec (star a) a), List.sum_ofFn]
    rfl
  rw [hm]
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, ofRowList]

/-- The native positional row enumeration has the original Gram matrix. -/
theorem sum_rowGrams_ofFn {N : ℕ} (A : Matrix (Fin N) n 𝕜) :
    ((List.ofFn (fun i => A i)).map (fun a => vecMulVec (star a) a)).sum = Aᴴ * A := by
  rw [List.map_ofFn, List.sum_ofFn]
  ext j k
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Function.comp_apply, Matrix.vecMulVec_apply, Pi.star_apply]

/-- Inserting a row into a zero row adds its Gram exactly. This is the source of the
Frequent Directions covariance invariant, including zero incoming rows. -/
theorem conjTranspose_updateRow_mul_updateRow_eq_add [Fintype m] [DecidableEq m]
    (B : Matrix m n 𝕜) (i : m) (a : n → 𝕜) (hi : B i = 0) :
    (B.updateRow i a)ᴴ * B.updateRow i a = Bᴴ * B + vecMulVec (star a) a := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, Pi.star_apply]
  rw [← Finset.sum_erase_add Finset.univ
    (fun t => star ((B.updateRow i a) t j) * (B.updateRow i a) t k) (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ
    (fun t => star (B t j) * B t k) (Finset.mem_univ i)]
  have he : (∑ t ∈ Finset.univ.erase i,
      star ((B.updateRow i a) t j) * (B.updateRow i a) t k) =
      ∑ t ∈ Finset.univ.erase i, star (B t j) * B t k := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Matrix.updateRow_ne (Finset.mem_erase.mp ht).1]
  rw [he]
  simp only [Matrix.updateRow_self, hi, Pi.zero_apply, star_zero, zero_mul, add_zero]

end Matrix
