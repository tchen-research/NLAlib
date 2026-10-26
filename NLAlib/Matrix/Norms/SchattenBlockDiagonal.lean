import NLAlib.Matrix.Norms.SchattenDiagonal
import NLAlib.Matrix.Norms.SchattenNormalization
import Mathlib.Data.Matrix.Block

/-!
# Schatten norms of finite block diagonal matrices

The `p`th Schatten power of a finite block diagonal matrix is exactly the
sum of the powers of its blocks. No ordering of the blocks' singular values
is needed: block diagonal singular frames reduce the assertion to an
ordinary diagonal matrix. This realizes finite matrix-valued `L^p` norms
as single native Schatten norms, with atom weights included.

Source: the finite-output interpolation reduction for
Latała--van Handel--Youssef, arXiv:1711.00807v2, §2.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

namespace NLAlib

/-- A finite block diagonal complex matrix has Schatten norm equal to the
`ℓ_p` norm of its blocks' Schatten norms, for every positive real exponent.
Zero blocks and empty block and matrix index spaces are included. -/
theorem schattenNormReal_blockDiagonal_complex
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNormReal (Matrix.blockDiagonal A) p =
      (∑ l, schattenNormReal (A l) p ^ p) ^ (1 / p) := by
  classical
  choose U V h using fun l => exists_isSVD (A l)
  let D : ι → Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ := fun l =>
    Matrix.diagonal (fun i => (singularValues (A l) i : ℂ))
  have hD (l : ι) : (rectDiag (singularValues (A l)) :
      Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) = D l := by
    ext i j
    simp only [D, rectDiag_apply_ofReal, Matrix.diagonal_apply, Fin.ext_iff]
    split_ifs <;> rfl
  have hU : HasOrthonormalCols (Matrix.blockDiagonal U) := by
    change (Matrix.blockDiagonal U)ᴴ * Matrix.blockDiagonal U = 1
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    simp only [(h _).conjTranspose_mul_left]
    exact Matrix.blockDiagonal_one
  have hV : HasOrthonormalCols (Matrix.blockDiagonal V) := by
    change (Matrix.blockDiagonal V)ᴴ * Matrix.blockDiagonal V = 1
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    simp only [(h _).conjTranspose_mul_right]
    exact Matrix.blockDiagonal_one
  have hA : Matrix.blockDiagonal A = Matrix.blockDiagonal U *
      Matrix.blockDiagonal D * (Matrix.blockDiagonal V)ᴴ := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
      ← Matrix.blockDiagonal_mul]
    congr 1
    funext l
    simpa only [← hD l] using (h l).eq
  have hnorm : schattenNormReal (Matrix.blockDiagonal U * Matrix.blockDiagonal D *
      (Matrix.blockDiagonal V)ᴴ) p = schattenNormReal (Matrix.blockDiagonal D) p := by
    simp only [schattenNormReal, singularValues_mul_isometry_conjTranspose hV,
      singularValues_isometry_mul hU, Fintype.card_prod, Fintype.card_fin]
  have hpower (l : ι) : schattenNormReal (A l) p ^ p =
      ∑ i : Fin (Fintype.card n), singularValues (A l) i ^ p := by
    rw [schattenNormReal_rpow_eq_sum (A l) hp, min_self,
      Fin.sum_univ_eq_sum_range (fun i => singularValues (A l) i ^ p)]
  rw [hA, hnorm]
  change schattenNormReal (Matrix.blockDiagonal fun l =>
    Matrix.diagonal (fun i : Fin (Fintype.card n) => (singularValues (A l) i : ℂ))) p = _
  rw [Matrix.blockDiagonal_diagonal, schattenNormReal_diagonal_complex]
  congr 1
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (singularValues_nonneg _ _), Fintype.sum_prod_type, hpower]
  exact Finset.sum_comm

/-- The real block diagonal Schatten formula has the same constant and
the same unnormalized power sum as its complex counterpart. -/
theorem schattenNormReal_blockDiagonal_real
    {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℝ) {p : ℝ} (hp : 0 < p) :
    schattenNormReal (Matrix.blockDiagonal A) p =
      (∑ l, schattenNormReal (A l) p ^ p) ^ (1 / p) := by
  have hh := schattenNormReal_blockDiagonal_complex (fun l => (A l).map Complex.ofReal) hp
  rw [← Matrix.blockDiagonal_map _ Complex.ofReal (by simp)] at hh
  have hs (B : Matrix n n ℝ) (i : ℕ) :
      singularValues (B.map Complex.ofReal) i = singularValues B i :=
    singularValues_map_ofReal (𝕜 := ℂ) B i
  have hsD (i : ℕ) : singularValues ((Matrix.blockDiagonal A).map Complex.ofReal) i =
      singularValues (Matrix.blockDiagonal A) i :=
    singularValues_map_ofReal (𝕜 := ℂ) (Matrix.blockDiagonal A) i
  simpa only [schattenNormReal, hs, hsD] using hh

end NLAlib
