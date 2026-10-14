import NLAlib.ForMathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Real.Star

/-! # Generic finite Jacobi algebra

The actual tridiagonal matrix, its finite scalar fraction, coefficient shifts,
and determinant recurrence are shared across real and complex consumers.
No positivity or matrix-function theory is needed for these finite identities.
-/

noncomputable section
open Matrix
open scoped Matrix Polynomial
namespace NLAlib

/-- The symmetric tridiagonal (Jacobi) matrix with diagonal `a 0, …, a (m−1)` and
off-diagonal entries `(i, i+1)`, `(i+1, i)` equal to `β (i+1)`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 3. Atlas: `jacobi-matrix-identities`. -/
def jacobiMatrix {𝕜 : Type*} [Zero 𝕜] (a β : ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) = j then a i else if (i : ℕ) + 1 = j then β j
    else if (j : ℕ) + 1 = i then β i else 0

/-- The finite Jacobi (Stieltjes) continued fraction with `m` levels starting at level `k`:
`jacobiFraction a β x 0 k = 0` and
`jacobiFraction a β x (m+1) k = 1 / (x − a k − β (k+1)² · jacobiFraction a β x m (k+1))`, so
`jacobiFraction a β x m 0 = 1/(x − a₀ − β₁²/(x − a₁ − ⋯ − β_{m−1}²/(x − a_{m−1})))`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 3. Atlas: `jacobi-matrix-identities`. -/
def jacobiFraction {𝕜 : Type*} [Field 𝕜] (a β : ℕ → 𝕜) (x : 𝕜) : ℕ → ℕ → 𝕜
  | 0, _ => 0
  | m + 1, k => 1 / (x - a k - β (k + 1) ^ 2 * jacobiFraction a β x m (k + 1))

/-- The zero-order Jacobi scalar approximant is zero, without selecting a
nonexistent first matrix coordinate. Source: operator derivations after (OF27).
atlas: jacobi-matrix-identities (partial) -/
@[simp] theorem jacobiFraction_zero {𝕜 : Type*} [Field 𝕜] (a β : ℕ → 𝕜) (x : 𝕜) (k : ℕ) :
    jacobiFraction a β x 0 k = 0 := rfl

/-- Shifting the start level of a Jacobi fraction shifts the coefficients. -/
theorem jacobiFraction_succ {𝕜 : Type*} [Field 𝕜] (a β : ℕ → 𝕜) (x : 𝕜) (m k : ℕ) :
    jacobiFraction a β x m (k + 1) =
      jacobiFraction (fun i => a (i + 1)) (fun i => β (i + 1)) x m k := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih => simp only [jacobiFraction, ih (k + 1)]

/-- The trailing principal submatrix of a Jacobi matrix is the Jacobi matrix of the shifted
coefficients. -/
theorem submatrix_succ_jacobiMatrix {𝕜 : Type*} [Field 𝕜] (a β : ℕ → 𝕜) (m : ℕ) :
    (jacobiMatrix a β (m + 1)).submatrix Fin.succ Fin.succ =
      jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)) m := by
  ext i j
  simp only [jacobiMatrix, Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- `(x − J)` restricted to the trailing block is `x − J'`. -/
theorem submatrix_succ_smul_one_sub_jacobiMatrix {𝕜 : Type*} [Field 𝕜] (a β : ℕ → 𝕜) (m : ℕ) (x : 𝕜) :
    (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) - jacobiMatrix a β (m + 1)).submatrix
        Fin.succ Fin.succ =
      x • (1 : Matrix (Fin m) (Fin m) 𝕜) -
        jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)) m := by
  rw [← submatrix_succ_jacobiMatrix]
  ext i j
  simp [Matrix.one_apply]

/-- Determinant recurrence of a Jacobi matrix along its first row:
`det(x − J) = (x − a₀) det(x − J') − β₁² det(x − J'')` with `J'`, `J''` the trailing blocks
(shifted coefficients). Source: Golub–Meurant (2010) [`gm10`], Ch. 3. -/
theorem det_smul_one_sub_jacobiMatrix {𝕜 : Type*} [Field 𝕜] (a β : ℕ → 𝕜) (m : ℕ) (x : 𝕜) :
    (x • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) 𝕜) - jacobiMatrix a β (m + 2)).det =
      (x - a 0) * (x • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) -
          jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)) (m + 1)).det -
        β 1 ^ 2 * (x • (1 : Matrix (Fin m) (Fin m) 𝕜) -
          jacobiMatrix (fun i => a (i + 2)) (fun i => β (i + 2)) m).det := by
  set N := x • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) 𝕜) - jacobiMatrix a β (m + 2)
  have hN : ∀ i j : Fin (m + 2),
      N i j = (if i = j then x else 0) - jacobiMatrix a β (m + 2) i j :=
    fun i j => by simp [N, Matrix.one_apply]
  have hsub1 := submatrix_succ_smul_one_sub_jacobiMatrix a β (m + 1) x
  have hsub2 : N.submatrix (fun k => Fin.succ (Fin.succ k)) (fun k => Fin.succ (Fin.succ k)) =
      x • (1 : Matrix (Fin m) (Fin m) 𝕜) -
        jacobiMatrix (fun i => a (i + 2)) (fun i => β (i + 2)) m := by
    rw [← submatrix_succ_smul_one_sub_jacobiMatrix (fun i => a (i + 1)) (fun i => β (i + 1)),
      ← hsub1, Matrix.submatrix_submatrix]
    rfl
  -- the `(0, 1)` minor, expanded along its first column
  have hminor : (N.submatrix Fin.succ (Fin.succ (0 : Fin (m + 1))).succAbove).det =
      N (Fin.succ 0) 0 *
        (N.submatrix (fun k => Fin.succ (Fin.succ k)) fun k => Fin.succ (Fin.succ k)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fintype.sum_eq_zero]
    · simp only [Fin.val_zero, pow_zero, one_mul, add_zero, Matrix.submatrix_apply,
        Matrix.submatrix_submatrix, Fin.succAbove_zero, Fin.succ_succAbove_zero]
      congr 2
    · intro i
      rw [Matrix.submatrix_apply, Fin.succ_succAbove_zero, hN]
      simp [jacobiMatrix, Fin.succ_ne_zero]
  have hzero : ∀ j : Fin m, (-1) ^ ((Fin.succ (Fin.succ j) : Fin (m + 2)) : ℕ) *
      N 0 (Fin.succ (Fin.succ j)) *
        (N.submatrix Fin.succ (Fin.succ (Fin.succ j)).succAbove).det = 0 := by
    intro j
    rw [hN]
    simp only [jacobiMatrix, Matrix.of_apply, Fin.val_zero, Fin.val_succ,
      if_neg (Fin.succ_ne_zero _).symm, show (0 : ℕ) ≠ (j : ℕ) + 1 + 1 by omega,
      show 0 + 1 ≠ (j : ℕ) + 1 + 1 by omega, show (j : ℕ) + 1 + 1 + 1 ≠ 0 by omega, if_false,
      sub_zero, mul_zero, zero_mul]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fintype.sum_eq_zero _ hzero,
    hminor, Fin.succAbove_zero, hsub1, hsub2, hN, hN, hN]
  simp [jacobiMatrix]
  ring

/-- Every real Jacobi coefficient matrix is Hermitian, independently of
off-diagonal positivity or irreducibility. -/
theorem isHermitian_jacobiMatrix (a β : ℕ → ℝ) (m : ℕ) :
    (jacobiMatrix a β m).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [jacobiMatrix]
  have hv : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [Matrix.conjTranspose_apply, star_trivial, jacobiMatrix, Matrix.of_apply,
    if_neg hv, if_neg hv.symm]
  by_cases hi : (i : ℕ) + 1 = j
  · have hj : (j : ℕ) + 1 ≠ i := by omega
    simp [hi, hj]
  · by_cases hj : (j : ℕ) + 1 = i <;> simp [hi, hj]

/-- Mapping the coefficients of the actual Jacobi matrix maps all of its entries. -/
theorem map_jacobiMatrix {𝕜 𝕜' : Type*} [Field 𝕜] [Field 𝕜']
    (f : 𝕜 →+* 𝕜') (a β : ℕ → 𝕜) (m : ℕ) :
    (jacobiMatrix a β m).map f = jacobiMatrix (f ∘ a) (f ∘ β) m := by
  ext i j
  simp only [Matrix.map_apply, jacobiMatrix, Matrix.of_apply, Function.comp_apply]
  split_ifs <;> simp

end NLAlib
