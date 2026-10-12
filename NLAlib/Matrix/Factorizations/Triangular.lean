import Mathlib.LinearAlgebra.Matrix.Block
import NLAlib.ForMathlib.LinearAlgebra.Matrix.Triangular
import Mathlib.Data.Real.Basic

/-!
# Triangular matrices and substitution

The predicates are Mathlib's: `Matrix.IsUpperTriangular A` is `A.BlockTriangular id` and
`Matrix.IsLowerTriangular A` is `A.BlockTriangular OrderDual.toDual` (both abbreviations, over any
linearly ordered index). This file adds:

* the entrywise forms `isUpperTriangular_iff`, `isLowerTriangular_iff` (the bridge lemmas) and
  transposition;
* unit triangular matrices `IsUnitLowerTriangular`, `IsUnitUpperTriangular`;
* closure under inverses (`isUpperTriangular_inv`, no invertibility hypothesis since `A⁻¹ = 0`
  for singular `A`); closure under products is Mathlib's `Matrix.BlockTriangular.mul` and the
  diagonal of a product is `mul_apply_self_of_isUpperTriangular` /
  `mul_apply_self_of_isLowerTriangular` (`NLAlib.ForMathlib.LinearAlgebra.Matrix.Triangular`);
* invertibility iff nonzero diagonal (`isUnit_det_iff_of_isUpperTriangular`); the determinant is
  Mathlib's `Matrix.det_of_isUpperTriangular` / `Matrix.det_of_isLowerTriangular`;
* the leading-pivot splitting `borderedMatrix a r c M = [[a, rᵀ], [c, M]]` on `Fin (n + 1)`, with
  its product, transpose, triangularity and determinant lemmas: every recursion of the direct
  methods (LU, Cholesky, substitution) is over this splitting;
* forward and back substitution as total recursions (`forwardSubst`, `backSubst`) and their
  realisation theorems `mulVec_forwardSubst`, `mulVec_backSubst`.

Sources: Trefethen–Bau 1997, Lect. 17; Golub–Van Loan 2013, §3.1.
Atlas: `triangular-matrices-def`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

section General

variable {n : Type*} [LinearOrder n]

/-- Bridge: Mathlib's `IsUpperTriangular` (`BlockTriangular id`) says the entries strictly below
the diagonal vanish. Trefethen–Bau 1997, Lect. 17; Golub–Van Loan 2013, §3.1. -/
theorem isUpperTriangular_iff {A : Matrix n n ℝ} :
    A.IsUpperTriangular ↔ ∀ i j, j < i → A i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h i j hij => h i j hij⟩

/-- Bridge: Mathlib's `IsLowerTriangular` (`BlockTriangular toDual`) says the entries strictly
above the diagonal vanish. Trefethen–Bau 1997, Lect. 17; Golub–Van Loan 2013, §3.1. -/
theorem isLowerTriangular_iff {A : Matrix n n ℝ} :
    A.IsLowerTriangular ↔ ∀ i j, i < j → A i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h i j hij => h i j hij⟩

/-- The transpose of a matrix is lower triangular iff the matrix is upper triangular.
Golub–Van Loan 2013, §3.1. -/
theorem isLowerTriangular_transpose_iff {A : Matrix n n ℝ} :
    Aᵀ.IsLowerTriangular ↔ A.IsUpperTriangular := by
  rw [isLowerTriangular_iff, isUpperTriangular_iff]
  exact ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

/-- The transpose of a matrix is upper triangular iff the matrix is lower triangular.
Golub–Van Loan 2013, §3.1. -/
theorem isUpperTriangular_transpose_iff {A : Matrix n n ℝ} :
    Aᵀ.IsUpperTriangular ↔ A.IsLowerTriangular := by
  rw [isLowerTriangular_iff, isUpperTriangular_iff]
  exact ⟨fun h i j hij => h j i hij, fun h i j hij => h j i hij⟩

/-- A matrix that is both lower and upper triangular is diagonal. Golub–Van Loan 2013, §3.1. -/
theorem eq_diagonal_of_isLowerTriangular_of_isUpperTriangular {A : Matrix n n ℝ}
    (hL : A.IsLowerTriangular) (hU : A.IsUpperTriangular) :
    A = Matrix.diagonal fun i => A i i := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [isLowerTriangular_iff.1 hL i j h, Matrix.diagonal_apply_ne _ h.ne]
  · simp
  · rw [isUpperTriangular_iff.1 hU i j h, Matrix.diagonal_apply_ne _ h.ne']

/-- A **unit lower triangular** matrix: lower triangular with ones on the diagonal (the `L` of
an LU factorization). Trefethen–Bau 1997, Lect. 20; Golub–Van Loan 2013, §3.1.
atlas: triangular-matrices-def -/
structure IsUnitLowerTriangular (L : Matrix n n ℝ) : Prop where
  /-- `L` is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- `L` has unit diagonal. -/
  apply_self : ∀ i, L i i = 1

/-- A **unit upper triangular** matrix: upper triangular with ones on the diagonal.
Golub–Van Loan 2013, §3.1.
atlas: triangular-matrices-def -/
structure IsUnitUpperTriangular (U : Matrix n n ℝ) : Prop where
  /-- `U` is upper triangular. -/
  isUpperTriangular : U.IsUpperTriangular
  /-- `U` has unit diagonal. -/
  apply_self : ∀ i, U i i = 1

/-- The identity is unit lower triangular. Golub–Van Loan 2013, §3.1. -/
theorem isUnitLowerTriangular_one : IsUnitLowerTriangular (1 : Matrix n n ℝ) :=
  ⟨blockTriangular_one, fun _ => Matrix.one_apply_eq _⟩

/-- The identity is unit upper triangular. Golub–Van Loan 2013, §3.1. -/
theorem isUnitUpperTriangular_one : IsUnitUpperTriangular (1 : Matrix n n ℝ) :=
  ⟨blockTriangular_one, fun _ => Matrix.one_apply_eq _⟩

/-- Transposition exchanges unit lower and unit upper triangular. Golub–Van Loan 2013, §3.1. -/
theorem isUnitUpperTriangular_transpose_iff {L : Matrix n n ℝ} :
    IsUnitUpperTriangular Lᵀ ↔ IsUnitLowerTriangular L :=
  ⟨fun h => ⟨isUpperTriangular_transpose_iff.1 h.1, h.2⟩,
    fun h => ⟨isUpperTriangular_transpose_iff.2 h.1, h.2⟩⟩

/-- Transposition exchanges unit upper and unit lower triangular. Golub–Van Loan 2013, §3.1. -/
theorem isUnitLowerTriangular_transpose_iff {U : Matrix n n ℝ} :
    IsUnitLowerTriangular Uᵀ ↔ IsUnitUpperTriangular U :=
  ⟨fun h => ⟨isLowerTriangular_transpose_iff.1 h.1, h.2⟩,
    fun h => ⟨isLowerTriangular_transpose_iff.2 h.1, h.2⟩⟩

/-- A unit lower triangular matrix that is also upper triangular is the identity (the step of
every uniqueness proof for triangular factorizations). Golub–Van Loan 2013, Thm 3.2.1 (proof). -/
theorem eq_one_of_isUnitLowerTriangular_of_isUpperTriangular {A : Matrix n n ℝ}
    (hL : IsUnitLowerTriangular A) (hU : A.IsUpperTriangular) : A = 1 := by
  rw [eq_diagonal_of_isLowerTriangular_of_isUpperTriangular hL.1 hU]
  simp [hL.2]

variable [Fintype n]

/-- The inverse of an upper triangular matrix is upper triangular. No invertibility hypothesis:
for singular `A`, Mathlib's `A⁻¹` is `0`. Trefethen–Bau 1997, Lect. 17; Golub–Van Loan 2013,
§3.1 (closure under inversion). -/
theorem isUpperTriangular_inv {A : Matrix n n ℝ} (hA : A.IsUpperTriangular) :
    A⁻¹.IsUpperTriangular := by
  by_cases h : IsUnit A.det
  · have := A.invertibleOfIsUnitDet h
    exact blockTriangular_inv_of_blockTriangular hA
  · rw [Matrix.nonsing_inv_apply_not_isUnit A h]
    exact blockTriangular_zero

/-- The inverse of a lower triangular matrix is lower triangular (no invertibility hypothesis).
Golub–Van Loan 2013, §3.1. -/
theorem isLowerTriangular_inv {A : Matrix n n ℝ} (hA : A.IsLowerTriangular) :
    A⁻¹.IsLowerTriangular := by
  by_cases h : IsUnit A.det
  · have := A.invertibleOfIsUnitDet h
    exact blockTriangular_inv_of_blockTriangular hA
  · rw [Matrix.nonsing_inv_apply_not_isUnit A h]
    exact blockTriangular_zero

/-- An upper triangular matrix is invertible iff its diagonal entries are all nonzero (the
determinant is the product of the diagonal, `Matrix.det_of_isUpperTriangular`).
Trefethen–Bau 1997, Lect. 17; Golub–Van Loan 2013, §3.1.
atlas: triangular-matrices-def -/
theorem isUnit_det_iff_of_isUpperTriangular {A : Matrix n n ℝ} (hA : A.IsUpperTriangular) :
    IsUnit A.det ↔ ∀ i, A i i ≠ 0 := by
  rw [det_of_isUpperTriangular hA, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp

/-- A lower triangular matrix is invertible iff its diagonal entries are all nonzero.
Trefethen–Bau 1997, Lect. 17; Golub–Van Loan 2013, §3.1.
atlas: triangular-matrices-def -/
theorem isUnit_det_iff_of_isLowerTriangular {A : Matrix n n ℝ} (hA : A.IsLowerTriangular) :
    IsUnit A.det ↔ ∀ i, A i i ≠ 0 := by
  rw [det_of_isLowerTriangular A hA, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp

/-- The diagonal of the inverse of an invertible upper triangular matrix is the reciprocal of
its diagonal. Golub–Van Loan 2013, §3.1. -/
theorem inv_apply_self_of_isUpperTriangular {A : Matrix n n ℝ} (hA : A.IsUpperTriangular)
    (hd : ∀ i, A i i ≠ 0) (i : n) : A⁻¹ i i = (A i i)⁻¹ := by
  have hu : IsUnit A.det := (isUnit_det_iff_of_isUpperTriangular hA).2 hd
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i) i
  rw [mul_apply_self_of_isUpperTriangular hA (isUpperTriangular_inv hA), Matrix.one_apply_eq]
    at h1
  exact eq_inv_of_mul_eq_one_right h1

/-- The diagonal of the inverse of an invertible lower triangular matrix is the reciprocal of
its diagonal. Golub–Van Loan 2013, §3.1. -/
theorem inv_apply_self_of_isLowerTriangular {A : Matrix n n ℝ} (hA : A.IsLowerTriangular)
    (hd : ∀ i, A i i ≠ 0) (i : n) : A⁻¹ i i = (A i i)⁻¹ := by
  have hu : IsUnit A.det := (isUnit_det_iff_of_isLowerTriangular hA).2 hd
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i) i
  rw [mul_apply_self_of_isLowerTriangular hA (isLowerTriangular_inv hA), Matrix.one_apply_eq]
    at h1
  exact eq_inv_of_mul_eq_one_right h1

/-- A product of unit lower triangular matrices is unit lower triangular. Golub–Van Loan 2013,
§3.1. -/
theorem IsUnitLowerTriangular.mul {A B : Matrix n n ℝ} (hA : IsUnitLowerTriangular A)
    (hB : IsUnitLowerTriangular B) : IsUnitLowerTriangular (A * B) :=
  ⟨BlockTriangular.mul hA.1 hB.1, fun i => by
    rw [mul_apply_self_of_isLowerTriangular hA.1 hB.1, hA.2, hB.2, one_mul]⟩

/-- A product of unit upper triangular matrices is unit upper triangular. Golub–Van Loan 2013,
§3.1. -/
theorem IsUnitUpperTriangular.mul {A B : Matrix n n ℝ} (hA : IsUnitUpperTriangular A)
    (hB : IsUnitUpperTriangular B) : IsUnitUpperTriangular (A * B) :=
  ⟨BlockTriangular.mul hA.1 hB.1, fun i => by
    rw [mul_apply_self_of_isUpperTriangular hA.1 hB.1, hA.2, hB.2, one_mul]⟩

/-- A unit lower triangular matrix has determinant one. Golub–Van Loan 2013, §3.1. -/
theorem IsUnitLowerTriangular.det_eq_one {L : Matrix n n ℝ} (hL : IsUnitLowerTriangular L) :
    L.det = 1 := by
  rw [det_of_isLowerTriangular L hL.1]
  simp [hL.2]

/-- A unit upper triangular matrix has determinant one. Golub–Van Loan 2013, §3.1. -/
theorem IsUnitUpperTriangular.det_eq_one {U : Matrix n n ℝ} (hU : IsUnitUpperTriangular U) :
    U.det = 1 := by
  rw [det_of_isUpperTriangular hU.1]
  simp [hU.2]

/-- The inverse of a unit lower triangular matrix is unit lower triangular. Golub–Van Loan 2013,
§3.1. -/
theorem IsUnitLowerTriangular.inv {L : Matrix n n ℝ} (hL : IsUnitLowerTriangular L) :
    IsUnitLowerTriangular L⁻¹ :=
  ⟨isLowerTriangular_inv hL.1, fun i => by
    rw [inv_apply_self_of_isLowerTriangular hL.1 (fun j => by simp [hL.2]), hL.2, inv_one]⟩

/-- The inverse of a unit upper triangular matrix is unit upper triangular. Golub–Van Loan 2013,
§3.1. -/
theorem IsUnitUpperTriangular.inv {U : Matrix n n ℝ} (hU : IsUnitUpperTriangular U) :
    IsUnitUpperTriangular U⁻¹ :=
  ⟨isUpperTriangular_inv hU.1, fun i => by
    rw [inv_apply_self_of_isUpperTriangular hU.1 (fun j => by simp [hU.2]), hU.2, inv_one]⟩

end General

/-! ### The leading-pivot splitting on `Fin (n + 1)` -/

section Bordered

variable {n : ℕ}

/-- The **bordered matrix** `[[a, rᵀ], [c, M]]` on `Fin (n + 1)`: pivot `a`, first row `r`,
first column `c`, trailing block `M`. This is the `Fin.cons` form of the leading-pivot block
splitting `Matrix.fromBlocks` over `Fin 1 ⊕ Fin n` that every recursion of the direct methods
uses (Trefethen–Bau 1997, Lect. 20–23; Golub–Van Loan 2013, §3.2, §4.2). -/
def borderedMatrix (a : ℝ) (r c : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (vecCons (vecCons a r) fun i => vecCons (c i) (M i))

/-- The pivot entry of a bordered matrix. -/
@[simp]
theorem borderedMatrix_zero_zero (a : ℝ) (r c : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    borderedMatrix a r c M 0 0 = a := rfl

/-- The first-row entries of a bordered matrix. -/
@[simp]
theorem borderedMatrix_zero_succ (a : ℝ) (r c : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) : borderedMatrix a r c M 0 j.succ = r j := by
  simp [borderedMatrix]

/-- The first-column entries of a bordered matrix. -/
@[simp]
theorem borderedMatrix_succ_zero (a : ℝ) (r c : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : borderedMatrix a r c M i.succ 0 = c i := by
  simp [borderedMatrix]

/-- The trailing-block entries of a bordered matrix. -/
@[simp]
theorem borderedMatrix_succ_succ (a : ℝ) (r c : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : borderedMatrix a r c M i.succ j.succ = M i j := by
  simp [borderedMatrix]

/-- The trailing block of a bordered matrix. -/
@[simp]
theorem submatrix_succ_borderedMatrix (a : ℝ) (r c : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (borderedMatrix a r c M).submatrix Fin.succ Fin.succ = M := by
  ext i j; simp

/-- Every matrix on `Fin (n + 1)` is the bordered matrix of its pivot, first row, first column
and trailing block. -/
theorem borderedMatrix_eta (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    borderedMatrix (A 0 0) (fun j => A 0 j.succ) (fun i => A i.succ 0)
      (A.submatrix Fin.succ Fin.succ) = A := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- Block multiplication of bordered matrices:
`[[a, rᵀ], [c, M]] [[a', r'ᵀ], [c', M']]` has pivot `a a' + r ⬝ c'`, first row `a r' + rᵀ M'`,
first column `a' c + M c'` and trailing block `c r'ᵀ + M M'`.
Golub–Van Loan 2013, §1.3 (block multiplication). -/
theorem borderedMatrix_mul_borderedMatrix (a a' : ℝ) (r c r' c' : Fin n → ℝ)
    (M M' : Matrix (Fin n) (Fin n) ℝ) :
    borderedMatrix a r c M * borderedMatrix a' r' c' M' =
      borderedMatrix (a * a' + r ⬝ᵥ c') (a • r' + r ᵥ* M') (a' • c + M *ᵥ c')
        (vecMulVec c r' + M * M') := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, dotProduct, vecMul, mulVec, vecMulVec_apply,
      mul_comm]

/-- The transpose of a bordered matrix exchanges the first row and column. -/
theorem transpose_borderedMatrix (a : ℝ) (r c : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (borderedMatrix a r c M)ᵀ = borderedMatrix a c r Mᵀ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

/-- A bordered matrix is upper triangular iff its first column below the pivot vanishes and its
trailing block is upper triangular. Golub–Van Loan 2013, §3.1. -/
theorem isUpperTriangular_borderedMatrix_iff {a : ℝ} {r c : Fin n → ℝ}
    {M : Matrix (Fin n) (Fin n) ℝ} :
    (borderedMatrix a r c M).IsUpperTriangular ↔ c = 0 ∧ M.IsUpperTriangular := by
  simp only [isUpperTriangular_iff]
  constructor
  · intro h
    refine ⟨funext fun i => ?_, fun i j hij => ?_⟩
    · simpa using h i.succ 0 (Fin.succ_pos i)
    · simpa using h i.succ j.succ (Fin.succ_lt_succ_iff.2 hij)
  · rintro ⟨rfl, hM⟩ i j hij
    induction i using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero j)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp
      | succ j => simpa using hM i j (Fin.succ_lt_succ_iff.1 hij)

/-- A bordered matrix is lower triangular iff its first row beyond the pivot vanishes and its
trailing block is lower triangular. Golub–Van Loan 2013, §3.1. -/
theorem isLowerTriangular_borderedMatrix_iff {a : ℝ} {r c : Fin n → ℝ}
    {M : Matrix (Fin n) (Fin n) ℝ} :
    (borderedMatrix a r c M).IsLowerTriangular ↔ r = 0 ∧ M.IsLowerTriangular := by
  rw [← isUpperTriangular_transpose_iff, transpose_borderedMatrix,
    isUpperTriangular_borderedMatrix_iff, isUpperTriangular_transpose_iff]

/-- Determinant of a bordered matrix with zero first column below the pivot:
`det [[a, rᵀ], [0, M]] = a det M` (Laplace expansion along the first column). -/
theorem det_borderedMatrix_of_left_eq_zero (a : ℝ) (r : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) : (borderedMatrix a r 0 M).det = a * M.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, borderedMatrix_zero_zero, Fin.succAbove_zero,
    borderedMatrix_succ_zero, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, submatrix_succ_borderedMatrix]

/-- Determinant of a bordered matrix with zero first row beyond the pivot:
`det [[a, 0], [c, M]] = a det M`. -/
theorem det_borderedMatrix_of_top_eq_zero (a : ℝ) (c : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) : (borderedMatrix a 0 c M).det = a * M.det := by
  rw [← det_transpose, transpose_borderedMatrix, det_borderedMatrix_of_left_eq_zero,
    det_transpose]

end Bordered

/-! ### Forward and back substitution -/

section Substitution

/-- **Forward substitution** for `L x = b`, as a total recursion on the leading pivot:
`x₀ = b₀ / L₀₀`, then solve the trailing system with right-hand side `b_{1:} − L_{1:,0} x₀`.
For a lower triangular `L` with nonzero diagonal this is the textbook loop
`xᵢ = (bᵢ − ∑_{j<i} Lᵢⱼ xⱼ) / Lᵢᵢ`; a zero pivot gives junk (`x / 0 = 0`), never an error.
Golub–Van Loan 2013, Alg. 3.1.1 (column-oriented form); Trefethen–Bau 1997, Lect. 17.
atlas: triangular-matrices-def -/
def forwardSubst : {n : ℕ} → Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, _ => 0
  | _ + 1, L, b =>
    vecCons (b 0 / L 0 0)
      (forwardSubst (L.submatrix Fin.succ Fin.succ) fun i => b i.succ - L i.succ 0 * (b 0 / L 0 0))

/-- **Back substitution** for `U x = b`: forward substitution on the index-reversed system (the
reversal `Fin.rev` turns an upper triangular matrix into a lower triangular one). Equivalent to
the textbook loop `xᵢ = (bᵢ − ∑_{j>i} Uᵢⱼ xⱼ) / Uᵢᵢ` for `i = n, …, 1`.
Trefethen–Bau 1997, Alg. 17.1; Golub–Van Loan 2013, Alg. 3.1.2.
atlas: triangular-matrices-def -/
def backSubst {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  forwardSubst (U.submatrix Fin.rev Fin.rev) (b ∘ Fin.rev) ∘ Fin.rev

/-- Realisation of forward substitution: for lower triangular `L` with nonzero diagonal,
`L (forwardSubst L b) = b`. Proof: induction on `n` over the bordered splitting of `L`.
Golub–Van Loan 2013, §3.1.1; Trefethen–Bau 1997, Lect. 17.
atlas: triangular-matrices-def -/
theorem mulVec_forwardSubst {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i ≠ 0) (b : Fin n → ℝ) : L *ᵥ forwardSubst L b = b := by
  induction n with
  | zero => ext i; exact i.elim0
  | succ n ih =>
    have hL' : (L.submatrix Fin.succ Fin.succ).IsLowerTriangular :=
      isLowerTriangular_iff.2 fun i j hij =>
        isLowerTriangular_iff.1 hL _ _ (Fin.succ_lt_succ_iff.2 hij)
    have hrow : ∀ j : Fin n, L 0 j.succ = 0 := fun j =>
      isLowerTriangular_iff.1 hL _ _ (Fin.succ_pos j)
    have ih' := ih hL' (fun i => hd i.succ)
      (fun i => b i.succ - L i.succ 0 * (b 0 / L 0 0))
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [forwardSubst, mulVec, dotProduct, Fin.sum_univ_succ, hrow, mul_div_cancel₀ _ (hd 0)]
    · have := congrFun ih' i
      simp only [mulVec, dotProduct, submatrix_apply] at this
      simp only [forwardSubst, mulVec, dotProduct, Fin.sum_univ_succ, cons_val_zero,
        cons_val_succ]
      rw [this]
      ring

/-- Realisation of back substitution: for upper triangular `U` with nonzero diagonal,
`U (backSubst U b) = b`. Proof: reverse the indices and apply `mulVec_forwardSubst`.
Trefethen–Bau 1997, Alg. 17.1; Golub–Van Loan 2013, §3.1.2.
atlas: triangular-matrices-def -/
theorem mulVec_backSubst {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (b : Fin n → ℝ) : U *ᵥ backSubst U b = b := by
  have hL : (U.submatrix Fin.rev Fin.rev).IsLowerTriangular :=
    isLowerTriangular_iff.2 fun i j hij =>
      isUpperTriangular_iff.1 hU _ _ (Fin.rev_lt_rev.2 hij)
  have h := mulVec_forwardSubst hL (fun i => hd i.rev) (b ∘ Fin.rev)
  ext i
  have hi := congrFun h i.rev
  simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply, Fin.rev_rev] at hi
  rw [← hi]
  simp only [backSubst, mulVec, dotProduct, Function.comp_apply]
  exact (Fintype.sum_equiv Fin.revPerm _ _ fun j => by simp).symm

end Substitution

end NLAlib
