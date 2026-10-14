import NLAlib.Matrix.Structured.JacobiBorders
import NLAlib.Matrix.Structured.TridiagonalPowers
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # First-coordinate moments of actual Jacobi borders

The finite reindexing places the scalar Schur corner after the leading matrix. Changing
this corner preserves moments through `2q`; adding the last coupling to a `(q+1)`-block
preserves moments through `2q+1`. Both statements include the smallest dimensions.
-/

noncomputable section
open Matrix Finset
open scoped Matrix
open scoped MatrixOrder

namespace NLAlib

variable {q : ℕ}

/-- The actual symmetric scalar border, on contiguous zero-based finite indices. -/
def finSymmetricBorder (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv (symmetricBorder J v d)

@[simp] theorem finSymmetricBorder_castSucc_castSucc
    (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) (i j : Fin q) :
    finSymmetricBorder J v d i.castSucc j.castSucc = J i j := by
  simp [finSymmetricBorder, symmetricBorder, Matrix.reindex]

@[simp] theorem finSymmetricBorder_castSucc_last
    (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) (i : Fin q) :
    finSymmetricBorder J v d i.castSucc (Fin.last q) = v i := by
  simp [finSymmetricBorder, symmetricBorder, Matrix.reindex]

@[simp] theorem finSymmetricBorder_last_castSucc
    (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) (i : Fin q) :
    finSymmetricBorder J v d (Fin.last q) i.castSucc = v i := by
  simp [finSymmetricBorder, symmetricBorder, Matrix.reindex]

@[simp] theorem finSymmetricBorder_last_last
    (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) :
    finSymmetricBorder J v d (Fin.last q) (Fin.last q) = d := by
  simp [finSymmetricBorder, symmetricBorder, Matrix.reindex]

/-- A border whose cross vector is supported at the last leading coordinate is
tridiagonal whenever its leading matrix is tridiagonal. -/
theorem isTridiagonal_finSymmetricBorder {J : Matrix (Fin q) (Fin q) ℝ}
    (hJ : IsTridiagonal J) {v : Fin q → ℝ} (hv : ∀ i, i.val + 1 < q → v i = 0)
    (d : ℝ) : IsTridiagonal (finSymmetricBorder J v d) := by
  constructor
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro hij; simp only [Fin.val_last] at hij; omega
    · intro hij
      simpa using hv j (by simpa using hij)
    · intro hij
      simp only [Fin.val_last, Fin.val_castSucc] at hij
      have := i.isLt
      omega
    · intro hij
      simpa using hJ.1 i j (by simpa using hij)
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro hij; simp only [Fin.val_last] at hij; omega
    · intro hij
      simpa only [transpose_apply, finSymmetricBorder_castSucc_last] using hv j (by simpa using hij)
    · intro hij
      simp only [Fin.val_last, Fin.val_castSucc] at hij
      have := i.isLt
      omega
    · intro hij
      simpa only [transpose_apply, finSymmetricBorder_castSucc_castSucc] using hJ.2 i j (by simpa using hij)

/-- Changing only the last corner of an actual `(q+1)`-dimensional tridiagonal border
preserves its rooted moments through degree `2q`.
Source: focused mathematical reroutes, Section 3, equations (BL1), (BL5).
atlas: gauss-radau-lobatto (partial) -/
theorem pow_finSymmetricBorder_apply_zero_eq_of_corner
    {J : Matrix (Fin q) (Fin q) ℝ} (hJ : IsTridiagonal J)
    {v : Fin q → ℝ} (hv : ∀ i, i.val + 1 < q → v i = 0)
    (d c : ℝ) (k : ℕ) (hk : k ≤ 2 * q) :
    (finSymmetricBorder J v d ^ k) 0 0 = (finSymmetricBorder J v c ^ k) 0 0 := by
  apply pow_apply_zero_eq_of_isTridiagonal_of_eq_below_add
    (isTridiagonal_finSymmetricBorder hJ hv d) (isTridiagonal_finSymmetricBorder hJ hv c)
    (Nat.succ_pos q) (2 * q) _ k hk
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij; simp only [Fin.val_last] at hij; omega
  · intro _; simp
  · intro _; simp
  · intro _; simp

/-- Adding the last neighboring coupling to a `(q+1)`-dimensional block preserves
its rooted moments through degree `2q+1`, independently of the new corner.
Source: focused mathematical reroutes, Section 3, equations (BL1), (BL10).
atlas: gauss-radau-lobatto (partial) -/
theorem pow_finSymmetricBorder_apply_zero_eq_of_coupling
    {J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ} (hJ : IsTridiagonal J)
    {v : Fin (q + 1) → ℝ} (hv : ∀ i, i.val < q → v i = 0)
    (d : ℝ) (k : ℕ) (hk : k ≤ 2 * q + 1) :
    (finSymmetricBorder J v d ^ k) 0 0 = (finSymmetricBorder J 0 d ^ k) 0 0 := by
  have hv' : ∀ i, i.val + 1 < q + 1 → v i = 0 := fun i hi => hv i (by omega)
  apply pow_apply_zero_eq_of_isTridiagonal_of_eq_below_add
    (isTridiagonal_finSymmetricBorder hJ hv' d)
    (isTridiagonal_finSymmetricBorder hJ (by simp) d)
    (by omega : 0 < (q + 1) + 1) (2 * q + 1) _ k hk
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij; simp only [Fin.val_last] at hij; omega
  · intro hij
    simpa using hv j (by simp only [Fin.val_last, Fin.val_castSucc] at hij; omega)
  · intro hij
    simpa using hv i (by simp only [Fin.val_last, Fin.val_castSucc] at hij; omega)
  · intro _; simp

/-- With no cross coupling, the rooted moments of the actual scalar border are those
of its leading block. -/
theorem pow_finSymmetricBorder_zero_apply_zero
    (J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (d : ℝ) (k : ℕ) :
    (finSymmetricBorder J 0 d ^ k) 0 0 = (J ^ k) 0 0 := by
  have hpow := (Matrix.reindexRingEquiv ℝ finSumFinEquiv).map_pow
    (symmetricBorder J 0 d) k
  change reindex finSumFinEquiv finSumFinEquiv (symmetricBorder J 0 d ^ k) =
    finSymmetricBorder J 0 d ^ k at hpow
  rw [← hpow]
  have hblock : symmetricBorder J 0 d =
      fromBlocks J 0 0 (of (fun _ _ => d) : Matrix (Fin 1) (Fin 1) ℝ) := rfl
  rw [hblock, fromBlocks_diagonal_pow]
  change (fromBlocks (J ^ k) 0 0 ((of (fun _ _ => d) : Matrix (Fin 1) (Fin 1) ℝ) ^ k))
    (Sum.inl (0 : Fin (q + 1))) (Sum.inl 0) = _
  rfl

/-- The finite indexed actual border inherits Hermitian symmetry from its leading
block, by the explicit reindexing. -/
theorem isHermitian_finSymmetricBorder {J : Matrix (Fin q) (Fin q) ℝ}
    (hJ : J.IsHermitian) (v : Fin q → ℝ) (d : ℝ) :
    (finSymmetricBorder J v d).IsHermitian :=
  (isHermitian_symmetricBorder hJ v d).submatrix finSumFinEquiv.symm

/-- A last-coordinate border with a nonzero last coupling keeps every superdiagonal
nonzero when the leading superdiagonal is nonzero. The empty leading block is allowed. -/
theorem finSymmetricBorder_superdiagonal_ne_zero
    {J : Matrix (Fin q) (Fin q) ℝ} {v : Fin q → ℝ} (d : ℝ)
    (hJ : ∀ i j : Fin q, i.val + 1 = j.val → J i j ≠ 0)
    (hv : ∀ i : Fin q, i.val + 1 = q → v i ≠ 0) :
    ∀ i j : Fin (q + 1), i.val + 1 = j.val → finSymmetricBorder J v d i j ≠ 0 := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij; simp only [Fin.val_last] at hij; omega
  · intro hij
    simp only [Fin.val_last, Fin.val_castSucc] at hij
    have := j.isLt
    omega
  · intro hij
    simpa using hv i (by simpa using hij)
  · intro hij
    simpa using hJ i j (by simpa using hij)

/-- Relabelling finite coordinates preserves the positive-semidefinite matrix order. -/
theorem reindex_le_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {A B : Matrix ι ι ℝ} (h : A ≤ B) :
    reindex e e A ≤ reindex e e B := by
  rw [Matrix.le_iff] at h ⊢
  change ((B - A).submatrix e.symm e.symm).PosSemidef
  exact h.submatrix e.symm

/-- Scalar identity shifts commute with finite coordinate relabelling. -/
theorem reindex_smul_one {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (a : ℝ) :
    reindex e e (a • (1 : Matrix ι ι ℝ)) = a • (1 : Matrix κ κ ℝ) := by
  ext i j
  simp [Matrix.reindex, Matrix.one_apply, e.symm.injective.eq_iff]

end NLAlib
