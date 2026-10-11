/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.Pattern
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Three-level ladder matrices

The literal local creation and annihilation matrices decompose the symmetric Jacobi operator and carry their exact occupation shifts.
Ported from `SparseFockFormal.LocalOperators` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace LocalOperator

/-- A real operator on the three local sparse-Fock levels.  Rows are outputs and
columns are inputs.

Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
abbrev Op := Matrix Level Level ℝ

/-- The rank-one matrix `|out><inp|`.

Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def ketBra (out inp : Level) : Op := fun i j =>
  if i = out ∧ j = inp then 1 else 0

/-- A local matrix unit has coefficient one precisely at its specified output and input levels.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem ketBra_apply (out inp i j : Level) :
    ketBra out inp i j = if i = out ∧ j = inp then 1 else 0 := rfl

/-- Light creation is the local matrix unit from level zero to level one.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def pCreate : Op := ketBra .one .zero
/-- Light annihilation is the local matrix unit from level one to level zero.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def pDestroy : Op := ketBra .zero .one
/-- Heavy promotion is the local matrix unit from level one to level two.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def rPromote : Op := ketBra .two .one
/-- Heavy demotion is the local matrix unit from level two to level one.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def rDemote : Op := ketBra .one .two

/-- The three-level Jacobi multiplication matrix with heavy amplitude `ρ`.

Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def jacobi (ρ : ℝ) : Op :=
  pDestroy + pCreate + ρ • (rPromote + rDemote)

/-- Transposing a local matrix unit exchanges its output and input levels.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_ketBra (out inp : Level) :
    (ketBra out inp).transpose = ketBra inp out := by
  ext i j
  simp [ketBra, Matrix.transpose_apply, and_comm]

/-- The transpose of light creation is light annihilation.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_pCreate : pCreate.transpose = pDestroy := by
  simp [pCreate, pDestroy]

/-- The transpose of light annihilation is light creation.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_pDestroy : pDestroy.transpose = pCreate := by
  simp [pCreate, pDestroy]

/-- The transpose of heavy promotion is heavy demotion.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_rPromote : rPromote.transpose = rDemote := by
  simp [rPromote, rDemote]

/-- The transpose of heavy demotion is heavy promotion.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_rDemote : rDemote.transpose = rPromote := by
  simp [rPromote, rDemote]

/-- The local Jacobi multiplication matrix is symmetric.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem transpose_jacobi (ρ : ℝ) : (jacobi ρ).transpose = jacobi ρ := by
  ext i j
  cases i <;> cases j <;>
    simp [jacobi, pCreate, pDestroy, rPromote, rDemote, ketBra,
      Matrix.transpose_apply]

/-- Entrywise verification of the local multiplication matrix.

Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem jacobi_apply (ρ : ℝ) (i j : Level) :
    jacobi ρ i j =
      match i, j with
      | .zero, .one => 1
      | .one, .zero => 1
      | .one, .two => ρ
      | .two, .one => ρ
      | _, _ => 0 := by
  cases i <;> cases j <;>
    simp [jacobi, pCreate, pDestroy, rPromote, rDemote, ketBra]

/-- Light creation is nilpotent of order two.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem pCreate_sq : pCreate * pCreate = 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [pCreate, ketBra, Matrix.mul_apply]

/-- Heavy promotion is nilpotent of order two.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem rPromote_sq : rPromote * rPromote = 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [rPromote, ketBra, Matrix.mul_apply]

/-- The same-site product used by the `C A` factorization vanishes.

Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem pCreate_mul_rPromote : pCreate * rPromote = 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [pCreate, rPromote, ketBra, Matrix.mul_apply]

/-- The same-site product used by the grade-zero `C Ã` factorization vanishes.

Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem pCreate_mul_rDemote : pCreate * rDemote = 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [pCreate, rDemote, ketBra, Matrix.mul_apply]

/-- Reversing the first mixed product produces the artificial direct jump.

Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem rPromote_mul_pCreate :
    rPromote * pCreate = ketBra .two .zero := by
  ext i j
  cases i <;> cases j <;>
    simp [pCreate, rPromote, ketBra, Matrix.mul_apply]

/-- Each local level receives its integer occupation weight.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def weightZ (q : Level) : ℤ := q.weight

/-- A local matrix changes occupation grade by `δ` on its support.

Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Homogeneous (δ : ℤ) (A : Op) : Prop :=
  ∀ ⦃out inp : Level⦄, A out inp ≠ 0 → weightZ out = weightZ inp + δ

/-- Light creation raises occupation grade by one.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pCreate_homogeneous : Homogeneous 1 pCreate := by
  intro out inp h
  cases out <;> cases inp <;>
    simp [pCreate, ketBra, weightZ, Level.weight] at h ⊢

/-- Light annihilation lowers occupation grade by one.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem pDestroy_homogeneous : Homogeneous (-1) pDestroy := by
  intro out inp h
  cases out <;> cases inp <;>
    simp [pDestroy, ketBra, weightZ, Level.weight] at h ⊢

/-- Heavy promotion raises occupation grade by one.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rPromote_homogeneous : Homogeneous 1 rPromote := by
  intro out inp h
  cases out <;> cases inp <;>
    simp [rPromote, ketBra, weightZ, Level.weight] at h ⊢

/-- Heavy demotion lowers occupation grade by one.
Source: ported from `SparseFockFormal.LocalOperators`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rDemote_homogeneous : Homogeneous (-1) rDemote := by
  intro out inp h
  cases out <;> cases inp <;>
    simp [rDemote, ketBra, weightZ, Level.weight] at h ⊢

end LocalOperator

end NLAlib.SparseFock
