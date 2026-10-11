/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Complete finite weighted orthonormal bases and multiplication operators

The scalar and matrix-valued coefficient representations preserve products,
powers and vacuum moments. Source: pinned sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`.
-/

noncomputable section

namespace NLAlib.SparseFock

namespace FiniteL2

open scoped BigOperators

variable (Omega I : Type*) [Fintype Omega] [Fintype I]

/-- A completely explicit orthonormal basis of a finite weighted real `L₂`
space.  `reconstruction` records completeness, not merely orthonormality.

Source: ported from `SparseFockFormal.FiniteL2`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
structure WeightedONBasis where
  /-- The finite outcome weights. Source: pinned finite weighted basis; supports `sparse-ose`. -/
  weight : Omega → ℝ
  /-- Every outcome weight is nonnegative. Source: pinned finite weighted basis; supports `sparse-ose`. -/
  weight_nonneg : ∀ x, 0 ≤ weight x
  /-- The outcome weights sum to one. Source: pinned finite weighted basis; supports `sparse-ose`. -/
  sum_weight : ∑ x, weight x = 1
  /-- The scalar functions forming the complete weighted basis. Source: pinned finite weighted basis; supports `sparse-ose`. -/
  basis : I → Omega → ℝ
  /-- Each basis function has weighted squared norm one. Source: pinned finite weighted basis; supports `sparse-ose`. -/
  orthonormal_same : ∀ i,
    (∑ x, weight x * basis i x * basis i x) = 1
  /-- Distinct basis functions have weighted pairing zero. Source: pinned finite weighted basis; supports `sparse-ose`. -/
  orthonormal_ne : ∀ i j, i ≠ j →
    (∑ x, weight x * basis i x * basis j x) = 0
  /-- Every scalar function is reconstructed pointwise from its weighted basis coefficients. Source: pinned finite weighted basis; supports `sparse-ose`. -/
  reconstruction : ∀ (f : Omega → ℝ) (x : Omega),
    f x = ∑ i, (∑ y, weight y * basis i y * f y) * basis i x
  /-- The distinguished coordinate of the constant basis function. Source: pinned finite weighted basis; supports `sparse-ose`. -/
  vacuum : I
  /-- The distinguished basis function equals one at every outcome. Source: pinned finite weighted basis; supports `sparse-ose`. -/
  vacuum_eq_one : ∀ x, basis vacuum x = 1

variable {Omega I} [DecidableEq I]

namespace WeightedONBasis

variable (B : WeightedONBasis Omega I)

/-- The weighted finite expectation is the sum of weight times observable.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
noncomputable def expect (f : Omega → ℝ) : ℝ :=
  ∑ x, B.weight x * f x

/-- A basis coefficient is the weighted pairing of the observable with that basis vector.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
noncomputable def coeff (i : I) (f : Omega → ℝ) : ℝ :=
  ∑ x, B.weight x * B.basis i x * f x

/-- Pairing two weighted orthonormal basis vectors gives their coordinate delta.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem coeff_basis (i j : I) :
    B.coeff i (B.basis j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simpa [coeff, mul_assoc] using B.orthonormal_same i
  · simp only [h, ↓reduceIte]
    simpa [coeff, mul_assoc] using B.orthonormal_ne i j h

omit [DecidableEq I] in
/-- Reconstruction in the complete weighted finite basis. Source: pinned
sparse-Fock `FiniteL2`, `reconstruct`; supports `sparse-ose`. -/
theorem reconstruct (f : Omega → ℝ) (x : Omega) :
    f x = ∑ i, B.coeff i f * B.basis i x := by
  simpa [coeff] using B.reconstruction f x

omit [DecidableEq I] in
/-- The weighted finite expectation of one is one. Source: pinned
sparse-Fock `FiniteL2`, `expect_one`; supports `sparse-ose`. -/
theorem expect_one : B.expect (fun _ => 1) = 1 := by
  simpa [expect] using B.sum_weight

omit [DecidableEq I] in
/-- Coefficients distribute over the finite basis sum. Source: pinned
sparse-Fock `FiniteL2`, `coeff_mul_sum`; supports `sparse-ose`. -/
theorem coeff_mul_sum (i : I) (a : Omega → ℝ) (c : I → ℝ) :
    B.coeff i (fun x => a x * ∑ j, c j * B.basis j x) =
      ∑ j, c j * B.coeff i (fun x => a x * B.basis j x) := by
  simp only [coeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [DecidableEq I] in
/-- Coefficients are additive over finite sums. Source: pinned
sparse-Fock `FiniteL2`, `coeff_sum`; supports `sparse-ose`. -/
theorem coeff_sum {K : Type*} [Fintype K] (i : I) (f : K → Omega → ℝ) :
    B.coeff i (fun x => ∑ k, f k x) = ∑ k, B.coeff i (f k) := by
  simp only [coeff, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Matrix of multiplication by a scalar observable in the finite ON basis.

Source: ported from `SparseFockFormal.FiniteL2`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def mulOp (a : Omega → ℝ) : Matrix I I ℝ :=
  fun i j => B.coeff i (fun x => a x * B.basis j x)

/-- Multiplication by the constant observable one is the identity coefficient matrix.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem mulOp_one : B.mulOp (fun _ => 1) = 1 := by
  classical
  ext i j
  simp [mulOp, coeff_basis, Matrix.one_apply]

omit [DecidableEq I] in
/-- Finite multiplication operators compose as multiplication of their
observables. Source: pinned sparse-Fock `FiniteL2`; supports `sparse-ose`. -/
theorem mulOp_mul (a b : Omega → ℝ) :
    B.mulOp a * B.mulOp b = B.mulOp (fun x => a x * b x) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [mulOp]
  calc
    (∑ k, B.coeff i (fun x => a x * B.basis k x) *
        B.coeff k (fun x => b x * B.basis j x)) =
        ∑ k, B.coeff k (fun x => b x * B.basis j x) *
          B.coeff i (fun x => a x * B.basis k x) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = B.coeff i (fun x => a x *
          ∑ k, B.coeff k (fun y => b y * B.basis j y) * B.basis k x) := by
            symm
            exact B.coeff_mul_sum i a
              (fun k => B.coeff k (fun y => b y * B.basis j y))
    _ = B.coeff i (fun x => a x * (b x * B.basis j x)) := by
            congr 1
            funext x
            rw [← B.reconstruct (fun y => b y * B.basis j y) x]
    _ = B.coeff i (fun x => (a x * b x) * B.basis j x) := by
            congr 2
            funext x
            ring

/-- The coefficient multiplication operator preserves powers of an observable.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem mulOp_pow (a : Omega → ℝ) (k : ℕ) :
    B.mulOp a ^ k = B.mulOp (fun x => a x ^ k) := by
  classical
  induction k with
  | zero => exact B.mulOp_one.symm
  | succ k ih =>
      rw [pow_succ, ih, B.mulOp_mul]
      congr 1

omit [DecidableEq I] in
/-- The vacuum matrix entry equals the actual weighted expectation. Source:
pinned sparse-Fock `FiniteL2`, `vacuum_mulOp`; supports `sparse-ose`. -/
theorem vacuum_mulOp (a : Omega → ℝ) :
    B.mulOp a B.vacuum B.vacuum = B.expect a := by
  simp [mulOp, coeff, expect, B.vacuum_eq_one]

/-- A scalar multiplication-operator vacuum entry is the corresponding weighted moment.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem vacuum_moment (a : Omega → ℝ) (k : ℕ) :
    (B.mulOp a ^ k) B.vacuum B.vacuum = B.expect (fun x => a x ^ k) := by
  rw [B.mulOp_pow]
  exact B.vacuum_mulOp _

section MatrixValued

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Matrix-valued multiplication operator.  Its basis is the external matrix
index paired with the finite `L₂` basis index.

Source: ported from `SparseFockFormal.FiniteL2`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def matrixMulOp (M : Omega → Matrix A A ℝ) :
    Matrix (A × I) (A × I) ℝ :=
  fun out inp =>
    B.coeff out.2 (fun x => M x out.1 inp.1 * B.basis inp.2 x)

omit [Fintype A] in
/-- Multiplication by the constant identity has the identity matrix in the
complete basis. Source: pinned sparse-Fock `FiniteL2`; supports `sparse-ose`. -/
theorem matrixMulOp_one :
    B.matrixMulOp (fun _ => (1 : Matrix A A ℝ)) = 1 := by
  classical
  ext out inp
  rcases out with ⟨a, i⟩
  rcases inp with ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    simp [matrixMulOp, Matrix.one_apply, B.coeff_basis]
  · simp [matrixMulOp, coeff, hab]

omit [DecidableEq A] [DecidableEq I] in
/-- Composition of matrix-valued multiplication operators computes the
pointwise product. Source: pinned sparse-Fock `FiniteL2`; supports `sparse-ose`. -/
theorem matrixMulOp_mul (M N : Omega → Matrix A A ℝ) :
    B.matrixMulOp M * B.matrixMulOp N =
      B.matrixMulOp (fun x => M x * N x) := by
  classical
  ext out inp
  rcases out with ⟨a, i⟩
  rcases inp with ⟨c, j⟩
  rw [Matrix.mul_apply]
  simp only [matrixMulOp, Fintype.sum_prod_type, Matrix.mul_apply]
  change (∑ b, ∑ k,
      B.coeff i (fun x => M x a b * B.basis k x) *
        B.coeff k (fun x => N x b c * B.basis j x)) =
    B.coeff i (fun x => (∑ b, M x a b * N x b c) * B.basis j x)
  have hfun :
      (fun x => (∑ b, M x a b * N x b c) * B.basis j x) =
        (fun x => ∑ b, (M x a b * N x b c) * B.basis j x) := by
    funext x
    rw [Finset.sum_mul]
  rw [hfun, B.coeff_sum]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ k, B.coeff i (fun x => M x a b * B.basis k x) *
        B.coeff k (fun x => N x b c * B.basis j x)) =
        ∑ k, B.coeff k (fun x => N x b c * B.basis j x) *
          B.coeff i (fun x => M x a b * B.basis k x) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = B.coeff i (fun x => M x a b *
          ∑ k, B.coeff k (fun y => N y b c * B.basis j y) * B.basis k x) := by
            symm
            exact B.coeff_mul_sum i (fun x => M x a b)
              (fun k => B.coeff k (fun y => N y b c * B.basis j y))
    _ = B.coeff i (fun x => M x a b * (N x b c * B.basis j x)) := by
            congr 1
            funext x
            rw [← B.reconstruct (fun y => N y b c * B.basis j y) x]
    _ = B.coeff i (fun x => (M x a b * N x b c) * B.basis j x) := by
            congr 2
            funext x
            ring

/-- The matrix-valued coefficient multiplication operator preserves pointwise matrix powers.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem matrixMulOp_pow (M : Omega → Matrix A A ℝ) (k : ℕ) :
    B.matrixMulOp M ^ k = B.matrixMulOp (fun x => M x ^ k) := by
  classical
  induction k with
  | zero => exact (B.matrixMulOp_one (A := A)).symm
  | succ k ih =>
      rw [pow_succ, ih, B.matrixMulOp_mul]
      congr 1

/-- A matrix-valued multiplication-operator vacuum entry is its weighted matrix-power moment.
Source: pinned sparse-Fock finite-law/basis proof, commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`. -/
theorem matrix_vacuum_moment (M : Omega → Matrix A A ℝ) (k : ℕ) :
    (∑ a, (B.matrixMulOp M ^ k) (a, B.vacuum) (a, B.vacuum)) =
      B.expect (fun x => Matrix.trace (M x ^ k)) := by
  rw [B.matrixMulOp_pow]
  simp only [matrixMulOp, coeff, B.vacuum_eq_one, mul_one, expect, Matrix.trace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  simp

end MatrixValued

end WeightedONBasis

end FiniteL2

end NLAlib.SparseFock
