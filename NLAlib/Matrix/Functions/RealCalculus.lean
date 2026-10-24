/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Functions.HermitianCalculus
import Mathlib.LinearAlgebra.Lagrange

/-! # Real functional calculus under finite coordinate changes

Arbitrary real functions act entrywise on a real diagonal over either `RCLike` field.
Functional calculus respects a full unitary coordinate change, including between
finite index types and empty spaces. No global continuity hypothesis is needed.
Source: finite Hermitian spectral calculus; Higham (2008), Definition 1.2.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Real functional calculus of a real diagonal over either scalar field is entrywise.
Arbitrary functions are permitted since the spectrum is finite. -/
theorem cfc_diagonal_ofReal {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (x : n → ℝ) :
    cfc f (Matrix.diagonal fun i => (x i : 𝕜)) =
      Matrix.diagonal fun i => (f (x i) : 𝕜) := by
  classical
  let s := (Set.finite_range x).toFinset
  let p : ℝ[X] := Lagrange.interpolate s id f
  have hp : ∀ y ∈ Set.range x, p.eval y = f y := by
    intro y hy
    exact Lagrange.eval_interpolate_at_node (s := s) (v := id) (i := y) f
      Function.injective_id.injOn (by simpa [s] using hy)
  have hdiag : (Matrix.diagonal fun i => (x i : 𝕜)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext; simp)
  have heq : cfc f (Matrix.diagonal fun i => (x i : 𝕜)) =
      cfc p.eval (Matrix.diagonal fun i => (x i : 𝕜)) := by
    apply cfc_congr
    intro y hy
    have hy' : (y : 𝕜) ∈ spectrum 𝕜 (Matrix.diagonal fun i => (x i : 𝕜)) :=
      (spectrum.algebraMap_mem_iff 𝕜).mpr hy
    rw [spectrum_diagonal] at hy'
    obtain ⟨i, hi⟩ := hy'
    exact (hp y ⟨i, RCLike.ofReal_injective hi⟩).symm
  rw [heq, cfc_polynomial p _ hdiag.isSelfAdjoint]
  have ha := Polynomial.aeval_algHom_apply
    (Matrix.diagonalAlgHom ℝ (n := n) (α := 𝕜)) (fun i => (x i : 𝕜)) p
  simp only [Matrix.diagonalAlgHom_apply] at ha
  rw [ha]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  change Polynomial.aeval (algebraMap ℝ 𝕜 (x i)) p = (f (x i) : 𝕜)
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hp (x i) ⟨i, rfl⟩]

/-- Functional calculus respects a unitary change between finite coordinate spaces.
Both inverse identities are explicit, so the statement includes empty spaces. -/
theorem cfc_isometric_conj {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (U : Matrix m n 𝕜)
    (hU : HasOrthonormalCols U) (hU' : U * Uᴴ = 1) (f : ℝ → ℝ)
    (A : Matrix n n 𝕜) (hA : A.IsHermitian) :
    cfc f (U * A * Uᴴ) = U * cfc f A * Uᴴ := by
  let E : Matrix n n 𝕜 →⋆ₐ[ℝ] Matrix m m 𝕜 :=
    { toFun := fun M => U * M * Uᴴ
      map_one' := by simp [hU']
      map_mul' := fun M N => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U, hU.conjTranspose_mul_self, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun M N => by simp [Matrix.mul_add, Matrix.add_mul]
      commutes' := fun r => by simp [Algebra.algebraMap_eq_smul_one, hU']
      map_star' := fun M => by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.mul_assoc] }
  symm
  change E (cfc f A) = cfc f (E A)
  exact StarAlgHomClass.map_cfc E f A (A.finite_real_spectrum.continuousOn f)
    E.toAlgHom.toLinearMap.continuous_of_finiteDimensional hA
    (Matrix.isHermitian_mul_mul_conjTranspose U hA)


end NLAlib
