import NLAlib.Matrix.Basic.KKT
import NLAlib.Matrix.Basic.Pseudoinverse
import NLAlib.Matrix.Functions.GeometricMeanIdentities
import NLAlib.Matrix.Functions.JensenBlockCalculus
import NLAlib.ForMathlib.LinearAlgebra.Matrix.Block

/-!
# Exact Schur preconditioning identities

The positive Schur complement `BA⁻¹Bᴴ`, symmetric block whitening, and the
ideal triangular preconditioner are defined using the native matrix operations.
Source: Benzi--Golub--Liesen (2005), Sections 10.1.1--10.1.2.
-/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Positive Schur complement of the saddle-point matrix `[A Bᴴ; B 0]`. -/
def saddleSchurComplement (A : Matrix n n 𝕜) (B : Matrix m n 𝕜) : Matrix m m 𝕜 :=
  B * A⁻¹ * Bᴴ

/-- Full row rank and a positive-definite leading block make the native Schur
complement positive definite.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem posDef_saddleSchurComplement {A : Matrix n n 𝕜} (hA : A.PosDef)
    {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m) :
    (saddleSchurComplement A B).PosDef := by
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr
    (isUnit_mul_conjTranspose_of_rank_eq_card B hB)
  have hbi : Function.Injective Bᴴ.mulVec := by
    intro v w hv
    apply hi
    simp only [← Matrix.mulVec_mulVec, hv]
  simpa only [saddleSchurComplement, Matrix.conjTranspose_conjTranspose] using
    hA.inv.conjTranspose_mul_mul_same hbi

open scoped Matrix.Norms.L2Operator in
/-- Symmetric preconditioning by `diag(A,Ŝ)` gives exactly `[I Cᴴ; C 0]`,
where `C=Ŝ⁻¹ᐟ² B A⁻¹ᐟ²`.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem symmetric_saddle_preconditioning_eq [Nonempty n] [Nonempty m]
    {A : Matrix n n 𝕜} {Shat : Matrix m m 𝕜} (hA : A.PosDef) (hS : Shat.PosDef)
    (B : Matrix m n 𝕜) :
    let R := cfc (fun x => (Real.sqrt x)⁻¹) (Matrix.fromBlocks A 0 0 Shat)
    let C := cfc (fun x => (Real.sqrt x)⁻¹) Shat * B * cfc (fun x => (Real.sqrt x)⁻¹) A
    R * kktMatrix A B * R = kktMatrix 1 C := by
  dsimp only
  rw [(cfc_fromBlocks A Shat hA.isHermitian hS.isHermitian _).2.2]
  have hRA : (cfc (fun x => (Real.sqrt x)⁻¹) A).IsHermitian := cfc_predicate _ _
  have hRS : (cfc (fun x => (Real.sqrt x)⁻¹) Shat).IsHermitian := cfc_predicate _ _
  simp only [kktMatrix, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, Matrix.conjTranspose_mul, hRA.eq, hRS.eq,
    cfc_inv_sqrt_mul_self_mul_inv_sqrt hA, Matrix.mul_assoc]

open scoped Matrix.Norms.L2Operator in
/-- The whitened coupling's row Gram matrix is the whitened Schur complement.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem saddle_coupling_mul_conjTranspose {A : Matrix n n 𝕜} (hA : A.PosDef)
    (B : Matrix m n 𝕜) (Shat : Matrix m m 𝕜) :
    let C := cfc (fun x => (Real.sqrt x)⁻¹) Shat * B * cfc (fun x => (Real.sqrt x)⁻¹) A
    C * Cᴴ = cfc (fun x => (Real.sqrt x)⁻¹) Shat * saddleSchurComplement A B *
      cfc (fun x => (Real.sqrt x)⁻¹) Shat := by
  dsimp only
  have hRA : (cfc (fun x => (Real.sqrt x)⁻¹) A).IsHermitian := cfc_predicate _ _
  have hRS : (cfc (fun x => (Real.sqrt x)⁻¹) Shat).IsHermitian := cfc_predicate _ _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRA.eq, hRS.eq,
    saddleSchurComplement, inv_eq_cfc_inv_sqrt_mul_self hA]
  simp only [Matrix.mul_assoc]

/-- The exact lower triangular Schur preconditioner gives a unit upper triangular
preconditioned matrix. -/
theorem triangular_saddle_preconditioning_eq {A : Matrix n n 𝕜} (hA : A.PosDef)
    {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m) :
    (Matrix.fromBlocks A 0 B (-saddleSchurComplement A B))⁻¹ * kktMatrix A B =
      Matrix.fromBlocks 1 (A⁻¹ * Bᴴ) 0 1 := by
  have hS := posDef_saddleSchurComplement hA hB
  have ht : IsUnit (Matrix.fromBlocks A 0 B (-saddleSchurComplement A B)) :=
    Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA.isUnit, hS.isUnit.neg⟩
  have he : Matrix.fromBlocks A 0 B (-saddleSchurComplement A B) *
      Matrix.fromBlocks 1 (A⁻¹ * Bᴴ) 0 1 = kktMatrix A B := by
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero,
      Matrix.mul_one, add_zero, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit), Matrix.one_mul, saddleSchurComplement,
      add_neg_cancel, kktMatrix]
  rw [← he, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp ht), Matrix.one_mul]

/-- The ideal triangular preconditioner leaves a nilpotent perturbation of order two.
atlas: saddle-point-schur-preconditioner-spectrum (partial) -/
theorem triangular_saddle_preconditioning_sub_one_sq {A : Matrix n n 𝕜} (hA : A.PosDef)
    {B : Matrix m n 𝕜} (hB : B.rank = Fintype.card m) :
    ((Matrix.fromBlocks A 0 B (-saddleSchurComplement A B))⁻¹ * kktMatrix A B - 1) ^ 2 = 0 := by
  rw [triangular_saddle_preconditioning_eq hA hB, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_sub, sub_self, sub_zero, sub_self,
    pow_two, Matrix.fromBlocks_multiply]
  simp only [sub_self, Matrix.zero_mul, Matrix.mul_zero, add_zero, Matrix.fromBlocks_zero]

/-- A normalized saddle matrix with orthonormal rows is annihilated by
`(t-1)(t²-t-1)`, without diagonalizing it. -/
theorem kktMatrix_one_annihilator {C : Matrix m n 𝕜} (hC : C * Cᴴ = 1) :
    (kktMatrix 1 C - 1) * ((kktMatrix 1 C) ^ 2 - kktMatrix 1 C - 1) = 0 := by
  have hs : (kktMatrix 1 C) ^ 2 - kktMatrix 1 C - 1 =
      Matrix.fromBlocks (Cᴴ * C - 1) 0 0 0 := by
    simp only [kktMatrix, pow_two, Matrix.fromBlocks_multiply, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, hC,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_sub, sub_self, sub_zero]
    congr 1
    abel
  rw [hs, kktMatrix, ← Matrix.fromBlocks_one, Matrix.fromBlocks_sub,
    sub_self, sub_zero, zero_sub, Matrix.fromBlocks_multiply]
  simp only [sub_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, Matrix.mul_sub,
    Matrix.mul_one, ← Matrix.mul_assoc C Cᴴ, hC, Matrix.one_mul, sub_self,
    Matrix.fromBlocks_zero]

end NLAlib
