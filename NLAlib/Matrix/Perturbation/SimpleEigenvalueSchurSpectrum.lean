import NLAlib.Matrix.Perturbation.SimpleEigenvalueSchurFunction
import Mathlib.LinearAlgebra.Matrix.SchurComplement
/-!
# Spectrum and the scalar Schur eigenvalue equation

For a scalar leading block and an invertible trailing resolvent block, the
matrix spectral equation is exactly the scalar Schur equation.
The trailing coordinate type is arbitrary finite, including empty.
Horn–Johnson 2013, Theorem 6.3.12.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- The scalar Schur function is the determinant factor in the separated
scalar/block eigenvalue pencil. Arbitrary finite trailing indices, including
empty blocks, are allowed. Horn–Johnson 2013, Theorem 6.3.12; supports
`simple-eigenvalue-perturbation`. -/
theorem det_scalar_block_eigenvalue_pencil_eq_schur
    {l n : Type*} [Unique l] [Fintype n] [DecidableEq n]
    (μ a t s : ℂ) (B F : Matrix n n ℂ) (b c : n → ℂ)
    (hK : IsUnit ((μ + s) • (1 : Matrix n n ℂ) - B - t • F)) :
    (((μ + s) • (1 : Matrix (l ⊕ n) (l ⊕ n) ℂ) -
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
        t • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
          (Matrix.replicateRow l b) (Matrix.replicateCol l c) F))).det =
      ((μ + s) • (1 : Matrix n n ℂ) - B - t • F).det *
        simpleEigenvalueSchurFunction μ a B F b c (t, s) := by
  let K := (μ + s) • (1 : Matrix n n ℂ) - B - t • F
  let := hK.nonempty_invertible.some
  have hBlocks : ((μ + s) • (1 : Matrix (l ⊕ n) (l ⊕ n) ℂ) -
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
        t • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
          (Matrix.replicateRow l b) (Matrix.replicateCol l c) F)) =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : l => s - t * a))
        (-(t • Matrix.replicateRow l b)) (-(t • Matrix.replicateCol l c)) K := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply, K] <;>
      split_ifs <;> ring
  rw [hBlocks, Matrix.det_fromBlocks₂₂]
  congr 1
  rw [Matrix.det_unique, Matrix.invOf_eq_nonsing_inv, Matrix.nonsing_inv_eq_ringInverse]
  simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.smul_mul, Matrix.mul_smul, smul_neg, neg_neg, smul_smul,
    Matrix.smul_apply, smul_eq_mul]
  change s - t * a - (t * t) *
    ((Matrix.replicateRow l b * Ring.inverse K * Matrix.replicateCol l c) default default) =
      s - t * a - t ^ 2 * (b ⬝ᵥ (Ring.inverse K *ᵥ c))
  have hCouple : ((Matrix.replicateRow l b * Ring.inverse K *
      Matrix.replicateCol l c) default default) = b ⬝ᵥ (Ring.inverse K *ᵥ c) := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply,
      dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [hCouple, pow_two]

open scoped Matrix.Norms.L2Operator in
/-- Under invertibility of the trailing pencil block, a spectral point of
the perturbed scalar/block matrix is exactly a zero of the scalar
Schur function. One common arbitrary finite trailing type is used throughout.
Horn–Johnson 2013, Theorem 6.3.12; supports `simple-eigenvalue-perturbation`. -/
theorem mem_spectrum_scalar_block_iff_schur_eq_zero
    {l n : Type*} [Unique l] [Fintype n] [DecidableEq n]
    (μ a t s : ℂ) (B F : Matrix n n ℂ) (b c : n → ℂ)
    (hK : IsUnit ((μ + s) • (1 : Matrix n n ℂ) - B - t • F)) :
    μ + s ∈ spectrum ℂ
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : l => μ)) 0 0 B +
        t • Matrix.fromBlocks (Matrix.diagonal (fun _ : l => a))
          (Matrix.replicateRow l b) (Matrix.replicateCol l c) F) ↔
      simpleEigenvalueSchurFunction μ a B F b c (t, s) = 0 := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    det_scalar_block_eigenvalue_pencil_eq_schur μ a t s B F b c hK]
  have hDet := (Matrix.isUnit_iff_isUnit_det _).mp hK
  exact mul_eq_zero_iff_left hDet.ne_zero

end NLAlib
