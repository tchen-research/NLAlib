import NLAlib.Matrix.Subspaces.PrincipalAngles
import NLAlib.Matrix.Subspaces.GraphTangent
import NLAlib.Matrix.Subspaces.OrthonormalBasisMatrix
import NLAlib.Matrix.Subspaces.RangeProjector
import NLAlib.ForMathlib.Analysis.Convex.Integral
/-!
# Subspace interface contract checks

The nested unequal-dimensional pair distinguishes a directed gap from a symmetric
principal angle. Nonzero orthogonality has infinite vector tangent and excludes
the finite overlap domain. The remaining checks exercise real/complex Mathlib
interoperability and direct composition of the Hilbert basis and projector APIs.
-/

open scoped Matrix
open NLAlib
noncomputable section
example : directedSubspaceGap (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) = 0 := by
  simp [directedSubspaceGap, projResidual, specNorm_zero]
open scoped Matrix.Norms.L2Operator in
example : directedSubspaceGap (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)
    (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  have h : projResidual (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [projResidual, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.vecMul, Matrix.transpose_apply, dotProduct]
  rw [directedSubspaceGap, h, specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (by intro i; fin_cases i <;> norm_num)
  · simpa using (norm_le_pi_norm (![0, 1] : Fin 2 → ℝ) 1)
example : vectorTangentToFrameENNReal (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)
    (![0, 1] : Fin 2 → ℝ) = ⊤ := by
  apply vectorTangentToFrameENNReal_eq_top_of_projection_eq_zero
  · intro h
    have hh := congrFun h 1
    norm_num at hh
  · ext i
    fin_cases i
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
example : ¬ IsUnit ((!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ *
    (!![0; 1] : Matrix (Fin 2) (Fin 1) ℝ)) := by
  norm_num [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one,
    Matrix.mul_apply, Fin.sum_univ_two]

example {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (Q : Matrix m n ℂ) :
    HasOrthonormalCols Q ↔ Orthonormal ℂ (fun j => WithLp.toLp 2 (Q.col j)) :=
  hasOrthonormalCols_iff_orthonormal Q
example {m : Type*} [Fintype m] (S : Submodule ℂ (EuclideanSpace ℂ m)) :
    columnSpace (orthonormalBasisMatrixOfEuclideanSubspace S) = S :=
  columnSpace_orthonormalBasisMatrixOfEuclideanSubspace S
example {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Q X : Matrix m n ℂ) : principalAnglesFintype Q X = principalAnglesFintype X Q :=
  principalAngles_comm Q X
example {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Matrix m n ℂ) :
    Matrix.toEuclideanLin.symm (columnSpace B).starProjection.toLinearMap = rangeProjector B :=
  toEuclideanLin_symm_starProjection_eq_rangeProjector B
#check ConcaveOn.le_map_integral_of_integral_mem
