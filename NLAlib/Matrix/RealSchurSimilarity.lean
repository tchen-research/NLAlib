import NLAlib.Matrix.RealSchurCanonical
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Orthogonal similarity to the corrected real Schur form

Every real square matrix, on arbitrary finite labels, is orthogonally similar
to an upper block triangular matrix with scalar and nonreal real Schur blocks.
-/

noncomputable section
open Module
open scoped Matrix
namespace NLAlib

/-- Every real square matrix is orthogonally similar to the corrected
real Schur form. In the supplied coordinate order, the nonscalar blocks
are exactly `[[a,b],[c,a]]` with `bc<0`; empty matrices are included.
Horn–Johnson 2013, Theorem 2.3.1; derivations equation (G1).
atlas: schur-triangularization (partial) -/
theorem exists_orthogonal_real_schur {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (order : Fin (Fintype.card n) ≃ n) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧
      A = Q * T * Qᵀ ∧ IsRealSchurForm (T.submatrix order order) := by
  classical
  obtain ⟨b₀, hb₀⟩ := exists_orthonormalBasis_real_schur (Fintype.card n)
    A.toEuclideanLin (finrank_euclideanSpace (𝕜 := ℝ))
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := b₀.reindex order
  let c := EuclideanSpace.basisFun n ℝ
  let Q : Matrix.unitaryGroup n ℝ :=
    ⟨c.toBasis.toMatrix b.toBasis, c.toMatrix_orthonormalBasis_mem_unitary b⟩
  let T := A.toEuclideanLin.toMatrix b.toBasis b.toBasis
  have hQ : HasOrthonormalCols (Q : Matrix n n ℝ) := by
    have h : (Q : Matrix n n ℝ)ᴴ * (Q : Matrix n n ℝ) = 1 := Unitary.coe_star_mul_self Q
    simpa only [HasOrthonormalCols, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hQQ : (Q : Matrix n n ℝ) * (Q : Matrix n n ℝ)ᵀ = 1 := mul_eq_one_comm.mp hQ
  have hback : b.toBasis.toMatrix c.toBasis = (Q : Matrix n n ℝ)ᵀ := by
    calc
      b.toBasis.toMatrix c.toBasis =
          b.toBasis.toMatrix c.toBasis * ((Q : Matrix n n ℝ) * (Q : Matrix n n ℝ)ᵀ) := by
            rw [hQQ, Matrix.mul_one]
      _ = (Q : Matrix n n ℝ)ᵀ := by
        rw [← Matrix.mul_assoc]
        change (b.toBasis.toMatrix c.toBasis * c.toBasis.toMatrix b.toBasis) * _ = _
        rw [Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mul]
  have hFactor : A = (Q : Matrix n n ℝ) * T * (Q : Matrix n n ℝ)ᵀ := by
    have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      c.toBasis b.toBasis c.toBasis b.toBasis A.toEuclideanLin
    have hstd : A.toEuclideanLin.toMatrix c.toBasis c.toBasis = A :=
      LinearMap.toMatrix_toLin c.toBasis c.toBasis A
    rw [hback, hstd] at h
    exact h.symm
  refine ⟨Q, T, hQ, hFactor, ?_⟩
  have hcoords : T.submatrix order order = A.toEuclideanLin.toMatrix b₀.toBasis b₀.toBasis := by
    ext i j
    simp only [T, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.repr_apply_apply, b, OrthonormalBasis.reindex_apply,
      Equiv.symm_apply_apply]
  rwa [hcoords]

end NLAlib
