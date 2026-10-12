import NLAlib.Matrix.Spectral.RealPencilTriangularization
import NLAlib.Matrix.Subspaces.Projections
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Real QZ for every square matrix pencil

Real orthogonal left and right factors give an upper quasitriangular first
factor and an upper triangular second factor, including singular pencils.
Source: Horn–Johnson (2013), Theorem 2.6.2.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

/-- Every real square pencil has common real orthogonal left and right
factors giving an upper quasitriangular first factor and upper triangular
second factor. Source: Horn–Johnson (2013), Theorem 2.6.2; the quasitriangular
zero pattern has consecutive blocks of size one or two. Singular and
identically singular pencils, common zero images and empty shapes are
included, with no regularity or invertibility assumption on either matrix.
atlas: schur-triangularization (partial) -/
theorem exists_orthogonal_qz_triangularization
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (order : Fin (Fintype.card n) ≃ n) :
    ∃ (V W T₁ T₂ : Matrix n n ℝ), HasOrthonormalCols V ∧ HasOrthonormalCols W ∧
      A = V * T₁ * Wᵀ ∧ B = V * T₂ * Wᵀ ∧
      IsUpperQuasiTriangular (T₁.submatrix order order) ∧
      (∀ i j, order.symm j < order.symm i → T₂ i j = 0) := by
  classical
  obtain ⟨e₀, f₀, hA₀, hB₀⟩ := exists_orthonormalBases_real_pencil_upper_quasi_triangular
    (Fintype.card n) A.toEuclideanLin B.toEuclideanLin
    (finrank_euclideanSpace (𝕜 := ℝ)) (finrank_euclideanSpace (𝕜 := ℝ))
  let e : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := e₀.reindex order
  let f : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := f₀.reindex order
  let c := EuclideanSpace.basisFun n ℝ
  let V : Matrix.unitaryGroup n ℝ :=
    ⟨c.toBasis.toMatrix f.toBasis, c.toMatrix_orthonormalBasis_mem_unitary f⟩
  let W : Matrix.unitaryGroup n ℝ :=
    ⟨c.toBasis.toMatrix e.toBasis, c.toMatrix_orthonormalBasis_mem_unitary e⟩
  let T (M : Matrix n n ℝ) := M.toEuclideanLin.toMatrix e.toBasis f.toBasis
  have hVorth : HasOrthonormalCols (V : Matrix n n ℝ) := by
    have h : (V : Matrix n n ℝ)ᴴ * (V : Matrix n n ℝ) = 1 := Unitary.coe_star_mul_self V
    simpa only [HasOrthonormalCols, Matrix.conjTranspose_eq_transpose_of_trivial] using
      h
  have hWorth : HasOrthonormalCols (W : Matrix n n ℝ) := by
    have h : (W : Matrix n n ℝ)ᴴ * (W : Matrix n n ℝ) = 1 := Unitary.coe_star_mul_self W
    simpa only [HasOrthonormalCols, Matrix.conjTranspose_eq_transpose_of_trivial] using
      h
  have hWW : (W : Matrix n n ℝ) * (W : Matrix n n ℝ)ᵀ = 1 := by
    have h : (W : Matrix n n ℝ) * (W : Matrix n n ℝ)ᴴ = 1 := Unitary.coe_mul_star_self W
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hback : e.toBasis.toMatrix c.toBasis = (W : Matrix n n ℝ)ᵀ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
      (Matrix.isUnit_det_of_right_inverse hWW) |>.mul_left_cancel
    change c.toBasis.toMatrix e.toBasis * e.toBasis.toMatrix c.toBasis =
      (W : Matrix n n ℝ) * (W : Matrix n n ℝ)ᵀ
    rw [Basis.toMatrix_mul_toMatrix_flip, hWW]
  have hFactor (M : Matrix n n ℝ) : M = (V : Matrix n n ℝ) * T M * (W : Matrix n n ℝ)ᵀ := by
    have hh := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      c.toBasis e.toBasis c.toBasis f.toBasis M.toEuclideanLin
    have hstd : M.toEuclideanLin.toMatrix c.toBasis c.toBasis = M :=
      LinearMap.toMatrix_toLin c.toBasis c.toBasis M
    rw [hback, hstd] at hh
    exact hh.symm
  refine ⟨V, W, T A, T B, hVorth, hWorth, hFactor A, hFactor B, ?_, ?_⟩
  · have hcoords : (T A).submatrix order order = A.toEuclideanLin.toMatrix e₀.toBasis f₀.toBasis := by
      ext i j
      simp only [T, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.repr_apply_apply, e, f, OrthonormalBasis.reindex_apply,
        Equiv.symm_apply_apply]
    rw [hcoords]
    exact hA₀
  · intro i j hij
    simp only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
    have h := hB₀ (i := order.symm i) (j := order.symm j) hij
    simpa only [e, f, OrthonormalBasis.reindex_apply, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.repr_apply_apply] using h

end NLAlib
