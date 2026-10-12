import NLAlib.ForMathlib.Analysis.OrderedSchur
/-!
# Complex Schur triangularization with prescribed eigenvalue order

Every complete characteristic-root list, including repetitions, is the
ordered diagonal of a unitary Schur factor.
Source: Horn–Johnson (2013), Theorem 2.3.1.
-/

noncomputable section
open Module Polynomial
open scoped Matrix

namespace NLAlib

/-- A real or complex matrix has a unitary Schur factor with any prescribed complete
characteristic-root order. Source: Horn–Johnson (2013), Theorem 2.3.1;
the enumeration orders arbitrary finite labels, with repeated eigenvalues
and the empty matrix allowed.
atlas: schur-triangularization (partial) -/
theorem exists_unitary_schur_triangularization_with_charpoly
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] (A : Matrix n n 𝕜)
    (e : Fin (Fintype.card n) ≃ n) (d : n → 𝕜)
    (hchar : A.charpoly = ∏ i, (X - C (d i))) :
    ∃ (U : Matrix.unitaryGroup n 𝕜) (T : Matrix n n 𝕜),
      A = (U : Matrix n n 𝕜) * T * (U : Matrix n n 𝕜)ᴴ ∧
      (∀ i j, e.symm j < e.symm i → T i j = 0) ∧ ∀ i, T i i = d i := by
  classical
  let f : Module.End 𝕜 (EuclideanSpace 𝕜 n) := A.toEuclideanLin
  let c := EuclideanSpace.basisFun n 𝕜
  have hstd : f.toMatrix c.toBasis c.toBasis = A := LinearMap.toMatrix_toLin c.toBasis c.toBasis A
  have hfchar : f.charpoly = ∏ i : Fin (Fintype.card n), (X - C (d (e i))) := by
    rw [← LinearMap.charpoly_toMatrix f c.toBasis, hstd, hchar]
    exact (e.prod_comp (fun i => X - C (d i))).symm
  obtain ⟨b₀, htri₀, hdiag₀⟩ := exists_orthonormalBasis_upper_triangular_with_charpoly
    (Fintype.card n) f (finrank_euclideanSpace (𝕜 := 𝕜)) (fun i => d (e i)) hfchar
  let b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) := b₀.reindex e
  let U : Matrix.unitaryGroup n 𝕜 :=
    ⟨c.toBasis.toMatrix b.toBasis, c.toMatrix_orthonormalBasis_mem_unitary b⟩
  let T : Matrix n n 𝕜 := f.toMatrix b.toBasis b.toBasis
  have hUU : (U : Matrix n n 𝕜) * (U : Matrix n n 𝕜)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hback : b.toBasis.toMatrix c.toBasis = (U : Matrix n n 𝕜)ᴴ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
      (Matrix.isUnit_det_of_right_inverse hUU) |>.mul_left_cancel
    change c.toBasis.toMatrix b.toBasis * b.toBasis.toMatrix c.toBasis =
      (U : Matrix n n 𝕜) * (U : Matrix n n 𝕜)ᴴ
    rw [Basis.toMatrix_mul_toMatrix_flip, hUU]
  have hA : A = (U : Matrix n n 𝕜) * T * (U : Matrix n n 𝕜)ᴴ := by
    have hbasis := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      c.toBasis b.toBasis c.toBasis b.toBasis f
    calc
      A = f.toMatrix c.toBasis c.toBasis := hstd.symm
      _ = c.toBasis.toMatrix b.toBasis * f.toMatrix b.toBasis b.toBasis *
          b.toBasis.toMatrix c.toBasis := hbasis.symm
      _ = _ := by rw [hback]
  refine ⟨U, T, hA, ?_, ?_⟩
  · intro i j hij
    simp only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
    simpa only [b, OrthonormalBasis.reindex_apply] using htri₀ (e.symm i) (e.symm j) hij
  · intro i
    simp only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
    simpa only [b, OrthonormalBasis.reindex_apply, Equiv.apply_symm_apply] using hdiag₀ (e.symm i)

end NLAlib
