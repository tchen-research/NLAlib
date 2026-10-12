import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Orthonormalization preserves a triangularizing basis

Gram–Schmidt changes an ordered basis by an invertible upper triangular
matrix. It therefore preserves every upper triangular operator matrix.
-/

noncomputable section
open Module

namespace NLAlib

/-- Any common triangularizing basis can be replaced by an orthonormal
basis with the same triangularity property, without a commutation assumption.
Source: Horn–Johnson (2013), Theorem 2.3.3; Gram–Schmidt preserves the flag. -/
theorem exists_orthonormalBasis_of_upper_triangular_basis
    {𝕜 E n ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [Fintype n] [DecidableEq n] [LinearOrder n]
    [LocallyFiniteOrderBot n] [WellFoundedLT n]
    (b : Basis n 𝕜 E) (f : ι → Module.End 𝕜 E)
    (htri : ∀ a, ((f a).toMatrix b b).IsUpperTriangular) :
    ∃ q : OrthonormalBasis n 𝕜 E, ∀ a, ((f a).toMatrix q.toBasis q.toBasis).IsUpperTriangular := by
  let q := InnerProductSpace.gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  let R := q.toBasis.toMatrix b
  let := Basis.invertibleToMatrix q.toBasis b
  have hR : R.IsUpperTriangular :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular _ _
  have hRinv : R⁻¹.IsUpperTriangular := Matrix.blockTriangular_inv_of_blockTriangular hR
  have hback : b.toMatrix q.toBasis = R⁻¹ :=
    (Matrix.inv_eq_left_inv (Basis.toMatrix_mul_toMatrix_flip b q.toBasis)).symm
  refine ⟨q, fun a => ?_⟩
  have hchange := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    q.toBasis b q.toBasis b (f a)
  rw [hback] at hchange
  rw [← hchange]
  exact (hR.mul (htri a)).mul hRinv

end NLAlib
