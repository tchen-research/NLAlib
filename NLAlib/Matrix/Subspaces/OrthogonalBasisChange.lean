import NLAlib.Matrix.Subspaces.GramIsometry
/-!
# Orthogonal coordinate changes of orthonormal bases

An orthogonal matrix acts on any real orthonormal basis, and conjugates the
coordinate matrix of every endomorphism by the usual formula.
-/

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Any real orthogonal change of coordinates can be realized by an
orthonormal basis, simultaneously for every endomorphism. Horn–Johnson
2013, Section 2.1; helper for canonical real Schur blocks. -/
theorem exists_orthonormalBasis_toMatrix_eq_conjugate {E n : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype n] [DecidableEq n] (b : OrthonormalBasis n ℝ E)
    (Q : Matrix n n ℝ) (hQ : HasOrthonormalCols Q) :
    ∃ c : OrthonormalBasis n ℝ E, ∀ T : Module.End ℝ E,
      T.toMatrix c.toBasis c.toBasis = Qᵀ * T.toMatrix b.toBasis b.toBasis * Q := by
  let L := hQ.toLinearIsometry
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp L.injective
  let e := LinearIsometryEquiv.ofSurjective L hsurj
  let c := (EuclideanSpace.basisFun n ℝ).map (e.trans b.repr.symm)
  have hchange : b.toBasis.toMatrix c.toBasis = Q := by
    ext i j
    simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, c, OrthonormalBasis.map_apply,
      LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
    change (Q *ᵥ (EuclideanSpace.basisFun n ℝ j).ofLp) i = Q i j
    simp [EuclideanSpace.basisFun_apply, Matrix.mulVec_single]
  have hback : c.toBasis.toMatrix b.toBasis = Qᵀ := by
    have hInv := Basis.toMatrix_mul_toMatrix_flip c.toBasis b.toBasis
    rw [hchange] at hInv
    calc
      c.toBasis.toMatrix b.toBasis = c.toBasis.toMatrix b.toBasis * (Q * Qᵀ) := by
        rw [mul_eq_one_comm.mp hQ, Matrix.mul_one]
      _ = Qᵀ := by rw [← Matrix.mul_assoc, hInv, Matrix.one_mul]
  refine ⟨c, fun T => ?_⟩
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    c.toBasis b.toBasis c.toBasis b.toBasis T
  rw [hback, hchange] at h
  exact h.symm

end NLAlib
