import NLAlib.ForMathlib.Analysis.SimultaneousTriangularization
/-!
# Simultaneous unitary triangularization of commuting complex families

An arbitrary commuting family admits one common nonzero eigenvector when
the matrix shape is nonempty, and one common unitary triangularizing basis
in all dimensions. Source: Horn–Johnson (2013), Lemma 1.3.19 and Theorem 2.3.3.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- An arbitrary commuting family of nonempty complex square matrices has
a common nonzero eigenvector. Source: Horn–Johnson (2013), Lemma 1.3.19;
infinite and empty families are allowed.
atlas: simultaneous-diagonalization -/
theorem exists_common_mulVec_eigenvector_of_commute [Nonempty n]
    (A : ι → Matrix n n ℂ) (hcomm : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ (x : n → ℂ) (d : ι → ℂ), x ≠ 0 ∧ ∀ i, A i *ᵥ x = d i • x := by
  let f (i : ι) : Module.End ℂ (n → ℂ) := (A i).toLin'
  have hf : Pairwise fun i j => Commute (f i) (f j) := by
    intro i j hij
    exact (hcomm hij).map Matrix.toLinAlgEquiv'.toRingHom
  exact exists_common_eigenvector_of_pairwise_commute f hf

/-- A commuting complex family has a common unitary Schur basis, with each
diagonal giving that member's characteristic roots with multiplicity.
Source: Horn–Johnson (2013), Theorem 2.3.3; one explicit enumeration handles
arbitrary finite and empty matrix shapes, and the family may be infinite.
atlas: simultaneous-diagonalization -/
theorem exists_simultaneous_unitary_schur_triangularization
    (A : ι → Matrix n n ℂ) (hcomm : Pairwise fun i j => Commute (A i) (A j))
    (e : Fin (Fintype.card n) ≃ n) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (T : ι → Matrix n n ℂ), ∀ a,
      A a = (U : Matrix n n ℂ) * T a * (U : Matrix n n ℂ)ᴴ ∧
      (∀ i j, e.symm j < e.symm i → T a i j = 0) ∧
      (A a).charpoly = ∏ i, (Polynomial.X - Polynomial.C (T a i i)) := by
  classical
  let f (a : ι) : Module.End ℂ (EuclideanSpace ℂ n) := (A a).toEuclideanLin
  have hfcomm : Pairwise fun a b => Commute (f a) (f b) := by
    intro a b hab
    exact (hcomm hab).map (Matrix.toLinAlgEquiv (PiLp.basisFun 2 ℂ n)).toRingHom
  obtain ⟨b₀, hb₀⟩ := exists_orthonormalBasis_simultaneous_upper_triangular
    (Fintype.card n) f hfcomm (finrank_euclideanSpace (𝕜 := ℂ))
  let b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := b₀.reindex e
  let c := EuclideanSpace.basisFun n ℂ
  let U : Matrix.unitaryGroup n ℂ :=
    ⟨c.toBasis.toMatrix b.toBasis, c.toMatrix_orthonormalBasis_mem_unitary b⟩
  let T (a : ι) : Matrix n n ℂ := (f a).toMatrix b.toBasis b.toBasis
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hUUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hback : b.toBasis.toMatrix c.toBasis = (U : Matrix n n ℂ)ᴴ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
      (Matrix.isUnit_det_of_right_inverse hUU) |>.mul_left_cancel
    change c.toBasis.toMatrix b.toBasis * b.toBasis.toMatrix c.toBasis =
      (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ
    rw [Basis.toMatrix_mul_toMatrix_flip, hUU]
  refine ⟨U, T, fun a => ?_⟩
  have hA : A a = (U : Matrix n n ℂ) * T a * (U : Matrix n n ℂ)ᴴ := by
    have hbasis := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      c.toBasis b.toBasis c.toBasis b.toBasis (f a)
    have hstd : (f a).toMatrix c.toBasis c.toBasis = A a :=
      LinearMap.toMatrix_toLin c.toBasis c.toBasis (A a)
    calc
      A a = (f a).toMatrix c.toBasis c.toBasis := hstd.symm
      _ = c.toBasis.toMatrix b.toBasis * (f a).toMatrix b.toBasis b.toBasis *
          b.toBasis.toMatrix c.toBasis := hbasis.symm
      _ = _ := by rw [hback]
  have htri : ∀ i j, e.symm j < e.symm i → T a i j = 0 := by
    intro i j hij
    simp only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
    simpa only [b, OrthonormalBasis.reindex_apply] using hb₀ a (e.symm i) (e.symm j) hij
  have hTfin : ((T a).submatrix e e).IsUpperTriangular := by
    intro i j hij
    exact htri (e i) (e j) (by simpa using hij)
  have hchar : (T a).charpoly = ∏ i, (Polynomial.X - Polynomial.C (T a i i)) := by
    calc
      (T a).charpoly = ((T a).submatrix e e).charpoly := (Matrix.charpoly_reindex e.symm (T a)).symm
      _ = ∏ i : Fin (Fintype.card n), (Polynomial.X - Polynomial.C (T a (e i) (e i))) :=
        Matrix.charpoly_of_isUpperTriangular _ hTfin
      _ = _ := e.prod_comp (fun i => Polynomial.X - Polynomial.C (T a i i))
  refine ⟨hA, htri, ?_⟩
  rw [hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUUt, Matrix.one_mul, hchar]

end NLAlib
