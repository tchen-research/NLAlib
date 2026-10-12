import NLAlib.ForMathlib.Analysis.OrderedSimultaneousSchur
import NLAlib.Matrix.SchurTriangularization

/-!
# Simultaneous unitary triangularization with one prescribed root order

One common unitary triangularizes every member of an arbitrary commuting
complex family while realizing any complete eigenvalue order of a designated
member, with no normality or diagonalizability assumption.
-/

noncomputable section
set_option autoImplicit false
open Module Polynomial
open scoped Matrix
namespace NLAlib

/-- Any complete ordering of a designated member's characteristic roots
can be realized within one simultaneous unitary upper triangularization of
an arbitrary commuting complex family. The same unitary works for every
family member, including an infinite family; every member's diagonal lists
its characteristic roots with multiplicity. Repetitions and empty matrix
dimension are allowed, without normality or diagonalizability assumptions.
Horn–Johnson 2013, Theorem 2.3.3; prescribed-order strengthening in
derivations Section gen:simultaneous.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_simultaneous_unitary_schur_triangularization_with_charpoly
    {n ι : Type*} [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℂ) (hcomm : Pairwise fun a b => Commute (A a) (A b))
    (order : Fin (Fintype.card n) ≃ n) (a₀ : ι) (d : n → ℂ)
    (hchar : (A a₀).charpoly = ∏ i, (X - C (d i))) :
    ∃ U : Matrix.unitaryGroup n ℂ, ∃ T : ι → Matrix n n ℂ,
      (∀ a, A a = (U : Matrix n n ℂ) * T a * (U : Matrix n n ℂ)ᴴ ∧
        (∀ i j, order.symm j < order.symm i → T a i j = 0) ∧
        (A a).charpoly = ∏ i, (X - C (T a i i))) ∧
      ∀ i, T a₀ i i = d i := by
  classical
  let f (a : ι) : Module.End ℂ (EuclideanSpace ℂ n) := (A a).toEuclideanLin
  have hfcomm : Pairwise fun a b => Commute (f a) (f b) := by
    intro a b hab
    exact (hcomm hab).map (Matrix.toLinAlgEquiv (PiLp.basisFun 2 ℂ n)).toRingHom
  let c := EuclideanSpace.basisFun n ℂ
  have hstd (a : ι) : (f a).toMatrix c.toBasis c.toBasis = A a :=
    LinearMap.toMatrix_toLin c.toBasis c.toBasis (A a)
  have hfchar : (f a₀).charpoly = ∏ i : Fin (Fintype.card n), (X - C (d (order i))) := by
    rw [← LinearMap.charpoly_toMatrix (f a₀) c.toBasis, hstd, hchar]
    exact (order.prod_comp (fun i => X - C (d i))).symm
  obtain ⟨b₀, htri₀, hdiag₀⟩ := exists_orthonormalBasis_simultaneous_upper_triangular_with_charpoly
    (Fintype.card n) f hfcomm (finrank_euclideanSpace (𝕜 := ℂ)) a₀ (fun i => d (order i)) hfchar
  let b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := b₀.reindex order
  let U : Matrix.unitaryGroup n ℂ :=
    ⟨c.toBasis.toMatrix b.toBasis, c.toMatrix_orthonormalBasis_mem_unitary b⟩
  let T (a : ι) : Matrix n n ℂ := (f a).toMatrix b.toBasis b.toBasis
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hUtU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hback : b.toBasis.toMatrix c.toBasis = (U : Matrix n n ℂ)ᴴ := by
    calc
      b.toBasis.toMatrix c.toBasis =
          b.toBasis.toMatrix c.toBasis * ((U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ) := by
            rw [hUU, Matrix.mul_one]
      _ = (U : Matrix n n ℂ)ᴴ := by
        rw [← Matrix.mul_assoc]
        change (b.toBasis.toMatrix c.toBasis * c.toBasis.toMatrix b.toBasis) * _ = _
        rw [Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mul]
  refine ⟨U, T, fun a => ?_, ?_⟩
  · have hA : A a = (U : Matrix n n ℂ) * T a * (U : Matrix n n ℂ)ᴴ := by
      have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
        c.toBasis b.toBasis c.toBasis b.toBasis (f a)
      rw [hback, hstd] at h
      exact h.symm
    have htri : ∀ i j, order.symm j < order.symm i → T a i j = 0 := by
      intro i j hij
      simp only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
      simpa only [b, OrthonormalBasis.reindex_apply] using htri₀ a (order.symm i) (order.symm j) hij
    have hTfin : ((T a).submatrix order order).IsUpperTriangular := by
      intro i j hij
      exact htri (order i) (order j) (by simpa using hij)
    have hTchar : (T a).charpoly = ∏ i, (X - C (T a i i)) := by
      calc
        (T a).charpoly = ((T a).submatrix order order).charpoly :=
          (Matrix.charpoly_reindex order.symm (T a)).symm
        _ = ∏ i : Fin (Fintype.card n), (X - C (T a (order i) (order i))) :=
          Matrix.charpoly_of_isUpperTriangular _ hTfin
        _ = _ := order.prod_comp (fun i => X - C (T a i i))
    refine ⟨hA, htri, ?_⟩
    rw [hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUtU, Matrix.one_mul, hTchar]
  · intro i
    simp only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
    simpa only [b, OrthonormalBasis.reindex_apply, Equiv.apply_symm_apply] using hdiag₀ (order.symm i)

end NLAlib
