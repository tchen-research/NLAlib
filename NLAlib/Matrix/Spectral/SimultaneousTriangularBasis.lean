import NLAlib.ForMathlib.Analysis.TriangularBasis
/-!
# Similarity and unitary simultaneous triangularization are equivalent

Gram–Schmidt preserves the common invariant flag supplied by any invertible
triangularizing similarity. No commutation assumption is needed.
Source: Horn–Johnson (2013), Theorem 2.3.3.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

/-- A family is simultaneously triangularizable by an invertible similarity
if and only if it is simultaneously triangularizable by a unitary matrix.
Source: Horn–Johnson (2013), Theorem 2.3.3; arbitrary families are allowed
and no commutation assumption is imposed.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_simultaneous_triangular_similarity_iff_unitary
    {n ι : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    [LocallyFiniteOrderBot n] [WellFoundedLT n] (A : ι → Matrix n n ℂ) :
    (∃ V : Matrix n n ℂ, IsUnit V ∧ ∀ a, (V⁻¹ * A a * V).IsUpperTriangular) ↔
      ∃ U : Matrix.unitaryGroup n ℂ,
        ∀ a, ((U : Matrix n n ℂ)ᴴ * A a * (U : Matrix n n ℂ)).IsUpperTriangular := by
  classical
  constructor
  · rintro ⟨V, hV, htri⟩
    let p := (EuclideanSpace.basisFun n ℂ).toBasis
    let b := p.map (Matrix.toLinearEquiv p V ((Matrix.isUnit_iff_isUnit_det V).mp hV))
    have hVcoord : p.toMatrix b = V := by
      ext i j
      simp only [b, Basis.toMatrix_apply, Basis.map_apply, Matrix.toLinearEquiv_apply]
      simpa only [LinearMap.toMatrix_apply] using
        congrArg (fun M : Matrix n n ℂ => M i j) (LinearMap.toMatrix_toLin p p V)
    have hbback : b.toMatrix p = V⁻¹ := by
      have h := Basis.toMatrix_mul_toMatrix_flip b p
      rw [hVcoord] at h
      exact (Matrix.inv_eq_left_inv h).symm
    let f (a : ι) : Module.End ℂ (EuclideanSpace ℂ n) := (A a).toEuclideanLin
    have hbtri (a : ι) : ((f a).toMatrix b b).IsUpperTriangular := by
      have hchange := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b p b p (f a)
      have hstd : (f a).toMatrix p p = A a := LinearMap.toMatrix_toLin p p (A a)
      rw [hstd, hbback, hVcoord] at hchange
      rw [← hchange]
      exact htri a
    obtain ⟨q, hqtri⟩ := exists_orthonormalBasis_of_upper_triangular_basis b f hbtri
    let U : Matrix.unitaryGroup n ℂ :=
      ⟨p.toMatrix q.toBasis, (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary q⟩
    have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
    have hback : q.toBasis.toMatrix p = (U : Matrix n n ℂ)ᴴ := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
        (Matrix.isUnit_det_of_right_inverse hUU) |>.mul_left_cancel
      change p.toMatrix q.toBasis * q.toBasis.toMatrix p =
        (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ
      rw [Basis.toMatrix_mul_toMatrix_flip, hUU]
    refine ⟨U, fun a => ?_⟩
    have hchange := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      q.toBasis p q.toBasis p (f a)
    have hstd : (f a).toMatrix p p = A a := LinearMap.toMatrix_toLin p p (A a)
    rw [hstd, hback] at hchange
    exact hchange ▸ hqtri a
  · rintro ⟨U, hU⟩
    have hUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
    have hinv : (U : Matrix n n ℂ)⁻¹ = (U : Matrix n n ℂ)ᴴ := Matrix.inv_eq_left_inv hUt
    refine ⟨U, (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hUt), ?_⟩
    simpa only [hinv] using hU

/-- The equivalence of similarity and unitary simultaneous triangularization
over arbitrary finite labels, with their order supplied by an enumeration.
Source: Horn–Johnson (2013), Theorem 2.3.3; no commutation assumption is used.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_simultaneous_triangular_similarity_iff_unitary_of_equiv
    {n ι : Type*} [Fintype n] [DecidableEq n] (A : ι → Matrix n n ℂ)
    (e : Fin (Fintype.card n) ≃ n) :
    (∃ V : Matrix n n ℂ, IsUnit V ∧
      ∀ a i j, e.symm j < e.symm i → (V⁻¹ * A a * V) i j = 0) ↔
      ∃ U : Matrix.unitaryGroup n ℂ,
        ∀ a i j, e.symm j < e.symm i →
          ((U : Matrix n n ℂ)ᴴ * A a * (U : Matrix n n ℂ)) i j = 0 := by
  let : LinearOrder n := LinearOrder.lift' e.symm e.symm.injective
  let o : n ≃o Fin (Fintype.card n) := { e.symm with map_rel_iff' := Iff.rfl }
  let : LocallyFiniteOrderBot n := o.locallyFiniteOrderBot
  let : WellFoundedLT n := ⟨(measure (fun i => (e.symm i).val)).wf⟩
  exact exists_simultaneous_triangular_similarity_iff_unitary A

end NLAlib
