import NLAlib.Matrix.Spectral.SchurTriangularization
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Upper triangular primary blocks

Generalized eigenspaces form an internal direct sum. Orthonormal
triangularization inside each primary space then yields one similarity to
upper triangular blocks, each having just its indexing eigenvalue.
Source: Horn–Johnson (2013), §2.4; atlas `sylvester-equation`.
-/

noncomputable section
open Module
open scoped Matrix InnerProductSpace

namespace NLAlib

/-- Every eigenvalue of the restriction to a maximal generalized eigenspace
is the eigenvalue indexing that space. Source: Horn–Johnson (2013), §2.4;
distinct generalized eigenspaces have zero intersection. -/
theorem eq_of_hasEigenvalue_restrict_maxGenEigenspace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : Module.End K E) (μ : K)
    (hpres : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ))
    {ν : K} (hν : Module.End.HasEigenvalue (f.restrict hpres) ν) : ν = μ := by
  obtain ⟨x, hx, hxne⟩ := hν.exists_hasEigenvector
  have heig : f x.val = ν • x.val :=
    congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hx)
  have hxν : x.val ∈ f.maxGenEigenspace ν :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr heig)
  by_contra hne
  have hz : x.val = 0 := by
    have hi : x.val ∈ f.maxGenEigenspace ν ⊓ f.maxGenEigenspace μ := ⟨hxν, x.property⟩
    rw [(f.disjoint_genEigenspace hne ⊤ ⊤).eq_bot] at hi
    exact hi
  exact hxne (Subtype.ext hz)

/-- Every complex matrix is similar to the direct sum of single-eigenvalue
upper triangular primary blocks. The block index is the scalar itself;
zero-size blocks are permitted, and the equivalence with the original index
type certifies that only finitely many nonempty blocks occur. Source:
Horn–Johnson (2013), §2.4; empty matrices are included.
atlas: sylvester-equation (partial) -/
theorem exists_similarity_primary_upperTriangular
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ∃ (d : ℂ → ℕ) (e : (Σ μ : ℂ, Fin (d μ)) ≃ n)
      (S : Matrix n n ℂ) (T : ∀ μ : ℂ, Matrix (Fin (d μ)) (Fin (d μ)) ℂ),
      IsUnit S ∧ (S⁻¹ * A * S).submatrix e e = Matrix.blockDiagonal' T ∧
      (∀ μ, (T μ).IsUpperTriangular) ∧ (∀ μ i, T μ i i = μ) := by
  classical
  let E := EuclideanSpace ℂ n
  let f : Module.End ℂ E := A.toEuclideanLin
  let W (μ : ℂ) := f.maxGenEigenspace μ
  have hpres (μ : ℂ) : Set.MapsTo f (W μ) (W μ) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  let C (μ : ℂ) : Module.End ℂ (W μ) := f.restrict (hpres μ)
  let d (μ : ℂ) := Module.finrank ℂ (W μ)
  choose b hb using fun μ : ℂ =>
    exists_orthonormalBasis_upper_triangular (E := W μ) (d μ) (C μ) rfl
  let T (μ : ℂ) : Matrix (Fin (d μ)) (Fin (d μ)) ℂ :=
    (C μ).toMatrix (b μ).toBasis (b μ).toBasis
  have htri (μ : ℂ) : (T μ).IsUpperTriangular := by
    intro i j hij
    simpa only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply] using hb μ i j hij
  have hdiag (μ : ℂ) (i : Fin (d μ)) : T μ i i = μ := by
    have hroot : (T μ).charpoly.IsRoot (T μ i i) := by
      rw [Matrix.charpoly_of_isUpperTriangular _ (htri μ)]
      simp only [Polynomial.IsRoot, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    have hν : (C μ).HasEigenvalue (T μ i i) := by
      apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      simpa only [T, LinearMap.charpoly_toMatrix] using hroot
    exact eq_of_hasEigenvalue_restrict_maxGenEigenspace f μ (hpres μ) hν
  have hsum : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      f.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top f)
  let c := hsum.collectedBasis (fun μ => (b μ).toBasis)
  let : Fintype (Σ μ : ℂ, Fin (d μ)) := FiniteDimensional.fintypeBasisIndex c
  have hcard : Fintype.card (Σ μ : ℂ, Fin (d μ)) = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis c, finrank_euclideanSpace]
  let e : (Σ μ : ℂ, Fin (d μ)) ≃ n := Fintype.equivOfCardEq hcard
  let q := c.reindex e
  let p := (EuclideanSpace.basisFun n ℂ).toBasis
  let S := p.toMatrix q
  let := Basis.invertibleToMatrix p q
  have hS : IsUnit S := isUnit_of_invertible S
  have hSinv : S⁻¹ = q.toMatrix p := Matrix.inv_eq_left_inv (Basis.toMatrix_mul_toMatrix_flip q p)
  have hM : S⁻¹ * A * S = f.toMatrix q q := by
    have hstd : f.toMatrix p p = A := LinearMap.toMatrix_toLin p p A
    rw [hSinv]
    nth_rw 1 [← hstd]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix q p q p f
  have hblock : f.toMatrix c c = Matrix.blockDiagonal' T := by
    ext ⟨μ, i⟩ ⟨ν, j⟩
    have hc : c ⟨ν, j⟩ = (b ν j : E) := by
      simp only [c, DirectSum.IsInternal.collectedBasis_coe, OrthonormalBasis.coe_toBasis]
    have hfc : f (c ⟨ν, j⟩) ∈ W ν := by rw [hc]; exact hpres ν (b ν j).property
    rw [LinearMap.toMatrix_apply]
    by_cases hμν : μ = ν
    · subst ν
      rw [Matrix.blockDiagonal'_apply_eq]
      change (hsum.collectedBasis (fun μ => (b μ).toBasis)).repr (f (c ⟨μ, j⟩)) ⟨μ, i⟩ = _
      rw [hsum.collectedBasis_repr_of_mem _ hfc]
      simpa only [T, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis] using
        congrArg (fun z : W μ => (b μ).toBasis.repr z i)
        (show (⟨f (c ⟨μ, j⟩), hfc⟩ : W μ) = C μ (b μ j) from
          Subtype.ext (congrArg f hc))
    · rw [Matrix.blockDiagonal'_apply_ne T i j hμν]
      exact hsum.collectedBasis_repr_of_mem_ne _ (Ne.symm hμν) hfc
  refine ⟨d, e, S, T, hS, ?_, htri, hdiag⟩
  rw [hM]
  have hcoords : (f.toMatrix q q).submatrix e e = f.toMatrix c c := by
    ext i j
    simp only [Matrix.submatrix_apply, LinearMap.toMatrix_apply, q, Basis.reindex_apply,
      Basis.repr_reindex_apply, Equiv.symm_apply_apply]
  exact hcoords.trans hblock

end NLAlib
