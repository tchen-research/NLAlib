import NLAlib.Matrix.Subspaces.ComplexGramIsometry
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Complex square singular bases on finite coordinate types

Sorted eigenvectors of the Gram matrix and a range isometry give the actual
complex singular value decomposition, including zero singular values.
-/

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- A complex square matrix admits unitary singular bases whose diagonal
is its actual ordered singular-value list. Arbitrary finite labels and
empty dimension are included. Horn–Johnson 2013, Theorem 2.6.3;
complex CS helper. -/
theorem exists_unitary_conjTranspose_mul_mul_eq_diagonal_singularValues
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ∃ V W : Matrix.unitaryGroup n ℂ,
      (V : Matrix n n ℂ)ᴴ * A * (W : Matrix n n ℂ) = Matrix.diagonal
        (fun i => (A.toEuclideanLin.singularValues ((Fintype.equivFin n) i) : ℂ)) := by
  let a := A.toEuclideanLin
  let h := a.isSymmetric_adjoint_comp_self
  have hdim : finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace
  let b₀ := h.eigenvectorBasis hdim
  let b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := b₀.reindex (Fintype.equivFin n).symm
  let c := EuclideanSpace.basisFun n ℂ
  let W : Matrix.unitaryGroup n ℂ :=
    ⟨c.toBasis.toMatrix b.toBasis, c.toMatrix_orthonormalBasis_mem_unitary b⟩
  let d : n → ℝ := fun i => a.singularValues ((Fintype.equivFin n) i)
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (d i : ℂ))
  have hcol (i j : n) : (W : Matrix n n ℂ) i j = b j i := by
    simp only [W, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis]
    rfl
  have hAw (i j : n) : (A * (W : Matrix n n ℂ)) i j = a (b j) i := by
    simp only [Matrix.mul_apply, hcol]
    rfl
  have hinner (i j : n) : inner ℂ (a (b i)) (a (b j)) =
      if i = j then ((d j) ^ 2 : ℝ) else 0 := by
    rw [← LinearMap.adjoint_inner_right]
    have heig := h.apply_eigenvectorBasis hdim ((Fintype.equivFin n) j)
    have hbj : b j = b₀ ((Fintype.equivFin n) j) := by
      simp only [b, OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    rw [hbj]
    change inner ℂ (b i) ((LinearMap.adjoint a ∘ₗ a) (b₀ ((Fintype.equivFin n) j))) = _
    rw [heig, inner_smul_right, ← hbj, b.inner_eq_ite]
    have hs := a.sq_singularValues_fin hdim ((Fintype.equivFin n) j)
    change (d j) ^ 2 = h.eigenvalues hdim ((Fintype.equivFin n) j) at hs
    rw [← hs]
    split_ifs <;> simp
  have hGram : (A * (W : Matrix n n ℂ))ᴴ * (A * (W : Matrix n n ℂ)) = Dᴴ * D := by
    have hDD : Dᴴ * D = Matrix.diagonal (fun i => ((d i) ^ 2 : ℂ)) := by
      simp [D, Matrix.diagonal_conjTranspose, pow_two]
    rw [hDD]
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hAw]
    rw [show (∑ x, star (a (b i) x) * a (b j) x) = inner ℂ (a (b i)) (a (b j)) by
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]]
    rw [hinner]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  obtain ⟨V, hV⟩ := exists_unitary_mul_eq_of_gram_eq (A * (W : Matrix n n ℂ)) D hGram
  refine ⟨V, W, ?_⟩
  rw [Matrix.mul_assoc, ← hV, ← Matrix.mul_assoc,
    show (V : Matrix n n ℂ)ᴴ * (V : Matrix n n ℂ) = 1 from Unitary.coe_star_mul_self V,
    Matrix.one_mul]

end NLAlib
