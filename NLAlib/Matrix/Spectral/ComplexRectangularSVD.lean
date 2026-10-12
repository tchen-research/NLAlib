import NLAlib.Matrix.Spectral.ComplexSquareSingularBasis
import NLAlib.Matrix.Functions.ComplexDiagonalFilter
/-!
# Rectangular complex singular value decomposition

Complex unitary row and column factors diagonalize every rectangular matrix
using its actual, nonnegative, decreasing, zero-padded singular values.
-/

noncomputable section
open Module
open scoped InnerProductSpace Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Every complex rectangular matrix has unitary singular bases with its
actual singular values on the rectangular diagonal. Zero dimensions and
deficient rank are included. Horn–Johnson 2013, Theorem 2.6.3;
complex oblique-projection canonical-form helper. -/
theorem exists_complex_rectangular_svd {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ V : Matrix.unitaryGroup (Fin m) ℂ, ∃ W : Matrix.unitaryGroup (Fin n) ℂ,
      (V : Matrix (Fin m) (Fin m) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) =
        (rectDiag (fun i => A.toEuclideanLin.singularValues i) :
          Matrix (Fin m) (Fin n) ℝ).map Complex.ofReal := by
  let a := A.toEuclideanLin
  let h := a.isSymmetric_adjoint_comp_self
  have hdim : finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := finrank_euclideanSpace_fin
  let b := h.eigenvectorBasis hdim
  let c := EuclideanSpace.basisFun (Fin n) ℂ
  let W : Matrix.unitaryGroup (Fin n) ℂ :=
    ⟨c.toBasis.toMatrix b.toBasis, c.toMatrix_orthonormalBasis_mem_unitary b⟩
  let d : ℕ → ℝ := fun i => a.singularValues i
  let D : Matrix (Fin m) (Fin n) ℂ := (rectDiag d).map Complex.ofReal
  have hz (j : Fin n) (hj : ¬j.val < m) : d j = 0 := by
    apply a.singularValues_eq_zero_iff_le_finrank_range.mpr
    have hr : finrank ℂ a.range = A.rank := by
      exact (Matrix.rank_eq_finrank_range_toLin A
        (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).symm
    rw [hr]
    exact A.rank_le_height.trans (Nat.le_of_not_gt hj)
  have hcol (i j : Fin n) : (W : Matrix (Fin n) (Fin n) ℂ) i j = b j i := by
    simp only [W, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis]
    rfl
  have hAw (i : Fin m) (j : Fin n) :
      (A * (W : Matrix (Fin n) (Fin n) ℂ)) i j = a (b j) i := by
    simp only [Matrix.mul_apply, hcol]
    rfl
  have hinner (i j : Fin n) : inner ℂ (a (b i)) (a (b j)) =
      ((if i = j then d j ^ 2 else 0 : ℝ) : ℂ) := by
    rw [← LinearMap.adjoint_inner_right]
    change inner ℂ (b i) ((LinearMap.adjoint a ∘ₗ a) (b j)) = _
    rw [h.apply_eigenvectorBasis hdim j, inner_smul_right, b.inner_eq_ite]
    have hs := a.sq_singularValues_fin hdim j
    change d j ^ 2 = h.eigenvalues hdim j at hs
    rw [← hs]
    split_ifs <;> simp
  have hDD : Dᴴ * D = Matrix.diagonal (fun i : Fin n => ((d i) ^ 2 : ℂ)) := by
    rw [show Dᴴ = (rectDiag d : Matrix (Fin m) (Fin n) ℝ)ᵀ.map Complex.ofReal from
      conjTranspose_map_ofReal _, ← map_ofReal_mul, transpose_rectDiag_mul_rectDiag]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i.val < m <;> simp [Matrix.map_apply, hi, hz i]
    · simp [Matrix.map_apply, hij]
  have hGram : (A * (W : Matrix (Fin n) (Fin n) ℂ))ᴴ *
      (A * (W : Matrix (Fin n) (Fin n) ℂ)) = Dᴴ * D := by
    rw [hDD]
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hAw]
    rw [show (∑ x, star (a (b i) x) * a (b j) x) = inner ℂ (a (b i)) (a (b j)) by
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm], hinner]
    by_cases hij : i = j <;> simp [hij]
  obtain ⟨V, hV⟩ := exists_unitary_mul_eq_of_gram_eq (A * (W : Matrix (Fin n) (Fin n) ℂ)) D hGram
  refine ⟨V, W, ?_⟩
  rw [Matrix.mul_assoc, ← hV, ← Matrix.mul_assoc,
    show (V : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ) = 1
      from Unitary.coe_star_mul_self V, Matrix.one_mul]

end NLAlib
