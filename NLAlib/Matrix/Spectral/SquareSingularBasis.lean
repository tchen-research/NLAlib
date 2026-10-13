import NLAlib.Matrix.Spectral.SingularValueSpectrum
import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.Matrix.Norms.RankNorm
import NLAlib.Matrix.Norms.Reindex
import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!
# Square singular bases on finite coordinate types

The actual singular values diagonalize any square real matrix by independent
orthogonal row and column bases. Horn–Johnson 2013, Theorem 2.6.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- A square real matrix on arbitrary finite labels admits orthogonal singular
bases, with diagonal entries the actual ordered singular values assigned by
`Fintype.equivFin`. Empty dimensions are included. Horn–Johnson 2013,
Theorem 2.6.3; supports `cs-decomposition`. -/
theorem exists_orthogonal_transpose_mul_mul_eq_diagonal_singularValues
    {p : Type*} [Fintype p] [DecidableEq p] (A : Matrix p p ℝ) :
    ∃ V W : Matrix p p ℝ, HasOrthonormalCols V ∧ HasOrthonormalCols W ∧
      Vᵀ * A * W = Matrix.diagonal
        (fun i => singularValues A ((Fintype.equivFin p) i)) := by
  let e := Fintype.equivFin p
  let AF := A.reindex e e
  obtain ⟨V, W, h⟩ := exists_isSVD AF
  refine ⟨V.reindex e.symm e.symm, W.reindex e.symm e.symm,
    HasOrthonormalCols.reindex h.transpose_mul_left _ _,
    HasOrthonormalCols.reindex h.transpose_mul_right _ _, ?_⟩
  have hBack : AF.reindex e.symm e.symm = A := by ext i j; simp [AF]
  have hEq := congrArg (fun M : Matrix (Fin (Fintype.card p))
      (Fin (Fintype.card p)) ℝ => M.reindex e.symm e.symm) h.transpose_mul_mul
  rw [mul_reindex _ _ e.symm e.symm e.symm,
    mul_reindex _ _ e.symm e.symm e.symm, hBack] at hEq
  have hTr : Vᵀ.reindex e.symm e.symm = (V.reindex e.symm e.symm)ᵀ := rfl
  rw [hTr] at hEq
  refine hEq.trans ?_
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    rectDiag_apply, Matrix.diagonal_apply]
  have hij : ((e i : Fin (Fintype.card p)) : ℕ) = e j ↔ i = j := by
    constructor
    · exact fun h => e.injective (Fin.ext h)
    · rintro rfl; rfl
  simp only [hij]
  split_ifs with h
  · subst j
    exact congrFun (singularValues_reindex A _ _) _
  · rfl

end NLAlib
