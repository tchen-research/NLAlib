import NLAlib.Matrix.Factorizations.QRCompletion
/-!
# Orthogonal completion with separately labelled block columns

An isometric frame extends to an orthogonal matrix whose first summand is the
given frame, on arbitrary finite labels. Horn–Johnson 2013, Section 2.1.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Complete an orthonormal frame to two separately labelled column blocks
when their total dimension is the ambient dimension. The left and right Gram
identities are both supplied, including empty blocks. Horn–Johnson 2013,
Section 2.1; supports the oblique-projector part of `cs-decomposition`. -/
theorem exists_orthogonal_sum_completion {m p q : Type*}
    [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (Q : Matrix m p ℝ) (hQ : HasOrthonormalCols Q)
    (hcard : Fintype.card p + Fintype.card q = Fintype.card m) :
    ∃ H : Matrix m (p ⊕ q) ℝ,
      HasOrthonormalCols H ∧ H * Hᵀ = 1 ∧ H.submatrix id Sum.inl = Q := by
  let e : (p ⊕ q) ≃ m := Fintype.equivOfCardEq (by simpa using hcard)
  let f : p ↪ m := ⟨fun i => e (Sum.inl i), e.injective.comp Sum.inl_injective⟩
  obtain ⟨W, _, hW, hFirst, _, _, _⟩ := exists_full_qr_completion hQ
    (show Q * (1 : Matrix p p ℝ) = Q from Matrix.mul_one _) f
  let H := W.reindex (Equiv.refl m) e.symm
  refine ⟨H, hW.reindex _ _, ?_, ?_⟩
  · change W.submatrix id e * Wᵀ.submatrix e id = 1
    rw [Matrix.submatrix_mul_equiv W Wᵀ id e id, Matrix.submatrix_id_id]
    exact mul_eq_one_comm.mp hW
  · exact hFirst

end NLAlib
