import NLAlib.Matrix.Subspaces.ProjectionGaps
/-!
# Equal-rank Frobenius projection gaps

The equality of the two complementary Frobenius gaps of equal-rank orthogonal projectors
(Hermitian idempotents over `[RCLike 𝕜]`) is the ingredient that retains the `√2` coefficient in
pseudoinverse perturbation. Stewart–Sun 1990, §I.5 and §III.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

omit [DecidableEq m] in
/-- The residual Frobenius squares between equal-width frames with orthonormal columns are
symmetric: `‖(I − PPᴴ)Q‖_F² = ‖(I − QQᴴ)P‖_F²`. Stewart–Sun 1990, §I.5. -/
theorem frobSq_residual_comm {P Q : Matrix m n 𝕜}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    frobSq (projResidual P Q) = frobSq (projResidual Q P) := by
  rw [frobSq_residual_eq_sub hP, frobSq_residual_eq_sub hQ, frobSq_frame_eq_card hP,
    frobSq_frame_eq_card hQ]
  congr 1
  rw [← frobSq_conjTranspose (Pᴴ * Q), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- Equal-rank orthogonal projections have equal one-sided complementary Frobenius gap
squares: `‖(I − Q)P‖_F² = ‖(I − P)Q‖_F²`. Stewart–Sun 1990, §I.5; ranks may be zero. -/
theorem frobSq_complement_mul_projector_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hPs : P.IsHermitian) (hPi : IsIdempotentElem P)
    (hQs : Q.IsHermitian) (hQi : IsIdempotentElem Q) (hr : P.rank = Q.rank) :
    frobSq ((1 - Q) * P) = frobSq ((1 - P) * Q) := by
  obtain ⟨U, hU, hPU⟩ := exists_frame_projector_of_isHermitian_of_isIdempotentElem hPs hPi
  obtain ⟨V, hV, hQV⟩ := exists_frame_projector_of_isHermitian_of_isIdempotentElem hQs hQi
  let e : Fin Q.rank ≃ Fin P.rank := finCongr hr.symm
  let V' := V.reindex (Equiv.refl n) e
  have hV' : HasOrthonormalCols V' := hV.reindex (Equiv.refl n) e
  have hVV : V' * V'ᴴ = V * Vᴴ := by
    simp only [V', Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hQV' : Q = V' * V'ᴴ := hQV.trans hVV.symm
  have hleft : (1 - Q) * P = projResidual V' U * Uᴴ := by
    rw [hPU, hQV', residual_eq_one_sub_mul, Matrix.mul_assoc]
  have hright : (1 - P) * Q = projResidual U V' * V'ᴴ := by
    rw [hQV', hPU, residual_eq_one_sub_mul, Matrix.mul_assoc]
  rw [hleft, hright, frobSq_mul_right_of_orthonormal hU, frobSq_mul_right_of_orthonormal hV',
    frobSq_residual_comm hV' hU]

/-- Equal-rank one-sided Frobenius gaps agree also after placing the projector on the left:
`‖Q(I − P)‖_F² = ‖(I − Q)P‖_F²`. Stewart–Sun 1990, §III.3, by adjoint invariance. -/
theorem frobSq_projector_mul_complement_eq_complement_mul_of_rank_eq {P Q : Matrix n n 𝕜}
    (hPs : P.IsHermitian) (hPi : IsIdempotentElem P)
    (hQs : Q.IsHermitian) (hQi : IsIdempotentElem Q) (hr : P.rank = Q.rank) :
    frobSq (Q * (1 - P)) = frobSq ((1 - Q) * P) := by
  rw [← frobSq_conjTranspose (Q * (1 - P)), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPs.eq, hQs.eq]
  exact (frobSq_complement_mul_projector_eq_of_rank_eq hPs hPi hQs hQi hr).symm

end NLAlib
