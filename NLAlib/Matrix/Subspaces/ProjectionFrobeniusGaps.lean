import NLAlib.Matrix.Subspaces.ProjectionGaps
/-!
# Equal-rank Frobenius projection gaps

The equality of the two complementary Frobenius gaps is the ingredient
that retains the square-root-two coefficient in pseudoinverse perturbation.
Source: Stewart–Sun §I.5 and §III.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The residual Frobenius squares between equal-width orthonormal frames
are symmetric. Stewart–Sun §I.5, by the overlap trace identity. -/
theorem frobSq_residual_comm {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    frobSq (residual P Q)=frobSq (residual Q P) := by
  rw [frobSq_residual_eq_sub hP, frobSq_residual_eq_sub hQ,
    frobSq_frame_eq_card hP, frobSq_frame_eq_card hQ]
  congr 1
  rw [← frobSq_transpose (Pᵀ*Q), Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Equal-rank orthogonal projections have equal one-sided complementary
Frobenius gap squares. Stewart–Sun §I.5; ranks may be zero. -/
theorem frobSq_complement_mul_projector_eq_of_rank_eq {P Q : Matrix n n ℝ}
    (hPs : P.IsSymm) (hPi : IsIdempotentElem P)
    (hQs : Q.IsSymm) (hQi : IsIdempotentElem Q) (hr : P.rank=Q.rank) :
    frobSq ((1-Q)*P)=frobSq ((1-P)*Q) := by
  obtain ⟨U, hU, hPU⟩ := exists_frame_projector_of_isSymm_of_isIdempotentElem hPs hPi
  obtain ⟨V, hV, hQV⟩ := exists_frame_projector_of_isSymm_of_isIdempotentElem hQs hQi
  let e : Fin Q.rank ≃ Fin P.rank := finCongr hr.symm
  let V' := V.reindex (Equiv.refl n) e
  have hV' : HasOrthonormalCols V' := hV.reindex (Equiv.refl n) e
  have hVV : V'*V'ᵀ=V*Vᵀ := by
    simp only [V', Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
      Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hQV' : Q=V'*V'ᵀ := hQV.trans hVV.symm
  have hleft : (1-Q)*P=residual V' U*Uᵀ := by
    calc
      _ = (1-Q)*(U*Uᵀ) := congrArg (fun T => (1-Q)*T) hPU
      _ = (1-V'*V'ᵀ)*(U*Uᵀ) := congrArg (fun T => (1-T)*(U*Uᵀ)) hQV'
      _ = _ := by rw [residual_eq_one_sub_mul, Matrix.mul_assoc]
  have hright : (1-P)*Q=residual U V'*V'ᵀ := by
    calc
      _ = (1-P)*(V'*V'ᵀ) := congrArg (fun T => (1-P)*T) hQV'
      _ = (1-U*Uᵀ)*(V'*V'ᵀ) := congrArg (fun T => (1-T)*(V'*V'ᵀ)) hPU
      _ = _ := by rw [residual_eq_one_sub_mul, Matrix.mul_assoc]
  rw [hleft, hright, frobSq_mul_right_of_orthonormal hU.transpose_mul_self,
    frobSq_mul_right_of_orthonormal hV'.transpose_mul_self, frobSq_residual_comm hV' hU]

/-- Equal-rank one-sided Frobenius gaps agree also after placing the
projector on the left. Stewart–Sun §III.3, by transpose invariance. -/
theorem frobSq_projector_mul_complement_eq_complement_mul_of_rank_eq {P Q : Matrix n n ℝ}
    (hPs : P.IsSymm) (hPi : IsIdempotentElem P)
    (hQs : Q.IsSymm) (hQi : IsIdempotentElem Q) (hr : P.rank=Q.rank) :
    frobSq (Q*(1-P))=frobSq ((1-Q)*P) := by
  rw [← frobSq_transpose (Q*(1-P)), Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_one, hPs.eq, hQs.eq]
  exact (frobSq_complement_mul_projector_eq_of_rank_eq hPs hPi hQs hQi hr).symm

end NLAlib
