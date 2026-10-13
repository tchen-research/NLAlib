import NLAlib.Matrix.Subspaces.PrincipalAngleDefinitions
/-!
# Principal-angle invariance under frame changes

Equal-range isometric frames differ by an orthogonal right factor; the
overlap singular values therefore depend only on the two subspaces.
Source: Stewart–Sun §I.5; atlas `principal-angles-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- Relabelling only the ambient rows preserves the actual principal-angle
sine matrix exactly. Stewart–Sun, Section I.5; the column labels and therefore
the angle indices are unchanged. No orthonormality premise is needed.
Supports `wedin-sin-theta` on arbitrary finite coordinate labels. -/
theorem sinePrincipalAngles_reindex_rows {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (P Q : Matrix m n ℝ) (em : m ≃ p) :
    sinePrincipalAngles (P.reindex em (Equiv.refl n))
      (Q.reindex em (Equiv.refl n)) = sinePrincipalAngles P Q := by
  simp only [sinePrincipalAngles, principalAnglesFintype,
    Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- Two equal-range orthonormal frames are related by their orthogonal
overlap factor. Stewart–Sun §I.5, including empty frames. -/
theorem exists_orthogonal_frame_transition {P P' : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hP' : HasOrthonormalCols P')
    (hr : LinearMap.range P.mulVecLin=LinearMap.range P'.mulVecLin) :
    ∃ T : Matrix n n ℝ, Tᵀ*T=1 ∧ T*Tᵀ=1 ∧ P*T=P' := by
  let T := Pᵀ*P'
  have hPT : P*T=P' := mul_transpose_mul_eq_of_range_le hP hr.ge
  have hTT : Tᵀ*T=1 := by
    have hgram : (P*T)ᵀ*(P*T)=Tᵀ*T := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ P,
        (show Pᵀ * P = 1 from hP), Matrix.one_mul]
    rw [hPT, (show P'ᵀ * P' = 1 from hP')] at hgram
    exact hgram.symm
  exact ⟨T, hTT, mul_eq_one_comm.mp hTT, hPT⟩

omit [DecidableEq m] in
/-- Changing the left orthonormal frame within its range preserves every
principal angle. Stewart–Sun §I.5; no spectral-gap condition is used.
atlas: principal-angles-def (partial) -/
theorem principalAngles_eq_of_range_eq_left {P P' : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hP' : HasOrthonormalCols P')
    (hr : LinearMap.range P.mulVecLin=LinearMap.range P'.mulVecLin) (Q : Matrix m n ℝ) :
    principalAnglesFintype P Q=principalAnglesFintype P' Q := by
  obtain ⟨T, _, hT, hPT⟩ := exists_orthogonal_frame_transition hP hP' hr
  have heq : P'ᵀ*Q=Tᵀ*(Pᵀ*Q) := by
    rw [← hPT, Matrix.transpose_mul, Matrix.mul_assoc]
  have hTt : Tᵀᵀ*Tᵀ=1 := by simpa only [Matrix.transpose_transpose] using hT
  have hh : singularValues ((Tᵀ*(Pᵀ*Q)).reindex (Fintype.equivFin n) (Fintype.equivFin n)) =
      singularValues ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) := by
    rw [singularValues_reindex, singularValues_reindex, singularValues_isometry_mul (H := Tᵀ) hTt]
  funext i
  simp only [principalAnglesFintype, heq]
  rw [hh]

omit [DecidableEq m] in
/-- Changing the right orthonormal frame within its range preserves every
principal angle. Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem principalAngles_eq_of_range_eq_right {Q Q' : Matrix m n ℝ}
    (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q')
    (hr : LinearMap.range Q.mulVecLin=LinearMap.range Q'.mulVecLin) (P : Matrix m n ℝ) :
    principalAnglesFintype P Q=principalAnglesFintype P Q' := by
  rw [principalAngles_comm P Q, principalAngles_comm P Q']
  exact principalAngles_eq_of_range_eq_left hQ hQ' hr P

omit [DecidableEq m] in
/-- The principal angles depend only on the pair of ranges.
Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem principalAngles_eq_of_range_eq {P P' Q Q' : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hP' : HasOrthonormalCols P')
    (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q')
    (hrP : LinearMap.range P.mulVecLin=LinearMap.range P'.mulVecLin)
    (hrQ : LinearMap.range Q.mulVecLin=LinearMap.range Q'.mulVecLin) :
    principalAnglesFintype P Q=principalAnglesFintype P' Q' :=
  (principalAngles_eq_of_range_eq_left hP hP' hrP Q).trans
    (principalAngles_eq_of_range_eq_right hQ hQ' hrQ P')

end NLAlib
