import NLAlib.Matrix.Norms.EuclideanOperatorBounds
import NLAlib.Matrix.Spectral.FiniteIndexTransport
import NLAlib.Matrix.Subspaces.OrthonormalBasisMatrix
/-!
# Distances between orthogonal projections

The orthogonal-support decomposition gives the norm of a projection difference
as the maximum of its two one-sided gaps. Equal-rank frames identify the gaps
through their overlap Gram matrices. Atlas: `principal-angles-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Squared Euclidean lengths split across a symmetric idempotent and its
orthogonal complement. Stewart–Sun §I.5, used for principal angles. -/
theorem dotProduct_projector_add_complement {P : Matrix n n ℝ}
    (hs : P.IsSymm) (hp : IsIdempotentElem P) (x : n → ℝ) :
    (P *ᵥ x) ⬝ᵥ (P *ᵥ x) + ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x) = x ⬝ᵥ x := by
  have hP := mulVec_dotProduct_mulVec_self P x
  rw [hs.eq, show P * P = P from hp] at hP
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, dotProduct_comm (P *ᵥ x) x, hP]
  ring

/-- Two blocks with orthogonal input and output supports have norm at most
the maximum block norm. Stewart–Sun §I.5; the proof uses Pythagoras twice. -/
theorem specNorm_add_le_max_of_projector_supports {P : Matrix n n ℝ}
    (hs : P.IsSymm) (hp : IsIdempotentElem P) {X Y : Matrix m n ℝ}
    (hX : X * P = X) (hY : Y * (1 - P) = Y) (hXY : Xᵀ * Y = 0) :
    specNorm (X + Y) ≤ max (specNorm X) (specNorm Y) := by
  apply specNorm_le_of_mulVec_sq_le (le_trans (specNorm_nonneg X) (le_max_left _ _))
  intro x
  have horth : (X *ᵥ x) ⬝ᵥ (Y *ᵥ x) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, hXY]
    simp
  have hx := sum_sq_mulVec_le_specNorm_sq X (P *ᵥ x)
  have hy := sum_sq_mulVec_le_specNorm_sq Y ((1 - P) *ᵥ x)
  simp only [Matrix.mulVec_mulVec, hX, hY] at hx hy
  have hx' : (X *ᵥ x) ⬝ᵥ (X *ᵥ x) ≤ specNorm X ^ 2 * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)) := by
    simpa [dotProduct, sq] using hx
  have hy' : (Y *ᵥ x) ⬝ᵥ (Y *ᵥ x) ≤ specNorm Y ^ 2 * (((1-P) *ᵥ x) ⬝ᵥ ((1-P) *ᵥ x)) := by
    simpa [dotProduct, sq] using hy
  have hxn : 0 ≤ (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := dotProduct_self_nonneg _
  have hyn : 0 ≤ ((1-P) *ᵥ x) ⬝ᵥ ((1-P) *ᵥ x) := dotProduct_self_nonneg _
  have hxx := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (specNorm_nonneg X) (le_max_left (specNorm X) (specNorm Y)) 2) hxn
  have hyy := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (specNorm_nonneg Y) (le_max_right (specNorm X) (specNorm Y)) 2) hyn
  rw [Matrix.add_mulVec, add_dotProduct, dotProduct_add, dotProduct_add,
    horth, dotProduct_comm (Y *ᵥ x) (X *ᵥ x), horth]
  have hsplit := dotProduct_projector_add_complement hs hp x
  nlinarith

/-- Complementary orthogonal-projector gap decomposition. Stewart–Sun §I.5.
This algebraic identity does not require equality of ranks. -/
theorem sub_projector_eq_complement_mul_sub {P Q : Matrix n n ℝ} :
    P - Q = (1 - Q) * P - Q * (1 - P) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  abel

/-- The norm of a difference of orthogonal projections is the maximum of
the two one-sided gaps. Stewart–Sun §I.5; ranks may differ and may be zero. -/
theorem specNorm_sub_projector_eq_max {P Q : Matrix n n ℝ}
    (hPs : P.IsSymm) (hPi : IsIdempotentElem P)
    (hQs : Q.IsSymm) (hQi : IsIdempotentElem Q) :
    specNorm (P - Q) = max (specNorm ((1 - Q) * P)) (specNorm (Q * (1 - P))) := by
  have hPP : P * P = P := hPi
  have hQQ : Q * Q = Q := hQi
  have hPc : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hQz : (1 - Q) * Q = 0 := by simp [Matrix.sub_mul, hQQ]
  apply le_antisymm
  · rw [sub_projector_eq_complement_mul_sub, sub_eq_add_neg]
    have hh := specNorm_add_le_max_of_projector_supports hPs hPi
      (X := (1-Q)*P) (Y := -(Q*(1-P)))
      (by simp [Matrix.mul_assoc, hPP]) (by simp [Matrix.mul_assoc, hPc])
      (by
        simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
          hPs.eq, hQs.eq, Matrix.mul_neg]
        rw [← Matrix.mul_assoc, Matrix.mul_assoc P (1-Q) Q, hQz]
        simp)
    simpa only [specNorm_neg] using hh
  · apply max_le
    · have heq : (1-Q)*P = (P-Q)*P := by simp [Matrix.sub_mul, hPP]
      rw [heq]
      exact (specNorm_mul_le _ _).trans (by
        have hh := specNorm_le_one_of_isSymm_of_isIdempotentElem hPs hPi
        nlinarith [specNorm_nonneg (P-Q)])
    · have heq : Q*(1-P) = -(P-Q)*(1-P) := by
        simp only [Matrix.neg_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, hPP]
        abel
      rw [heq]
      have hPcs : (1-P).IsSymm := by simp [Matrix.IsSymm, hPs.eq]
      exact (specNorm_mul_le _ _).trans (by
        have hh := specNorm_le_one_of_isSymm_of_isIdempotentElem hPcs hPc
        rw [specNorm_neg]
        nlinarith [specNorm_nonneg (P-Q)])

/-- The two square overlap Gram defects have the same norm, since an SVD
diagonalizes them with the same singular-value squares. Stewart–Sun §I.5. -/
theorem specNorm_one_sub_transpose_mul_eq_one_sub_mul_transpose (C : Matrix n n ℝ) :
    specNorm (1 - Cᵀ * C) = specNorm (1 - C * Cᵀ) := by
  let e := Fintype.equivFin n
  let CF := C.reindex e e
  have hf : specNorm (1 - CFᵀ * CF) = specNorm (1 - CF * CFᵀ) := by
    obtain ⟨U, V, h⟩ := exists_isSVD CF
    have hdiag : (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ) -
        Matrix.diagonal (fun j : Fin (Fintype.card n) => singularValues CF j ^ 2) =
          Matrix.diagonal (fun j : Fin (Fintype.card n) => 1 - singularValues CF j ^ 2) := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    have hleft : 1 - CFᵀ * CF =
        V * Matrix.diagonal (fun j : Fin (Fintype.card n) => 1 - singularValues CF j ^ 2) * Vᵀ := by
      rw [← hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        h.mul_transpose_right, h.transpose_mul_self]
    have hright : 1 - CF * CFᵀ =
        U * Matrix.diagonal (fun j : Fin (Fintype.card n) => 1 - singularValues CF j ^ 2) * Uᵀ := by
      rw [← hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        h.mul_transpose_left, h.mul_transpose_self]
    rw [hleft, hright,
      specNorm_mul_transpose_right_of_hasOrthonormalCols h.transpose_mul_right,
      specNorm_mul_left_of_hasOrthonormalCols h.transpose_mul_right,
      specNorm_mul_transpose_right_of_hasOrthonormalCols h.transpose_mul_left,
      specNorm_mul_left_of_hasOrthonormalCols h.transpose_mul_left]
  have hleft : 1 - CFᵀ * CF = (1 - Cᵀ*C).reindex e e := by
    simp only [CF, Matrix.reindex_apply, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv]
    change 1 - (Cᵀ*C).submatrix e.symm e.symm =
      (1 : Matrix n n ℝ).submatrix e.symm e.symm - (Cᵀ*C).submatrix e.symm e.symm
    rw [Matrix.submatrix_one_equiv]
  have hright : 1 - CF * CFᵀ = (1 - C*Cᵀ).reindex e e := by
    simp only [CF, Matrix.reindex_apply, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv]
    change 1 - (C*Cᵀ).submatrix e.symm e.symm =
      (1 : Matrix n n ℝ).submatrix e.symm e.symm - (C*Cᵀ).submatrix e.symm e.symm
    rw [Matrix.submatrix_one_equiv]
  rw [hleft, hright, specNorm_reindex, specNorm_reindex] at hf
  exact hf

/-- The residual Gram equals the identity minus the overlap Gram for
orthonormal frames: `(residual P Q)ᵀ (residual P Q) = I − (PᵀQ)ᵀ(PᵀQ)`. The frame widths may
differ, and empty frames are allowed. Stewart–Sun, §I.5 (Theorem I.5.5). -/
theorem transpose_residual_mul_residual_eq_one_sub_overlap {p : Type*} [DecidableEq p]
    {P : Matrix m n ℝ} {Q : Matrix m p ℝ} (hP : HasOrthonormalCols P)
    (hQ : HasOrthonormalCols Q) :
    (residual P Q)ᵀ * residual P Q = 1 - (Pᵀ*Q)ᵀ*(Pᵀ*Q) := by
  rw [residual_eq_one_sub_mul, Matrix.transpose_mul,
    show (1-P*Pᵀ)ᵀ = 1-P*Pᵀ by simp,
    Matrix.mul_assoc, ← Matrix.mul_assoc (1-P*Pᵀ),
    one_sub_mul_transpose_idem hP, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, hQ.transpose_mul_self]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- **Symmetry of `θ_max` for equal dimensions.** The two residuals between equal-width
orthonormal frames have equal spectral norm: `‖(I − PPᵀ)Q‖₂ = ‖(I − QQᵀ)P‖₂`. False for unequal
widths (a line inside a plane has `θ = 0` one way and `π/2` the other). Stewart–Sun, Thm I.5.5;
Golub–Van Loan 2013, Thm 2.5.1; the square overlap SVD handles zero angles.
atlas: principal-angles-def (partial) -/
theorem specNorm_residual_comm {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    specNorm (residual P Q) = specNorm (residual Q P) := by
  have hc := specNorm_one_sub_transpose_mul_eq_one_sub_mul_transpose (Pᵀ*Q)
  have hg : (Qᵀ*P) = (Pᵀ*Q)ᵀ := by simp
  have hp := specNorm_sq_eq_specNorm_transpose_mul_self (residual P Q)
  have hq := specNorm_sq_eq_specNorm_transpose_mul_self (residual Q P)
  rw [transpose_residual_mul_residual_eq_one_sub_overlap hP hQ] at hp
  rw [transpose_residual_mul_residual_eq_one_sub_overlap hQ hP, hg,
    Matrix.transpose_transpose] at hq
  nlinarith [specNorm_nonneg (residual P Q), specNorm_nonneg (residual Q P)]

/-- **Projector form of `sin θ_max`.** Equal-rank frame projector distance is exactly the
one-sided residual spectral norm: `‖PPᵀ − QQᵀ‖₂ = ‖(I − PPᵀ)Q‖₂`. Stewart–Sun, Thm I.5.5;
Golub–Van Loan 2013, Thm 2.5.1; including empty frames.
atlas: principal-angles-def (partial) -/
theorem specNorm_sub_frame_projector_eq_residual {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    specNorm (P*Pᵀ - Q*Qᵀ) = specNorm (residual P Q) := by
  rw [specNorm_sub_projector_eq_max (by simp [Matrix.IsSymm])
    (mul_transpose_mul_mul_transpose hP) (by simp [Matrix.IsSymm])
    (mul_transpose_mul_mul_transpose hQ)]
  have hleft : (1-Q*Qᵀ)*(P*Pᵀ) = residual Q P * Pᵀ := by
    rw [residual_eq_one_sub_mul, Matrix.mul_assoc]
  have hright : (Q*Qᵀ)*(1-P*Pᵀ) = (residual P Q * Qᵀ)ᵀ := by
    rw [residual_eq_one_sub_mul]
    simp [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.mul_assoc]
  rw [hleft, hright, specNorm_transpose,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hP.transpose_mul_self,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hQ.transpose_mul_self,
    specNorm_residual_comm hQ hP, max_self]

omit [DecidableEq m] [DecidableEq n] in
/-- The Frobenius inner product of frame projectors is the squared
Frobenius norm of the overlap. Stewart–Sun §I.5. -/
theorem frobInner_frame_projectors_eq_frobSq_overlap (P Q : Matrix m n ℝ) :
    frobInner (P*Pᵀ) (Q*Qᵀ) = frobSq (Pᵀ*Q) := by
  rw [frobInner_eq_trace, frobSq, frobInner_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [← Matrix.mul_assoc (P*Pᵀ) Q Qᵀ, Matrix.trace_mul_cycle (P*Pᵀ) Q Qᵀ]
  simp only [Matrix.mul_assoc]

omit [DecidableEq m] in
/-- Equal-rank frame projector distance squared is twice the residual
Frobenius norm squared. Stewart–Sun §I.5, including zero-dimensional frames.
atlas: principal-angles-def (partial) -/
theorem frobSq_sub_frame_projector_eq_two_mul_residual {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    frobSq (P*Pᵀ-Q*Qᵀ) = 2 * frobSq (residual P Q) := by
  rw [frobSq_sub, frobSq_mul_left_of_orthonormal hP.transpose_mul_self,
    frobSq_mul_left_of_orthonormal hQ.transpose_mul_self, frobSq_transpose, frobSq_transpose,
    frobSq_residual_eq_sub hP, frobSq_frame_eq_card hP, frobSq_frame_eq_card hQ,
    frobInner_frame_projectors_eq_frobSq_overlap]
  ring

omit [DecidableEq n] in
/-- A symmetric idempotent is the frame projector of an orthonormal basis
of its range. Stewart–Sun §I.5; the frame has exactly the matrix rank columns. -/
theorem exists_frame_projector_of_isSymm_of_isIdempotentElem {P : Matrix n n ℝ}
    (hs : P.IsSymm) (hp : IsIdempotentElem P) :
    ∃ Q : Matrix n (Fin P.rank) ℝ, HasOrthonormalCols Q ∧ P = Q*Qᵀ := by
  let Q := orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  have hQ := hasOrthonormalCols_orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  have hrange := range_orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  have hQP : Q*(Qᵀ*P) = P := mul_transpose_mul_eq_of_range_le hQ hrange.ge
  have hPQ : P*Q = Q := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    have hx : Q*ᵥx ∈ LinearMap.range P.mulVecLin :=
      hrange.le (show Q*ᵥx ∈ LinearMap.range Q.mulVecLin from ⟨x, rfl⟩)
    obtain ⟨y, hy⟩ := hx
    rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      show P*P=P from hp]
  have hQtP : Qᵀ*P = Qᵀ := by
    have hh := congrArg Matrix.transpose hPQ
    simpa only [Matrix.transpose_mul, hs.eq] using hh
  have heq : P = Q*Qᵀ := hQP.symm.trans (congrArg (fun T => Q*T) hQtP)
  exact ⟨Q, hQ, heq⟩

/-- Equal-rank orthogonal projections have equal one-sided gap norms.
Stewart–Sun §I.5; the rank-zero case is handled by an empty frame.
atlas: principal-angles-def (partial) -/
theorem specNorm_complement_mul_projector_eq_of_rank_eq {P Q : Matrix n n ℝ}
    (hPs : P.IsSymm) (hPi : IsIdempotentElem P)
    (hQs : Q.IsSymm) (hQi : IsIdempotentElem Q) (hr : P.rank=Q.rank) :
    specNorm ((1-Q)*P) = specNorm ((1-P)*Q) := by
  obtain ⟨U, hU, hPU⟩ := exists_frame_projector_of_isSymm_of_isIdempotentElem hPs hPi
  obtain ⟨V, hV, hQV⟩ := exists_frame_projector_of_isSymm_of_isIdempotentElem hQs hQi
  let e : Fin Q.rank ≃ Fin P.rank := finCongr hr.symm
  let V' := V.reindex (Equiv.refl n) e
  have hV' : HasOrthonormalCols V' := hV.reindex (Equiv.refl n) e
  have hVV : V'*V'ᵀ = V*Vᵀ := by
    simp only [V', Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
      Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hQV' : Q=V'*V'ᵀ := hQV.trans hVV.symm
  have hleft : (1-Q)*P = residual V' U*Uᵀ := by
    calc
      _ = (1-Q)*(U*Uᵀ) := congrArg (fun T => (1-Q)*T) hPU
      _ = (1-V'*V'ᵀ)*(U*Uᵀ) := congrArg (fun T => (1-T)*(U*Uᵀ)) hQV'
      _ = _ := by rw [residual_eq_one_sub_mul, Matrix.mul_assoc]
  have hright : (1-P)*Q = residual U V'*V'ᵀ := by
    calc
      _ = (1-P)*(V'*V'ᵀ) := congrArg (fun T => (1-P)*T) hQV'
      _ = (1-U*Uᵀ)*(V'*V'ᵀ) := congrArg (fun T => (1-T)*(V'*V'ᵀ)) hPU
      _ = _ := by rw [residual_eq_one_sub_mul, Matrix.mul_assoc]
  rw [hleft, hright,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hU.transpose_mul_self,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hV'.transpose_mul_self, specNorm_residual_comm hV' hU]

/-- For equal-rank orthogonal projections, the projector distance is one
one-sided gap norm. Stewart–Sun §I.5, with no positive-rank restriction. -/
theorem specNorm_sub_projector_eq_complement_mul_of_rank_eq {P Q : Matrix n n ℝ}
    (hPs : P.IsSymm) (hPi : IsIdempotentElem P)
    (hQs : Q.IsSymm) (hQi : IsIdempotentElem Q) (hr : P.rank=Q.rank) :
    specNorm (P-Q) = specNorm ((1-Q)*P) := by
  rw [specNorm_sub_projector_eq_max hPs hPi hQs hQi]
  have ht : specNorm (Q*(1-P)) = specNorm ((1-P)*Q) := by
    rw [← specNorm_transpose (Q*(1-P))]
    simp [hPs.eq, hQs.eq]
  rw [ht, ← specNorm_complement_mul_projector_eq_of_rank_eq hPs hPi hQs hQi hr,
    max_self]

end NLAlib
