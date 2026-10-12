import NLAlib.Matrix.Subspaces.ProjectionGaps

/-!
# Principal angles of equal-dimensional subspaces

Angles are arccosines of the descending overlap singular values. Their sine
matrix is linked to the residual and the projector-distance APIs, with empty
frames allowed. Stewart–Sun §I.5; atlas `principal-angles-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Principal angles are arccosines of the overlap singular values in
descending order; row and column labels are temporarily normalized to `Fin`.
Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
def principalAnglesFintype (P Q : Matrix m n ℝ) : Fin (Fintype.card n) → ℝ :=
  fun i => Real.arccos (singularValues
    ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i)

/-- The diagonal sine matrix of the principal angles. Stewart–Sun §I.5;
the matrix is empty when the frames have no columns.
atlas: principal-angles-def (partial) -/
def sinePrincipalAngles (P Q : Matrix m n ℝ) :
    Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ :=
  Matrix.diagonal (fun i => Real.sin (principalAnglesFintype P Q i))

/-- Overlap singular values lie between zero and one for orthonormal
frames. Stewart–Sun §I.5, since both frame maps are contractions. -/
theorem overlap_singularValues_mem_Icc {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (i : ℕ) :
    singularValues ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact singularValues_nonneg _ _
  · have hh := singularValues_le_specNorm
      ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i
    rw [specNorm_reindex] at hh
    have hp := specNorm_le_one_of_orthonormal hP
    have hq := specNorm_le_one_of_orthonormal hQ
    have hm := specNorm_mul_le Pᵀ Q
    rw [specNorm_transpose] at hm
    have hb : specNorm P * specNorm Q ≤ 1 := by
      calc
        _ ≤ 1*specNorm Q := mul_le_mul_of_nonneg_right hp (specNorm_nonneg _)
        _ ≤ 1 := by simpa using hq
    exact hh.trans (hm.trans hb)

/-- Every principal angle lies between zero and `π/2`. Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem principalAngles_mem_Icc {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (i : Fin (Fintype.card n)) :
    principalAnglesFintype P Q i ∈ Set.Icc (0 : ℝ) (Real.pi/2) :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (overlap_singularValues_mem_Icc hP hQ i).1⟩

omit [DecidableEq m] [DecidableEq n] in
/-- Principal angles increase because overlap singular values decrease.
Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem principalAngles_monotone (P Q : Matrix m n ℝ) : Monotone (principalAnglesFintype P Q) := by
  intro i j hij
  exact Real.antitone_arccos (singularValues_antitone _ hij)

/-- The cosine of a principal angle is its overlap singular value.
Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem cos_principalAngles {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (i : Fin (Fintype.card n)) :
    Real.cos (principalAnglesFintype P Q i) =
      singularValues ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i := by
  have hh := overlap_singularValues_mem_Icc hP hQ i
  exact Real.cos_arccos (by linarith [hh.1]) hh.2

omit [DecidableEq m] [DecidableEq n] in
/-- The sine is the nonnegative square root of one minus the cosine square.
Stewart–Sun §I.5. -/
theorem sin_principalAngles (P Q : Matrix m n ℝ) (i : Fin (Fintype.card n)) :
    Real.sin (principalAnglesFintype P Q i) =
      Real.sqrt (1-singularValues
        ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i ^ 2) :=
  Real.sin_arccos _

/-- The principal-angle sine Gram is the diagonal overlap Gram defect.
Stewart–Sun §I.5. -/
theorem transpose_sinePrincipalAngles_mul_self {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    (sinePrincipalAngles P Q)ᵀ*sinePrincipalAngles P Q =
      Matrix.diagonal (fun i : Fin (Fintype.card n) => 1-singularValues
        ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i ^ 2) := by
  rw [sinePrincipalAngles, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  rw [← sq, sin_principalAngles, Real.sq_sqrt]
  have hh := overlap_singularValues_mem_Icc hP hQ i
  nlinarith [hh.1, hh.2]

/-- The residual operator norm equals the norm of the genuine sine-angle
matrix. Stewart–Sun §I.5, including empty frames.
atlas: principal-angles-def (partial) -/
theorem specNorm_sinePrincipalAngles_eq_residual {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    specNorm (sinePrincipalAngles P Q) = specNorm (residual P Q) := by
  let C := (Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)
  have hs := specNorm_sq_eq_specNorm_transpose_mul_self (sinePrincipalAngles P Q)
  rw [transpose_sinePrincipalAngles_mul_self hP hQ] at hs
  simp only [specNorm_eq_norm, Matrix.l2_opNorm_diagonal] at hs
  have hr := specNorm_sq_eq_specNorm_transpose_mul_self (residual P Q)
  rw [transpose_residual_mul_residual_eq_one_sub_overlap hP hQ] at hr
  have hc := specNorm_gram_sub_one_eq_norm_singularValues_sq_sub_one C
  have heq : Cᵀ*C-1 = ((Pᵀ*Q)ᵀ*(Pᵀ*Q)-1).reindex
      (Fintype.equivFin n) (Fintype.equivFin n) := by
    simp only [C, Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
    change _ = ((Pᵀ*Q)ᵀ*(Pᵀ*Q)).submatrix _ _ - (1 : Matrix n n ℝ).submatrix _ _
    rw [Matrix.submatrix_one_equiv]
  rw [heq, specNorm_reindex, specNorm_sub_comm] at hc
  have hn : ‖(fun j : Fin (Fintype.card n) => singularValues C j^2-1)‖ =
      ‖(fun j : Fin (Fintype.card n) => 1-singularValues C j^2)‖ := by
    rw [show (fun j : Fin (Fintype.card n) => singularValues C j^2-1) =
      -(fun j : Fin (Fintype.card n) => 1-singularValues C j^2) by ext j; simp]
    exact norm_neg _
  rw [hn] at hc
  change specNorm (sinePrincipalAngles P Q)^2 =
    ‖(fun j : Fin (Fintype.card n) => 1-singularValues C j^2)‖ at hs
  nlinarith [specNorm_nonneg (sinePrincipalAngles P Q), specNorm_nonneg (residual P Q)]

/-- The sine-angle Frobenius square is width minus overlap Frobenius square.
Stewart–Sun §I.5, including the empty frame.
atlas: principal-angles-def (partial) -/
theorem frobSq_sinePrincipalAngles_eq_card_sub_overlap {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    frobSq (sinePrincipalAngles P Q) = (Fintype.card n : ℝ)-frobSq (Pᵀ*Q) := by
  rw [frobSq, frobInner_eq_trace, transpose_sinePrincipalAngles_mul_self hP hQ,
    Matrix.trace_diagonal, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  rw [← frobSq_reindex (Pᵀ*Q) (Fintype.equivFin n) (Fintype.equivFin n),
    frobSq_eq_sum_sq_singularValues, min_self]
  exact Fin.sum_univ_eq_sum_range (fun j => singularValues
    ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) j^2) (Fintype.card n)

/-- The actual sine-angle Frobenius norm equals the residual Frobenius norm.
Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem frobNorm_sinePrincipalAngles_eq_residual {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    frobNorm (sinePrincipalAngles P Q) = frobNorm (residual P Q) := by
  rw [frobNorm, frobNorm, frobSq_sinePrincipalAngles_eq_card_sub_overlap hP hQ,
    frobSq_residual_eq_sub hP, frobSq_frame_eq_card hQ]

/-- The sine-angle operator norm is exactly the equal-rank projector distance.
Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem specNorm_sinePrincipalAngles_eq_projector_distance {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    specNorm (sinePrincipalAngles P Q) = specNorm (P*Pᵀ-Q*Qᵀ) := by
  rw [specNorm_sinePrincipalAngles_eq_residual hP hQ,
    specNorm_sub_frame_projector_eq_residual hP hQ]

/-- The projector-distance Frobenius square is twice the sine-angle square.
Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem frobSq_projector_distance_eq_two_mul_sinePrincipalAngles {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    frobSq (P*Pᵀ-Q*Qᵀ) = 2*frobSq (sinePrincipalAngles P Q) := by
  rw [frobSq_sub_frame_projector_eq_two_mul_residual hP hQ,
    frobSq_residual_eq_sub hP, frobSq_sinePrincipalAngles_eq_card_sub_overlap hP hQ,
    frobSq_frame_eq_card hQ]

omit [DecidableEq m] [DecidableEq n] in
/-- Principal angles are symmetric under exchanging frames. Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem principalAngles_comm (P Q : Matrix m n ℝ) : principalAnglesFintype P Q = principalAnglesFintype Q P := by
  have heq : ((Qᵀ*P).reindex (Fintype.equivFin n) (Fintype.equivFin n)) =
      ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n))ᵀ := by
    simp only [Matrix.reindex_apply, Matrix.transpose_submatrix,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  funext i
  simp only [principalAnglesFintype, heq, singularValues_transpose]

omit [DecidableEq n] in
/-- Completeness expresses a residual through orthonormal complementary
coordinates. Stewart–Sun §I.5; the complement may be empty. -/
theorem residual_eq_complement_mul_overlap {r : Type*} [Fintype r]
    {P Q : Matrix m n ℝ} {R : Matrix m r ℝ}
    (hcomp : P*Pᵀ+R*Rᵀ=1) : residual P Q = R*(Rᵀ*Q) := by
  have heq : (1 : Matrix m m ℝ)-P*Pᵀ=R*Rᵀ := by
    rw [← hcomp]
    abel
  rw [residual_eq_one_sub_mul, heq, Matrix.mul_assoc]

/-- The sine-angle norm equals the complementary overlap norm.
Stewart–Sun §I.5; no ambient dimension subtraction or nonempty assumption.
atlas: principal-angles-def (partial) -/
theorem specNorm_sinePrincipalAngles_eq_complement_overlap {r : Type*} [Fintype r]
    [DecidableEq r] {P Q : Matrix m n ℝ} {R : Matrix m r ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (hR : HasOrthonormalCols R)
    (hcomp : P*Pᵀ+R*Rᵀ=1) : specNorm (sinePrincipalAngles P Q)=specNorm (Rᵀ*Q) := by
  rw [specNorm_sinePrincipalAngles_eq_residual hP hQ,
    residual_eq_complement_mul_overlap hcomp, specNorm_mul_left_of_hasOrthonormalCols hR]

/-- The Frobenius sine-angle norm equals the complementary overlap norm.
Stewart–Sun §I.5.
atlas: principal-angles-def (partial) -/
theorem frobNorm_sinePrincipalAngles_eq_complement_overlap {r : Type*} [Fintype r]
    [DecidableEq r] {P Q : Matrix m n ℝ} {R : Matrix m r ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (hR : HasOrthonormalCols R)
    (hcomp : P*Pᵀ+R*Rᵀ=1) : frobNorm (sinePrincipalAngles P Q)=frobNorm (Rᵀ*Q) := by
  rw [frobNorm_sinePrincipalAngles_eq_residual hP hQ,
    residual_eq_complement_mul_overlap hcomp, frobNorm, frobNorm,
    frobSq_mul_left_of_orthonormal hR]

/-- The sine-angle norm is at most one, for all widths including zero.
Stewart–Sun §I.5. -/
theorem specNorm_sinePrincipalAngles_le_one {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    specNorm (sinePrincipalAngles P Q) ≤ 1 := by
  rw [specNorm_sinePrincipalAngles_eq_residual hP hQ]
  exact (specNorm_sub_mul_transpose_mul_le hP Q).trans (specNorm_le_one_of_orthonormal hQ)

end NLAlib
