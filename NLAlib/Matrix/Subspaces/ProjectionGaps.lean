import NLAlib.Matrix.Norms.EuclideanOperatorBounds
import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.Matrix.Spectral.SpectralBounds
import NLAlib.Matrix.Norms.RankNorm
import NLAlib.Matrix.Norms.Reindex
import NLAlib.Matrix.Subspaces.OrthogonalProducts
import NLAlib.Matrix.Subspaces.OrthonormalBasisMatrix
/-!
# Distances between orthogonal projections

The orthogonal-support decomposition gives the spectral norm of a difference of two orthogonal
projectors (Hermitian idempotents over `[RCLike 𝕜]`) as the maximum of its two one-sided gaps
(`specNorm_sub_projector_eq_max`); equal-rank projectors have equal one-sided gaps
(`specNorm_complement_mul_projector_eq_of_rank_eq`); frames with orthonormal columns identify
the gaps through their overlap Gram matrices (`specNorm_sub_frame_projector_eq_residual`,
`specNorm_residual_comm`). Stewart–Sun 1990, §I.5 (Thm I.5.5); Golub–Van Loan 2013, Thm 2.5.1.
Atlas: `principal-angles-def`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Euclidean vector-norm helpers -/

omit [DecidableEq m] in
/-- `‖A x‖₂ ≤ ‖A‖₂ ‖x‖₂` in the `WithLp` spelling. -/
theorem norm_toLp_mulVec_le (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace 𝕜 m)‖ ≤
      specNorm A * ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ := by
  open scoped Matrix.Norms.L2Operator in
  rw [specNorm_eq_norm]
  exact A.l2_opNorm_mulVec (WithLp.toLp 2 x)

omit [DecidableEq m] in
/-- `‖A‖₂ ≤ c` as soon as `‖A x‖₂ ≤ c ‖x‖₂` for every `x` (operator-norm bound). -/
theorem specNorm_le_of_forall_norm_toLp_mulVec_le (A : Matrix m n 𝕜) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : n → 𝕜, ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace 𝕜 m)‖ ≤
      c * ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖) : specNorm A ≤ c := by
  open scoped Matrix.Norms.L2Operator in
  rw [specNorm_eq_norm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply]
  simpa using h x.ofLp

omit [DecidableEq n] in
/-- Pythagoras for orthogonal vectors: `‖u + v‖₂² = ‖u‖₂² + ‖v‖₂²` when `⟪u, v⟫ = 0`. -/
theorem norm_toLp_add_sq_of_star_dotProduct_eq_zero (u v : n → 𝕜) (h : star u ⬝ᵥ v = 0) :
    ‖(WithLp.toLp 2 (u + v) : EuclideanSpace 𝕜 n)‖ ^ 2 =
      ‖(WithLp.toLp 2 u : EuclideanSpace 𝕜 n)‖ ^ 2 +
        ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ ^ 2 := by
  rw [WithLp.toLp_add, @norm_add_sq 𝕜, EuclideanSpace.inner_toLp_toLp, dotProduct_comm, h, map_zero]
  ring

/-- Squared Euclidean lengths split across an orthogonal projector (Hermitian idempotent) and
its complement: `‖Px‖₂² + ‖(I − P)x‖₂² = ‖x‖₂²`. Stewart–Sun 1990, §I.5. -/
theorem norm_toLp_sq_add_norm_toLp_sq_of_isHermitian_of_isIdempotentElem {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (x : n → 𝕜) :
    ‖(WithLp.toLp 2 (P *ᵥ x) : EuclideanSpace 𝕜 n)‖ ^ 2 +
      ‖(WithLp.toLp 2 ((1 - P) *ᵥ x) : EuclideanSpace 𝕜 n)‖ ^ 2 =
      ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖ ^ 2 := by
  have horth : star (P *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x) = 0 := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hs.eq,
      Matrix.mul_sub, Matrix.mul_one, show P * P = P from hp, sub_self, Matrix.zero_mulVec,
      dotProduct_zero]
  have h := norm_toLp_add_sq_of_star_dotProduct_eq_zero _ _ horth
  rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec] at h
  exact h.symm

/-! ### Projector gaps -/

/-- Two blocks with orthogonal input and output supports have norm at most
the maximum block norm. Stewart–Sun 1990, §I.5; the proof uses Pythagoras twice. -/
theorem specNorm_add_le_max_of_projector_supports {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) {X Y : Matrix m n 𝕜}
    (hX : X * P = X) (hY : Y * (1 - P) = Y) (hXY : Xᴴ * Y = 0) :
    specNorm (X + Y) ≤ max (specNorm X) (specNorm Y) := by
  apply specNorm_le_of_forall_norm_toLp_mulVec_le _
    (le_trans (specNorm_nonneg X) (le_max_left _ _))
  intro x
  have horth : star (X *ᵥ x) ⬝ᵥ (Y *ᵥ x) = 0 := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hXY,
      Matrix.zero_mulVec, dotProduct_zero]
  have hsum := norm_toLp_add_sq_of_star_dotProduct_eq_zero _ _ horth
  rw [← Matrix.add_mulVec] at hsum
  have hx := norm_toLp_mulVec_le X (P *ᵥ x)
  have hy := norm_toLp_mulVec_le Y ((1 - P) *ᵥ x)
  rw [Matrix.mulVec_mulVec, hX] at hx
  rw [Matrix.mulVec_mulVec, hY] at hy
  have hsplit := norm_toLp_sq_add_norm_toLp_sq_of_isHermitian_of_isIdempotentElem hs hp x
  set c := max (specNorm X) (specNorm Y) with hc
  have hXc : specNorm X ≤ c := le_max_left _ _
  have hYc : specNorm Y ≤ c := le_max_right _ _
  have hc0 : 0 ≤ c := (specNorm_nonneg X).trans hXc
  have hx2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hy2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hX2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (specNorm_nonneg X) hXc 2)
    (sq_nonneg ‖(WithLp.toLp 2 (P *ᵥ x) : EuclideanSpace 𝕜 n)‖)
  have hY2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (specNorm_nonneg Y) hYc 2)
    (sq_nonneg ‖(WithLp.toLp 2 ((1 - P) *ᵥ x) : EuclideanSpace 𝕜 n)‖)
  have h1 : ‖(WithLp.toLp 2 ((X + Y) *ᵥ x) : EuclideanSpace 𝕜 m)‖ ^ 2 ≤
      (c * ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 n)‖) ^ 2 := by
    rw [hsum, mul_pow, ← hsplit, mul_add]
    rw [mul_pow] at hx2 hy2
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

omit [DecidableEq m] in
/-- Complementary orthogonal-projector gap decomposition `P − Q = (I − Q)P − Q(I − P)`.
Stewart–Sun 1990, §I.5. -/
theorem sub_projector_eq_complement_mul_sub {P Q : Matrix n n 𝕜} :
    P - Q = (1 - Q) * P - Q * (1 - P) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  abel

/-- The norm of a difference of orthogonal projections is the maximum of
the two one-sided gaps. Stewart–Sun 1990, §I.5; ranks may differ and may be zero. -/
theorem specNorm_sub_projector_eq_max {P Q : Matrix n n 𝕜}
    (hPs : P.IsHermitian) (hPi : IsIdempotentElem P)
    (hQs : Q.IsHermitian) (hQi : IsIdempotentElem Q) :
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
      (X := (1 - Q) * P) (Y := -(Q * (1 - P)))
      (by simp [Matrix.mul_assoc, hPP]) (by simp [Matrix.mul_assoc, hPc])
      (by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
          hPs.eq, hQs.eq, Matrix.mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Q) Q, hQz,
          Matrix.zero_mul, Matrix.mul_zero, neg_zero])
    simpa only [specNorm_neg] using hh
  · apply max_le
    · have heq : (1 - Q) * P = (P - Q) * P := by simp [Matrix.sub_mul, hPP]
      rw [heq]
      exact (specNorm_mul_le _ _).trans (by
        have hh := Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem hPs hPi
        nlinarith [specNorm_nonneg (P - Q)])
    · have heq : Q * (1 - P) = -(P - Q) * (1 - P) := by
        simp only [Matrix.neg_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, hPP]
        abel
      rw [heq]
      have hPcs : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hPs
      exact (specNorm_mul_le _ _).trans (by
        have hh : specNorm (1 - P) ≤ 1 :=
          Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem hPcs hPc
        rw [specNorm_neg]
        nlinarith [specNorm_nonneg (P - Q)])

/-- The two square overlap Gram defects `I − CᴴC` and `I − CCᴴ` have the same spectral norm,
since an SVD diagonalizes both with the same singular-value squares. Stewart–Sun 1990, §I.5. -/
theorem specNorm_one_sub_conjTranspose_mul_eq_one_sub_mul_conjTranspose (C : Matrix n n 𝕜) :
    specNorm (1 - Cᴴ * C) = specNorm (1 - C * Cᴴ) := by
  obtain ⟨U, V, h⟩ := exists_isSVD C
  set D := Matrix.diagonal (fun j : Fin (Fintype.card n) =>
    ((singularValues C j ^ 2 : ℝ) : 𝕜)) with hD
  have hleft : 1 - Cᴴ * C = V * (1 - D) * Vᴴ := by
    rw [h.conjTranspose_mul_self, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      h.mul_conjTranspose_right]
  have hright : 1 - C * Cᴴ = U * (1 - D) * Uᴴ := by
    rw [h.mul_conjTranspose_self, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      h.mul_conjTranspose_left]
  rw [hleft, hright,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols h.conjTranspose_mul_right,
    specNorm_mul_left_of_hasOrthonormalCols h.conjTranspose_mul_right,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols h.conjTranspose_mul_left,
    specNorm_mul_left_of_hasOrthonormalCols h.conjTranspose_mul_left]

/-- The projection-residual Gram equals the identity minus the overlap Gram for frames with
orthonormal columns: `(projResidual P Q)ᴴ (projResidual P Q) = I − (PᴴQ)ᴴ(PᴴQ)`. The frame
widths may differ, and empty frames are allowed. Stewart–Sun 1990, §I.5 (Thm I.5.5). -/
theorem conjTranspose_residual_mul_residual_eq_one_sub_overlap {p : Type*} [Fintype p]
    [DecidableEq p] {P : Matrix m n 𝕜} {Q : Matrix m p 𝕜} (hP : HasOrthonormalCols P)
    (hQ : HasOrthonormalCols Q) :
    (projResidual P Q)ᴴ * projResidual P Q = 1 - (Pᴴ * Q)ᴴ * (Pᴴ * Q) := by
  have hH : (1 - P * Pᴴ)ᴴ = 1 - P * Pᴴ := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  rw [residual_eq_one_sub_mul, Matrix.conjTranspose_mul, hH, Matrix.mul_assoc,
    ← Matrix.mul_assoc (1 - P * Pᴴ), one_sub_mul_conjTranspose_idem hP, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, hQ.conjTranspose_mul_self]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- **Symmetry of `θ_max` for equal dimensions.** The two residuals between equal-width
frames with orthonormal columns have equal spectral norm: `‖(I − PPᴴ)Q‖₂ = ‖(I − QQᴴ)P‖₂`.
False for unequal widths (a line inside a plane has `θ = 0` one way and `π/2` the other).
Stewart–Sun 1990, Thm I.5.5; Golub–Van Loan 2013, Thm 2.5.1.
atlas: principal-angles-def (partial) -/
theorem specNorm_residual_comm {P Q : Matrix m n 𝕜}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    specNorm (projResidual P Q) = specNorm (projResidual Q P) := by
  have hc := specNorm_one_sub_conjTranspose_mul_eq_one_sub_mul_conjTranspose (Pᴴ * Q)
  have hg : Qᴴ * P = (Pᴴ * Q)ᴴ := by simp
  have hp := specNorm_sq_eq_specNorm_conjTranspose_mul_self (projResidual P Q)
  have hq := specNorm_sq_eq_specNorm_conjTranspose_mul_self (projResidual Q P)
  rw [conjTranspose_residual_mul_residual_eq_one_sub_overlap hP hQ] at hp
  rw [conjTranspose_residual_mul_residual_eq_one_sub_overlap hQ hP, hg,
    Matrix.conjTranspose_conjTranspose] at hq
  nlinarith [specNorm_nonneg (projResidual P Q), specNorm_nonneg (projResidual Q P)]

/-- **Projector form of `sin θ_max`.** The distance between equal-rank frame projectors is the
one-sided residual spectral norm: `‖PPᴴ − QQᴴ‖₂ = ‖(I − PPᴴ)Q‖₂`. Stewart–Sun 1990, Thm I.5.5;
Golub–Van Loan 2013, Thm 2.5.1; including empty frames.
atlas: principal-angles-def (partial) -/
theorem specNorm_sub_frame_projector_eq_residual {P Q : Matrix m n 𝕜}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    specNorm (P * Pᴴ - Q * Qᴴ) = specNorm (projResidual P Q) := by
  rw [specNorm_sub_projector_eq_max (Matrix.isHermitian_mul_conjTranspose_self P)
    (show P * Pᴴ * (P * Pᴴ) = P * Pᴴ from mul_conjTranspose_mul_mul_conjTranspose hP)
    (Matrix.isHermitian_mul_conjTranspose_self Q)
    (show Q * Qᴴ * (Q * Qᴴ) = Q * Qᴴ from mul_conjTranspose_mul_mul_conjTranspose hQ)]
  have hleft : (1 - Q * Qᴴ) * (P * Pᴴ) = projResidual Q P * Pᴴ := by
    rw [residual_eq_one_sub_mul, Matrix.mul_assoc]
  have hright : (Q * Qᴴ) * (1 - P * Pᴴ) = (projResidual P Q * Qᴴ)ᴴ := by
    rw [residual_eq_one_sub_mul]
    simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.mul_assoc]
  rw [hleft, hright, specNorm_conjTranspose,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hP,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hQ,
    specNorm_residual_comm hQ hP, max_self]

omit [DecidableEq m] [DecidableEq n] in
/-- The Frobenius inner product of frame projectors is the squared Frobenius norm of the
overlap: `⟪PPᴴ, QQᴴ⟫_F = ‖PᴴQ‖_F²`. Stewart–Sun 1990, §I.5. -/
theorem frobInner_frame_projectors_eq_frobSq_overlap (P Q : Matrix m n 𝕜) :
    frobInner (P * Pᴴ) (Q * Qᴴ) = frobSq (Pᴴ * Q) := by
  rw [frobInner_eq_trace, frobSq, frobInner_eq_trace]
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [Matrix.mul_assoc]

omit [DecidableEq m] in
/-- Equal-rank frame projector distance squared is twice the residual Frobenius norm squared:
`‖PPᴴ − QQᴴ‖_F² = 2 ‖(I − PPᴴ)Q‖_F²`. Stewart–Sun 1990, §I.5, including zero-dimensional frames.
atlas: principal-angles-def (partial) -/
theorem frobSq_sub_frame_projector_eq_two_mul_residual {P Q : Matrix m n 𝕜}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    frobSq (P * Pᴴ - Q * Qᴴ) = 2 * frobSq (projResidual P Q) := by
  rw [frobSq_sub, frobSq_mul_left_of_orthonormal hP, frobSq_mul_left_of_orthonormal hQ,
    frobSq_conjTranspose, frobSq_conjTranspose, frobSq_residual_eq_sub hP,
    frobSq_frame_eq_card hP, frobSq_frame_eq_card hQ,
    frobInner_frame_projectors_eq_frobSq_overlap]
  ring

omit [DecidableEq n] in
/-- An orthogonal projector (Hermitian idempotent) is the frame projector `QQᴴ` of an orthonormal
basis `Q` of its range; the frame has exactly `rank P` columns. Stewart–Sun 1990, §I.5. -/
theorem exists_frame_projector_of_isHermitian_of_isIdempotentElem {P : Matrix n n 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) :
    ∃ Q : Matrix n (Fin P.rank) 𝕜, HasOrthonormalCols Q ∧ P = Q * Qᴴ := by
  let Q := orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  have hQ := hasOrthonormalCols_orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  have hrange := range_orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  have hQP : Q * (Qᴴ * P) = P := mul_conjTranspose_mul_eq_of_range_le hQ hrange.ge
  have hPQ : P * Q = Q := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    have hx : Q *ᵥ x ∈ LinearMap.range P.mulVecLin :=
      hrange.le (show Q *ᵥ x ∈ LinearMap.range Q.mulVecLin from ⟨x, rfl⟩)
    obtain ⟨y, hy⟩ := hx
    rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      show P * P = P from hp]
  have hQtP : Qᴴ * P = Qᴴ := by
    have hh := congrArg Matrix.conjTranspose hPQ
    simpa only [Matrix.conjTranspose_mul, hs.eq] using hh
  exact ⟨Q, hQ, hQP.symm.trans (congrArg (fun T => Q * T) hQtP)⟩

/-- Equal-rank orthogonal projections have equal one-sided gap norms:
`‖(I − Q)P‖₂ = ‖(I − P)Q‖₂`. Stewart–Sun 1990, §I.5; rank zero is the empty frame.
atlas: principal-angles-def (partial) -/
theorem specNorm_complement_mul_projector_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hPs : P.IsHermitian) (hPi : IsIdempotentElem P)
    (hQs : Q.IsHermitian) (hQi : IsIdempotentElem Q) (hr : P.rank = Q.rank) :
    specNorm ((1 - Q) * P) = specNorm ((1 - P) * Q) := by
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
    rw [residual_eq_one_sub_mul, Matrix.mul_assoc, ← hPU, ← hQV']
  have hright : (1 - P) * Q = projResidual U V' * V'ᴴ := by
    rw [residual_eq_one_sub_mul, ← hPU, Matrix.mul_assoc, ← hQV']
  rw [hleft, hright, specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hU,
    specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hV', specNorm_residual_comm hV' hU]

/-- For equal-rank orthogonal projections, the projector distance is one
one-sided gap norm: `‖P − Q‖₂ = ‖(I − Q)P‖₂`. Stewart–Sun 1990, §I.5, with no positive-rank
restriction. -/
theorem specNorm_sub_projector_eq_complement_mul_of_rank_eq {P Q : Matrix n n 𝕜}
    (hPs : P.IsHermitian) (hPi : IsIdempotentElem P)
    (hQs : Q.IsHermitian) (hQi : IsIdempotentElem Q) (hr : P.rank = Q.rank) :
    specNorm (P - Q) = specNorm ((1 - Q) * P) := by
  rw [specNorm_sub_projector_eq_max hPs hPi hQs hQi]
  have ht : specNorm (Q * (1 - P)) = specNorm ((1 - P) * Q) := by
    rw [← specNorm_conjTranspose (Q * (1 - P))]
    simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hPs.eq, hQs.eq]
  rw [ht, ← specNorm_complement_mul_projector_eq_of_rank_eq hPs hPi hQs hQi hr, max_self]

end NLAlib
