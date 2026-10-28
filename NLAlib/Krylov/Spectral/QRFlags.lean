import NLAlib.Krylov.Spectral.QRAlgorithm
import NLAlib.Krylov.Spectral.SubspaceIteration
import NLAlib.Matrix.Subspaces.OrderedFrames

/-!
# Leading QR flags without a nonsingular full matrix

Only the relevant leading overlap needs to be invertible. This retains QR
convergence when the final eigenvalue is zero and the last column is completed
orthogonally. Source: the simultaneous-iteration proof of Trefethen--Bau, Thm 28.4.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {n j : ℕ}

/-- A square QR factorization restricts to a thin factorization of every prefix,
without assuming full rank. -/
theorem IsQR.headColumns_isQR {M Q R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR M Q R)
    (hj : j ≤ n) :
    IsQR (headColumns M hj) (headColumns Q hj) (R.submatrix (Fin.castLE hj) (Fin.castLE hj)) := by
  have hf : IsFullQR (headColumns M hj) Q (R.submatrix id (Fin.castLE hj)) := by
    refine ⟨?_, h.orth, ?_⟩
    · rw [h.eq]; ext i l; rfl
    · intro i l hil
      exact h.upper hil
  exact hf.isQR_castLE hj

/-- Invertibility of any square overlap of a matrix's leading columns identifies
the corresponding QR flag. No invertibility of the full matrix is required. -/
theorem IsQR.range_headColumns_eq_of_isUnit_overlap
    {M Q R : Matrix (Fin n) (Fin n) ℝ} (h : IsQR M Q R) (hj : j ≤ n)
    (U : Matrix (Fin n) (Fin j) ℝ) (hU : IsUnit (Uᵀ * headColumns M hj)) :
    LinearMap.range (headColumns M hj).mulVecLin = LinearMap.range (headColumns Q hj).mulVecLin := by
  have ht := h.headColumns_isQR hj
  have hi : IsUnit (R.submatrix (Fin.castLE hj) (Fin.castLE hj)) := by
    rw [ht.eq, ← Matrix.mul_assoc, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hU
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hU)
  exact ht.range_mulVecLin_eq (ht.isUnit_det_iff.mp ((Matrix.isUnit_iff_isUnit_det _).mp hi))

/-- A transverse leading eigenvector overlap stays transverse along the native
unshifted QR run, even when the full matrix is singular. -/
theorem qrAlgorithm_head_overlap_isUnit
    {qr : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ}
    {A Q : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hQ : HasOrthonormalCols Q) (hAQ : A * Q = Q * Matrix.diagonal d)
    (hj : j ≤ n) (hd : ∀ i : Fin j, d (Fin.castLE hj i) ≠ 0)
    (hΩ : IsUnit ((headColumns Q hj)ᵀ * headColumns (1 : Matrix (Fin n) (Fin n) ℝ) hj))
    {k : ℕ} (hqr : QRAlgorithmSucceeds qr (fun _ => 0) A k) :
    IsUnit ((headColumns Q hj)ᵀ * headColumns (qrAlgorithmQ qr (fun _ => 0) A k) hj) ∧
    LinearMap.range (headColumns (qrAlgorithmQ qr (fun _ => 0) A k) hj).mulVecLin =
      LinearMap.range (headColumns (A ^ k) hj).mulVecLin := by
  have hUV : headColumns Q hj * (headColumns Q hj)ᵀ +
      tailColumns Q hj * (tailColumns Q hj)ᵀ = 1 := by
    rw [headColumns_projector_add_tailColumns_projector]
    exact mul_eq_one_comm.mp hQ
  have hAU : A * headColumns Q hj = headColumns Q hj *
      Matrix.diagonal (fun i => d (Fin.castLE hj i)) := by
    rw [mul_headColumns, hAQ, headColumns_mul_diagonal]
  have hAV : A * tailColumns Q hj = tailColumns Q hj *
      Matrix.diagonal (fun i => d ⟨j+i.val, by omega⟩) := by
    rw [mul_tailColumns, hAQ, tailColumns_mul_diagonal]
  have hi := isUnit_transpose_mul_pow_mul (hasOrthonormalCols_headColumns hQ hj)
    (hasOrthonormalCols_tailColumns hQ hj) hUV hAU hAV hd hΩ k
  rw [mul_headColumns, Matrix.mul_one] at hi
  have ht := (isQR_pow_qrAlgorithm hqr).headColumns_isQR hj
  have hi' := hi
  rw [ht.eq, ← Matrix.mul_assoc, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hi'
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hi'),
    ((isQR_pow_qrAlgorithm hqr).range_headColumns_eq_of_isUnit_overlap hj _ hi).symm⟩

/-- Every proper leading flag of unshifted QR converges at its spectral-gap
ratio. The zero smallest eigenvalue is permitted.
atlas: qr-algorithm-convergence (partial) -/
theorem overlapTangentNorm_qrAlgorithm_head_le
    {qr : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ}
    {A Q : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hQ : HasOrthonormalCols Q) (hAQ : A * Q = Q * Matrix.diagonal d)
    (hj : j ≤ n) {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hd : ∀ i : Fin j, α ≤ |d (Fin.castLE hj i)|)
    (he : ∀ i : Fin (n-j), |d ⟨j+i.val, by omega⟩| ≤ β)
    (hΩ : IsUnit ((headColumns Q hj)ᵀ * headColumns (1 : Matrix (Fin n) (Fin n) ℝ) hj))
    {k : ℕ} (hqr : QRAlgorithmSucceeds qr (fun _ => 0) A k) :
    overlapTangentNorm (headColumns Q hj) (headColumns (qrAlgorithmQ qr (fun _ => 0) A k) hj) ≤
      (β / α) ^ k * overlapTangentNorm (headColumns Q hj)
        (headColumns (1 : Matrix (Fin n) (Fin n) ℝ) hj) := by
  have hd0 (i : Fin j) : d (Fin.castLE hj i) ≠ 0 := by
    intro hz
    have hi := hd i
    rw [hz, abs_zero] at hi
    linarith
  have hUV : headColumns Q hj * (headColumns Q hj)ᵀ +
      tailColumns Q hj * (tailColumns Q hj)ᵀ = 1 := by
    rw [headColumns_projector_add_tailColumns_projector]
    exact mul_eq_one_comm.mp hQ
  apply overlapTangentNorm_le_of_range_eq_subspaceIterate
    (hasOrthonormalCols_headColumns hQ hj) (hasOrthonormalCols_tailColumns hQ hj) hUV
    (by rw [mul_headColumns, hAQ, headColumns_mul_diagonal])
    (by rw [mul_tailColumns, hAQ, tailColumns_mul_diagonal]) hα hβ hd he hΩ rfl
  simpa only [subspaceIterate, mul_headColumns, Matrix.mul_one] using
    (qrAlgorithm_head_overlap_isUnit hQ hAQ hj hd0 hΩ hqr).2

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-- The projector gap is bounded by the transverse overlap tangent. -/
theorem specNorm_sub_frame_projector_le_overlapTangentNorm {U W : Matrix m k ℝ}
    (hU : HasOrthonormalCols U) (hW : HasOrthonormalCols W) (hUW : IsUnit (Uᵀ * W)) :
    specNorm (U * Uᵀ - W * Wᵀ) ≤ overlapTangentNorm U W := by
  rw [show Uᵀ = Uᴴ from rfl, show Wᵀ = Wᴴ from rfl,
    specNorm_sub_frame_projector_eq_residual hU hW]
  have hc : specNorm (Uᵀ * W) ≤ 1 := by
    have h := specNorm_mul_le Uᵀ W
    rw [specNorm_transpose] at h
    exact h.trans (by nlinarith [specNorm_le_one_of_orthonormal hU,
      specNorm_le_one_of_orthonormal hW, specNorm_nonneg U, specNorm_nonneg W])
  have hi := Matrix.nonsing_inv_mul (Uᵀ * W) ((Matrix.isUnit_iff_isUnit_det _).mp hUW)
  calc
    specNorm (projResidual U W) =
        specNorm (projResidual U W * (Uᵀ * W)⁻¹ * (Uᵀ * W)) := by
      rw [Matrix.mul_assoc, hi, Matrix.mul_one]
    _ ≤ overlapTangentNorm U W * specNorm (Uᵀ * W) := specNorm_mul_le _ _
    _ ≤ overlapTangentNorm U W := by
      nlinarith [overlapTangentNorm_nonneg U W]

/-- Frobenius projector gap from the overlap tangent, including empty frames. -/
theorem frobNorm_sub_frame_projector_le_overlapTangentNorm {U W : Matrix m k ℝ}
    (hU : HasOrthonormalCols U) (hW : HasOrthonormalCols W) (hUW : IsUnit (Uᵀ * W)) :
    frobNorm (U * Uᵀ - W * Wᵀ) ≤
      Real.sqrt (2 * Fintype.card k) * overlapTangentNorm U W := by
  have hg := specNorm_sub_frame_projector_le_overlapTangentNorm hU hW hUW
  change specNorm (U * Uᴴ - W * Wᴴ) ≤ _ at hg
  rw [specNorm_sub_frame_projector_eq_residual hU hW] at hg
  have hF := frobSq_mul_le_specNorm_sq_mul_frobSq (projResidual U W) (1 : Matrix k k ℝ)
  have hone : frobSq (1 : Matrix k k ℝ) = Fintype.card k := by
    simp [frobSq_eq_sum_sq, Matrix.one_apply]
  rw [Matrix.mul_one, hone] at hF
  have he := frobSq_sub_frame_projector_eq_two_mul_residual hU hW
  have hs := frobNorm_sq (U * Uᵀ - W * Wᵀ)
  change _ = frobSq (U * Uᴴ - W * Wᴴ) at hs
  rw [he] at hs
  have hmul := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (specNorm_nonneg _) hg 2) (show (0 : ℝ) ≤ Fintype.card k by positivity)
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * Fintype.card k by positivity)
  have hn := overlapTangentNorm_nonneg U W
  have hp : 0 ≤ Real.sqrt (2 * Fintype.card k) * overlapTangentNorm U W := by positivity
  nlinarith [frobNorm_nonneg (U * Uᵀ - W * Wᵀ)]

end NLAlib
