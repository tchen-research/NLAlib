import NLAlib.Matrix.SpectralBounds
import NLAlib.Matrix.MoorePenrose

/-!
# Rank-dependent comparison of the Frobenius and spectral norms

This completes the advertised upper comparison in atlas `norms-frob-spec`.
The rank counts the nonzero singular values, and each such value is bounded by
the largest one. No positive-rank or nonempty-dimension hypothesis is needed.

Source: Horn–Johnson, Matrix Analysis, §5.6.

The general Moore–Penrose norm is also identified using the smallest positive
singular value, with a separate zero-rank branch. No probabilistic estimates or
inverse-Wishart moments enter these deterministic identities.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- Every padded singular value is bounded by the spectral norm.
Horn–Johnson §5.6; atlas `norms-frob-spec`, `svd`. -/
theorem singularValues_le_specNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    singularValues A k ≤ specNorm A :=
  (singularValues_antitone A (Nat.zero_le k)).trans_eq (singularValues_zero_eq_specNorm A)

/-- The squared Frobenius norm is the sum of the squares of precisely the
positive singular values. Zero singular values contribute nothing.
Horn–Johnson §5.6; atlas `norms-frob-spec`, `svd`. -/
theorem frobSq_eq_sum_rank_singularValues_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A = ∑ k ∈ Finset.range A.rank, singularValues A k ^ 2 := by
  rw [frobSq_eq_sum_sq_singularValues]
  symm
  apply Finset.sum_subset
  · exact Finset.range_mono (le_min A.rank_le_height A.rank_le_width)
  · intro k _ hk
    rw [singularValues_eq_zero_of_rank_le A (by simpa only [Finset.mem_range, not_lt] using hk)]
    simp

/-- The rank-dependent squared norm comparison, including rank zero and
empty rectangular matrices. Horn–Johnson §5.6; atlas `norms-frob-spec`. -/
theorem frobSq_le_rank_mul_specNorm_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A ≤ (A.rank : ℝ) * specNorm A ^ 2 := by
  calc
    frobSq A = ∑ k ∈ Finset.range A.rank, singularValues A k ^ 2 :=
      frobSq_eq_sum_rank_singularValues_sq A
    _ ≤ ∑ _k ∈ Finset.range A.rank, specNorm A ^ 2 :=
      Finset.sum_le_sum (fun k _ => pow_le_pow_left₀
        (singularValues_nonneg A k) (singularValues_le_specNorm A k) 2)
    _ = (A.rank : ℝ) * specNorm A ^ 2 := by simp

/-- The Frobenius norm is at most the spectral norm times the square root of
the rank, with no excluded zero cases. Horn–Johnson §5.6; atlas `norms-frob-spec`. -/
theorem frobNorm_le_sqrt_rank_mul_specNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    frobNorm A ≤ Real.sqrt (A.rank : ℝ) * specNorm A := by
  apply (sq_le_sq₀ (frobNorm_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (specNorm_nonneg A))).mp
  rw [frobNorm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg A.rank)]
  exact frobSq_le_rank_mul_specNorm_sq A

private theorem specNorm_inverse_rectDiag_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    specNorm (rectDiag (fun k => (singularValues A k)⁻¹) :
        Matrix (Fin n) (Fin m) ℝ) ^ 2 =
      ‖(fun i : Fin m => (singularValues A i)⁻¹ ^ 2)‖ := by
  rw [specNorm_sq_eq_specNorm_transpose_mul_self, transpose_rectDiag_mul_rectDiag]
  have he : (fun i : Fin m =>
      if (i : ℕ) < n then (singularValues A i)⁻¹ ^ 2 else 0) =
      (fun i : Fin m => (singularValues A i)⁻¹ ^ 2) := by
    funext i
    by_cases hin : (i : ℕ) < n
    · simp only [if_pos hin]
    · rw [if_neg hin, singularValues_eq_zero_of_width_le A (not_lt.mp hin)]
      simp
  rw [he, specNorm_eq_norm, Matrix.l2_opNorm_diagonal]

/-- For positive rank, the spectral norm of the general inverse is the
reciprocal of the smallest positive singular value, at index `rank A - 1`.
This is the correct formula for rank-deficient matrices as well as full-rank
matrices. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hr : 0 < A.rank) :
    specNorm (moorePenroseInverse A) = 1 / singularValues A (A.rank - 1) := by
  let r := A.rank - 1
  have hrrank : r < A.rank := by dsimp [r]; omega
  have hrm : r < m := lt_of_lt_of_le hrrank A.rank_le_height
  have hs : 0 < singularValues A r := (singularValues_pos_iff A r).mpr hrrank
  have hmax : ‖(fun i : Fin m => (singularValues A i)⁻¹ ^ 2)‖ =
      (singularValues A r)⁻¹ ^ 2 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).mpr
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hir : (i : ℕ) < A.rank
      · have hir' : (i : ℕ) ≤ r := by dsimp [r]; omega
        have hsi := singularValues_antitone A hir'
        have hiinv : (singularValues A i)⁻¹ ≤ (singularValues A r)⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hs hsi
        exact pow_le_pow_left₀ (inv_nonneg.mpr (singularValues_nonneg A i)) hiinv 2
      · rw [singularValues_eq_zero_of_rank_le A (not_lt.mp hir), inv_zero, zero_pow (by decide)]
        exact sq_nonneg _
    · have hlower := norm_le_pi_norm
        (fun i : Fin m => (singularValues A i)⁻¹ ^ 2) ⟨r, hrm⟩
      change ‖(singularValues A r)⁻¹ ^ 2‖ ≤
        ‖(fun i : Fin m => (singularValues A i)⁻¹ ^ 2)‖ at hlower
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((singularValues A r)⁻¹))] at hlower
      exact hlower
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A
  have hn : specNorm (moorePenroseInverse A) =
      specNorm (rectDiag (fun k => (singularValues A k)⁻¹) :
        Matrix (Fin n) (Fin m) ℝ) := by
    rw [hSVD.moorePenroseInverse_eq,
      specNorm_mul_transpose_right_of_hasOrthonormalCols hSVD.transpose_mul_left,
      specNorm_mul_left_of_hasOrthonormalCols hSVD.transpose_mul_right]
  have hsq : specNorm (moorePenroseInverse A) ^ 2 = (singularValues A r)⁻¹ ^ 2 := by
    rw [hn, specNorm_inverse_rectDiag_sq, hmax]
  have he := (sq_eq_sq₀ (specNorm_nonneg (moorePenroseInverse A))
    (inv_nonneg.mpr hs.le)).mp hsq
  simpa only [r, one_div] using he

/-- At rank zero the general Moore–Penrose inverse is zero; no division by a
nonexistent positive singular value is used. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem moorePenroseInverse_eq_zero_of_rank_eq_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hr : A.rank = 0) :
    moorePenroseInverse A = 0 := by
  have hσ : ∀ k : ℕ, singularValues A k = 0 := fun k =>
    singularValues_eq_zero_of_rank_le A (by rw [hr]; exact Nat.zero_le k)
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A
  rw [hSVD.moorePenroseInverse_eq]
  have hd : (rectDiag (fun k => (singularValues A k)⁻¹) :
      Matrix (Fin n) (Fin m) ℝ) = 0 := by
    ext i j
    simp [rectDiag_apply, hσ]
  rw [hd, Matrix.mul_zero, Matrix.zero_mul]

/-- The complete spectral-norm formula for the general Moore–Penrose inverse:
zero at rank zero and the reciprocal of the smallest positive singular value
otherwise. Empty dimensions are covered by the rank-zero branch.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem specNorm_moorePenroseInverse_eq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    specNorm (moorePenroseInverse A) =
      if A.rank = 0 then 0 else 1 / singularValues A (A.rank - 1) := by
  by_cases hr : A.rank = 0
  · rw [if_pos hr, moorePenroseInverse_eq_zero_of_rank_eq_zero A hr]
    exact specNorm_zero
  · rw [if_neg hr]
    exact specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive A
      (Nat.pos_of_ne_zero hr)

end NLAlib
