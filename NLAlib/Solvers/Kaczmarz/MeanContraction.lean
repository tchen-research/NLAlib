/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.Kaczmarz.Mean
import NLAlib.Matrix.Norms.RayleighNorm

/-!
# Row-space contraction of the Kaczmarz mean

The mean error operator is the identity on the null space. Its geometric contraction
therefore applies only to row-space errors. Compressing it with the Moore–Penrose row
projector gives a positive contraction on the entire ambient space, without a full-rank
assumption. Source: Epperly–Goldshlager–Webber 2024, tail-averaged randomized Kaczmarz, covariance argument.
Atlas: `tail-averaged-kaczmarz` (correlation kernel).
-/

noncomputable section
open scoped Matrix
namespace NLAlib.Kaczmarz
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
private theorem rowProjector_mul_transpose (A : Matrix m n ℝ) :
    (moorePenroseInverse A * A) * Aᵀ = Aᵀ := by
  have hs : (moorePenroseInverse A * A)ᵀ = moorePenroseInverse A * A :=
    (moorePenroseInverse_mul_isHermitian A).eq
  calc
    _ = (A * (moorePenroseInverse A * A))ᵀ := by rw [Matrix.transpose_mul, hs]
    _ = Aᵀ := by rw [← Matrix.mul_assoc, mul_moorePenroseInverse_mul]

omit [DecidableEq m] [DecidableEq n] in
private theorem rowProjector_mulVec_mem_range (A : Matrix m n ℝ) (v : n → ℝ) :
    (moorePenroseInverse A * A) *ᵥ v ∈ LinearMap.range Aᵀ.mulVecLin := by
  refine ⟨(moorePenroseInverse A)ᵀ *ᵥ v, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [← Matrix.transpose_mul]
  exact congrArg (fun M : Matrix n n ℝ => M *ᵥ v)
    (moorePenroseInverse_mul_isHermitian A).eq

omit [DecidableEq m] [DecidableEq n] in
private theorem rowProjector_mulVec_eq_self (A : Matrix m n ℝ) (v : n → ℝ)
    (hv : v ∈ LinearMap.range Aᵀ.mulVecLin) :
    (moorePenroseInverse A * A) *ᵥ v = v := by
  obtain ⟨w, rfl⟩ := hv
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, rowProjector_mul_transpose]

omit [DecidableEq m] [DecidableEq n] in
private theorem dotProduct_rowProjector_eq (A : Matrix m n ℝ) (v : n → ℝ) :
    v ⬝ᵥ ((moorePenroseInverse A * A) *ᵥ v) =
      ((moorePenroseInverse A * A) *ᵥ v) ⬝ᵥ ((moorePenroseInverse A * A) *ᵥ v) := by
  have hs : (moorePenroseInverse A * A)ᵀ = moorePenroseInverse A * A :=
    (moorePenroseInverse_mul_isHermitian A).eq
  symm
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs,
    Matrix.mulVec_mulVec, (moorePenroseInverse_mul_isIdempotentElem A).eq, dotProduct_comm]

/-- The row-space compression of the mean error operator has spectral norm at most the
usual contraction factor. The lower singular bound is required only on `range Aᵀ`. -/
theorem specNorm_rowProjector_sub_smul_gram_le
    (A : Matrix m n ℝ) (hA : A ≠ 0) (σ : ℝ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 ≤ ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2) :
    specNorm (moorePenroseInverse A * A - (frobSq A)⁻¹ • (Aᵀ * A)) ≤
      1 - σ ^ 2 / frobSq A := by
  simp only [norm_toLp_sq_eq_dotProduct_self] at hσ
  have hF : 0 < frobSq A := lt_of_le_of_ne (frobSq_nonneg A)
    (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
  have hq := rate_nonneg_of_lower_bound_on_range A σ hσ
  apply (specNorm_le_iff_abs_dotProduct_mulVec_le _
    ((moorePenroseInverse_mul_isHermitian A).sub
      ((show (Aᵀ * A).IsHermitian from Matrix.isHermitian_conjTranspose_mul_self A).smul
        (by simp [IsSelfAdjoint]))) _ hq).mpr
  intro v
  let w := (moorePenroseInverse A * A) *ᵥ v
  have hAv : A *ᵥ w = A *ᵥ v := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, mul_moorePenroseInverse_mul]
  have hww : w ⬝ᵥ w ≤ v ⬝ᵥ v := by
    rw [← dotProduct_rowProjector_eq]
    exact dotProduct_moorePenroseInverse_mul_mulVec_le_dotProduct_self A v
  have hu := mulVec_dotProduct_mulVec_le_frobSq_mul A w
  have hl := hσ w (rowProjector_mulVec_mem_range A v)
  rw [hAv] at hu hl
  have he : v ⬝ᵥ ((moorePenroseInverse A * A - (frobSq A)⁻¹ • (Aᵀ * A)) *ᵥ v) =
      w ⬝ᵥ w - ((A *ᵥ v) ⬝ᵥ (A *ᵥ v)) / frobSq A := by
    have hg : v ⬝ᵥ ((Aᵀ * A) *ᵥ v) = (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        Matrix.transpose_transpose]
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      dotProduct_rowProjector_eq, hg]
    simp only [w, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he]
  have hnonneg : 0 ≤ w ⬝ᵥ w - ((A *ᵥ v) ⬝ᵥ (A *ᵥ v)) / frobSq A := by
    exact sub_nonneg.mpr ((div_le_iff₀ hF).mpr (by simpa only [mul_comm] using hu))
  rw [abs_of_nonneg hnonneg]
  have hlow := (div_le_div_of_nonneg_right hl hF.le)
  calc
    _ ≤ (1 - σ ^ 2 / frobSq A) * (w ⬝ᵥ w) := by
      rw [sub_mul, one_mul, div_mul_eq_mul_div]
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hww hq

omit [DecidableEq m] in
private theorem meanError_mulVec_mem_range (A : Matrix m n ℝ) (v : n → ℝ)
    (hv : v ∈ LinearMap.range Aᵀ.mulVecLin) :
    (1 - (frobSq A)⁻¹ • (Aᵀ * A)) *ᵥ v ∈ LinearMap.range Aᵀ.mulVecLin := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ ⟨A *ᵥ v, rfl⟩)

private theorem pow_meanError_mulVec_eq_pow_rowCompression_mulVec
    (A : Matrix m n ℝ) (v : n → ℝ)
    (hv : v ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    (1 - (frobSq A)⁻¹ • (Aᵀ * A)) ^ k *ᵥ v =
      (moorePenroseInverse A * A - (frobSq A)⁻¹ • (Aᵀ * A)) ^ k *ᵥ v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec,
      ih _ (meanError_mulVec_mem_range A v hv), pow_succ, ← Matrix.mulVec_mulVec]
    congr 1
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, rowProjector_mulVec_eq_self A v hv]

open scoped Matrix.Norms.L2Operator in
/-- **Geometric row-space correlation bound.** A row-space error paired with its future
conditional mean has magnitude at most `q^k` times its squared norm. This is valid at every
rank; the null-space component must be excluded by `hv`. -/
theorem abs_dotProduct_pow_meanError_mulVec_le_of_mem_range
    (A : Matrix m n ℝ) (hA : A ≠ 0) (σ : ℝ)
    (hσ : ∀ v ∈ LinearMap.range Aᵀ.mulVecLin,
      σ ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 ≤ ‖WithLp.toLp 2 (A *ᵥ v)‖ ^ 2)
    (v : n → ℝ) (hv : v ∈ LinearMap.range Aᵀ.mulVecLin) (k : ℕ) :
    |v ⬝ᵥ ((1 - (frobSq A)⁻¹ • (Aᵀ * A)) ^ k *ᵥ v)| ≤
      (1 - σ ^ 2 / frobSq A) ^ k * ‖WithLp.toLp 2 v‖ ^ 2 := by
  simp only [norm_toLp_sq_eq_dotProduct_self]
  haveI : Nonempty n := Classical.byContradiction fun hn => hA (by
    haveI : IsEmpty n := not_nonempty_iff.mp hn
    ext i j
    exact isEmptyElim j)
  rw [pow_meanError_mulVec_eq_pow_rowCompression_mulVec A v hv]
  apply (abs_dotProduct_mulVec_le_specNorm _ v).trans
  apply mul_le_mul_of_nonneg_right _ (dotProduct_self_nonneg v)
  change ‖(moorePenroseInverse A * A - (frobSq A)⁻¹ • (Aᵀ * A)) ^ k‖ ≤ _
  exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _)
    (specNorm_rowProjector_sub_smul_gram_le A hA σ hσ) k)

end NLAlib.Kaczmarz
