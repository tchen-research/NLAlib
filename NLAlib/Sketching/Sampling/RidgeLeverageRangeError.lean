import NLAlib.Matrix.Functions.RidgeRange
import NLAlib.Matrix.Functions.RidgeEffectiveDimension
import NLAlib.Matrix.Norms.LoewnerBounds

/-!
# Range error from a regularized approximation

A lower regularized Loewner approximation by `B Bᵀ` controls the spectral and Frobenius
errors of projection onto the actual range of `B`. The Frobenius guarantee uses the ridge
effective dimension and its singular-value tail bound. Rank-deficient sampled matrices
are handled by their canonical range projector.

Source: Chenakkod–Dereziński 2026, Lemma 3.3, with a general distortion parameter;
`sketching_lowrank_routes_2026_10_24/sketching.tex`, regularized range-error derivation.
Atlas: `regularized-approximation-range-error`.
-/

noncomputable section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {m n s : Type*} [Fintype m] [Fintype n] [Fintype s]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- A lower regularized approximation controls the actual projected Gram error by the
transpose ridge kernel. This retains the canonical range projector when `B` is deficient. -/
theorem conjTranspose_mul_one_sub_rangeProjector_mul_le_ridgeKernel
    (A : Matrix m n ℝ) (B : Matrix m s ℝ) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ε < 1)
    (happrox : (1 - ε) • ridgeGram Aᵀ ρ ≤ ridgeGram Bᵀ ρ) :
    Aᵀ * (1 - rangeProjector B) * A ≤
      (ρ / (1 - ε)) • ridgeKernel Aᵀ ρ := by
  classical
  have hα : 0 < 1 - ε := sub_pos.mpr hε
  let : Invertible (1 - ε) := invertibleOfNonzero hα.ne'
  have hi := inv_le_inv_of_posDef ((posDef_ridgeGram Aᵀ hρ).smul hα) happrox
  rw [Matrix.inv_smul _ _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (posDef_ridgeGram Aᵀ hρ).isUnit), invOf_eq_inv] at hi
  have hR : 1 - rangeProjector B ≤ (ρ / (1 - ε)) • (ridgeGram Aᵀ ρ)⁻¹ := by
    refine (one_sub_rangeProjector_le_smul_inv_ridgeGram B hρ).trans ?_
    have hh := smul_le_smul_of_nonneg_left hi hρ.le
    simpa only [smul_smul, div_eq_mul_inv] using hh
  have hp := (Matrix.le_iff.mp hR).conjTranspose_mul_mul_same A
  apply Matrix.le_iff.mpr
  simpa only [ridgeKernel, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc] using hp

/-- A lower regularized approximation bounds the squared spectral range error by
`ρ / (1 - ε)`. The theorem only needs `ε < 1`; the usual `0 ≤ ε` domain is included.
atlas: regularized-approximation-range-error (partial) -/
theorem specNorm_one_sub_rangeProjector_mul_sq_le_of_regularized_le
    (A : Matrix m n ℝ) (B : Matrix m s ℝ) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ε < 1)
    (happrox : (1 - ε) • ridgeGram Aᵀ ρ ≤ ridgeGram Bᵀ ρ) :
    specNorm ((1 - rangeProjector B) * A) ^ 2 ≤ ρ / (1 - ε) := by
  let R := (1 : Matrix m m ℝ) - rangeProjector B
  have hR := one_sub_projector_isHermitian_isIdempotentElem
    (rangeProjector_isHermitian B) (rangeProjector_isIdempotentElem B)
  have hRR : R * R = R := hR.2
  have hRT : Rᵀ = R := hR.1.eq
  have hGram : (R * A)ᴴ * (R * A) = Aᵀ * R * A := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hRT]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R A, hRR]
  have hc : 0 ≤ ρ / (1 - ε) := div_nonneg hρ.le (sub_pos.mpr hε).le
  apply specNorm_sq_le_of_conjTranspose_mul_self_le _ hc
  rw [hGram]
  refine (conjTranspose_mul_one_sub_rangeProjector_mul_le_ridgeKernel A B hρ hε happrox).trans ?_
  exact smul_le_smul_of_nonneg_left (ridgeKernel_le_one Aᵀ hρ) hc

/-- A lower regularized approximation bounds the squared Frobenius range error by
`ρ / (1 - ε)` times the actual ridge effective dimension.
atlas: regularized-approximation-range-error (partial) -/
theorem frobSq_one_sub_rangeProjector_mul_le_ridgeEffectiveDimension_of_regularized_le
    (A : Matrix m n ℝ) (B : Matrix m s ℝ) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ε < 1)
    (happrox : (1 - ε) • ridgeGram Aᵀ ρ ≤ ridgeGram Bᵀ ρ) :
    frobSq ((1 - rangeProjector B) * A) ≤
      ρ / (1 - ε) * ridgeEffectiveDimension A ρ := by
  let R := (1 : Matrix m m ℝ) - rangeProjector B
  have hR := one_sub_projector_isHermitian_isIdempotentElem
    (rangeProjector_isHermitian B) (rangeProjector_isIdempotentElem B)
  have hRR : R * R = R := hR.2
  have hRT : Rᵀ = R := hR.1.eq
  have hGram : (R * A)ᴴ * (R * A) = Aᵀ * R * A := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hRT]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R A, hRR]
  have hf : frobSq (R * A) = (Aᵀ * R * A).trace := by
    rw [frobSq_eq_re_trace_conjTranspose_mul_self, hGram, RCLike.re_to_real]
  have ht := (Matrix.le_iff.mp
    (conjTranspose_mul_one_sub_rangeProjector_mul_le_ridgeKernel A B hρ hε happrox)).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, ← ridgeEffectiveDimension_eq_trace Aᵀ ρ,
    ridgeEffectiveDimension_transpose A hρ] at ht
  rw [hf]
  exact sub_nonneg.mp ht

/-- The Frobenius range error is controlled by `kρ` plus the actual squared singular-value
tail, with denominator `1 - ε`. Target rank zero and vanishing tails are included.
atlas: regularized-approximation-range-error (partial) -/
theorem frobSq_one_sub_rangeProjector_mul_le_bestRankFrobSq_of_regularized_le
    (A : Matrix m n ℝ) (B : Matrix m s ℝ) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ε < 1)
    (happrox : (1 - ε) • ridgeGram Aᵀ ρ ≤ ridgeGram Bᵀ ρ) (k : ℕ) :
    frobSq ((1 - rangeProjector B) * A) ≤
      ((k : ℝ) * ρ + bestRankFrobSq A k) / (1 - ε) := by
  have hc : 0 ≤ ρ / (1 - ε) := div_nonneg hρ.le (sub_pos.mpr hε).le
  refine (frobSq_one_sub_rangeProjector_mul_le_ridgeEffectiveDimension_of_regularized_le
    A B hρ hε happrox).trans ?_
  calc
    ρ / (1 - ε) * ridgeEffectiveDimension A ρ ≤
        ρ / (1 - ε) * ((k : ℝ) + bestRankFrobSq A k / ρ) :=
      mul_le_mul_of_nonneg_left
        (ridgeEffectiveDimension_le_rank_add_div_bestRankFrobSq A hρ k) hc
    _ = ((k : ℝ) * ρ + bestRankFrobSq A k) / (1 - ε) := by
      field_simp [hρ.ne', (sub_pos.mpr hε).ne']

end NLAlib
