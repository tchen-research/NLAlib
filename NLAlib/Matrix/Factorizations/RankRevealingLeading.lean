import NLAlib.Matrix.Norms.BlockNormBounds
import NLAlib.Matrix.Factorizations.NearestPolar
import NLAlib.Matrix.Spectral.Weyl
/-!
# Leading singular-value bound from the RRQR exchange budget

Truncated leading-block SVDs give explicit rank competitors. The exact shared
budget controls every leading singular value with factor `sqrt(1+b)`.
Gu–Eisenstat 1996, Theorem 3.2; derivations §alg:rrqr.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Spectral Eckart–Young's lower bound on arbitrary finite index types,
using the actual native singular-value sequence. Horn–Johnson 2013,
Theorem 7.4.9.1; supports `rank-revealing-qr`. -/
theorem toEuclideanLin_singularValues_le_specNorm_sub_of_rank_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n ℝ) {k : ℕ} (hB : B.rank ≤ k) :
    A.toEuclideanLin.singularValues k ≤ specNorm (A - B) := by
  have hh := singularValues_le_specNorm_sub_of_rank_le
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (B.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (by simpa only [Matrix.rank_reindex] using hB)
  have hSub : A.reindex (Fintype.equivFin m) (Fintype.equivFin n) -
      B.reindex (Fintype.equivFin m) (Fintype.equivFin n) =
      (A - B).reindex (Fintype.equivFin m) (Fintype.equivFin n) := rfl
  rw [hSub, specNorm_reindex] at hh
  simp only [singularValues_reindex] at hh
  exact hh

/-- Every singular value of an invertible square matrix satisfies
`1 ≤ σᵢ(R)² ‖R⁻¹‖F²`. Gu–Eisenstat 1996, leading-block estimate. -/
theorem one_le_sq_singularValue_mul_frobSq_inv {k : ℕ}
    (R : Matrix (Fin k) (Fin k) ℝ) (hR : IsUnit R) {i : ℕ} (hi : i < k) :
    1 ≤ singularValues R i ^ 2 * frobSq R⁻¹ := by
  have h := singularValues_mul_le_specNorm_mul R⁻¹ R i
  rw [Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR)] at h
  rw [singularValues_eq_one_of_hasOrthonormalCols (by simp [HasOrthonormalCols]) le_rfl hi] at h
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h 2
  have hf := specNorm_sq_le_frobSq R⁻¹
  have hs := singularValues_nonneg R i
  nlinarith [mul_le_mul_of_nonneg_left hf (sq_nonneg (singularValues R i))]

/-- The exact shared RRQR budget bounds every leading singular value by
`σᵢ(block) ≤ sqrt(1+b) σᵢ(R)`. No factor is lost by separating interpolation
and residual estimates. The trailing row and column labels are arbitrary
finite types, and the leading index may be any `i < k`.
Gu–Eisenstat 1996, Theorem 3.2; derivations equation alg:rrqr-leading.
Supports `rank-revealing-qr`. -/
theorem singularValues_upper_block_le_sqrt_budget_mul {k : ℕ} {r q : Type*}
    [Fintype r] [Fintype q] [DecidableEq r] [DecidableEq q]
    (R : Matrix (Fin k) (Fin k) ℝ) (T : Matrix (Fin k) q ℝ) (D : Matrix r q ℝ)
    (hR : IsUnit R) (b : ℝ) (hb : 0 ≤ b)
    (hBudget : frobSq T + frobSq R⁻¹ * frobSq D ≤ b) {i : ℕ} (hi : i < k) :
    (Matrix.fromBlocks R (R * T) 0 D).toEuclideanLin.singularValues i ≤
      Real.sqrt (1 + b) * singularValues R i := by
  let Ri := truncatedSVD R i
  let B := Matrix.fromBlocks Ri (Ri * T) (0 : Matrix r (Fin k) ℝ) (0 : Matrix r q ℝ)
  have hBForm : B = Matrix.fromRows (1 : Matrix (Fin k) (Fin k) ℝ) (0 : Matrix r (Fin k) ℝ) *
      Ri * Matrix.fromCols (1 : Matrix (Fin k) (Fin k) ℝ) T := by
    simp only [B, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul,
      Matrix.mul_fromCols, Matrix.fromCols_fromRows_eq_fromBlocks, Matrix.mul_one]
  have hB : B.rank ≤ i := by
    rw [hBForm]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans (isBestRankApprox_truncatedSVD R i).1)
  have hDiff : Matrix.fromBlocks R (R * T) 0 D - B =
      Matrix.fromBlocks (R - Ri) ((R - Ri) * T) 0 D := by
    ext a c
    cases a <;> cases c <;> simp [B, Matrix.sub_mul]
  have hZ := specNorm_upper_block_sq_le (R - Ri) T D
  have hErr : specNorm (R - Ri) = singularValues R i := specNorm_sub_truncatedSVD_eq R i
  rw [hErr] at hZ
  have hInv := one_le_sq_singularValue_mul_frobSq_inv R hR hi
  have hDle := mul_le_mul_of_nonneg_right hInv (frobSq_nonneg D)
  have hBle := mul_le_mul_of_nonneg_left hBudget (sq_nonneg (singularValues R i))
  have hSq : specNorm (Matrix.fromBlocks (R - Ri) ((R - Ri) * T) 0 D) ^ 2 ≤
      (Real.sqrt (1 + b) * singularValues R i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + b)]
    nlinarith
  have hNorm := (sq_le_sq₀ (specNorm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (singularValues_nonneg R i))).mp hSq
  exact (toEuclideanLin_singularValues_le_specNorm_sub_of_rank_le _ B hB).trans
    (by simpa only [hDiff] using hNorm)

end NLAlib
