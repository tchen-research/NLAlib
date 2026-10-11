import NLAlib.LowRank.ComplexVolumeSamplingEndpoints
import NLAlib.Matrix.ComplexBestRankApproximation

/-!
# Full actual complex volume-sampling error theorem

The true normalized determinant law and the genuine Hilbert column projector
satisfy the exact elementary spectral ratio and factor-`k+1` optimal error
bound. Empty samples, exact rank and infeasible sizes are proved in the
imported endpoint leaf. Source: `sa:volume-theorem`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical Matrix Matrix.Norms.Frobenius
namespace NLAlib

/-- The actual normalized complex volume law has exact expected projection
error `(k+1)e_(k+1)/e_k`, at most `k+1` times the true optimum over all
complex rank-at-most-`k` matrices. No determinant, projector, normalizer,
spectral tail or best-approximation identity is assumed.
Source: Deshpande–Rademacher–Vempala–Wang (2006); `sa:volume-theorem`.
atlas: volume-sampling -/
theorem integral_complexVolumeSampling_residual_norm_sq_eq_and_le_bestRank
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) {k : ℕ} (hk : k ≤ A.rank) :
    (∫ S, ‖complexVolumeSamplingResidual A S‖ ^ 2 ∂complexVolumeSamplingLaw A hk) =
      (k + 1 : ℝ) * complexGramElementary A (k + 1) / complexGramElementary A k ∧
    (∫ S, ‖complexVolumeSamplingResidual A S‖ ^ 2 ∂complexVolumeSamplingLaw A hk) ≤
      (k + 1 : ℝ) * complexBestRankFrobSq k A := by
  refine ⟨integral_complexVolumeSampling_residual_norm_sq_eq_elementary_ratio A hk, ?_⟩
  rw [complexBestRankFrobSq_eq_complexGramTail]
  exact integral_complexVolumeSampling_residual_norm_sq_le_mul_tail A hk

/-- The actual complex volume law has factor-`k+1` error relative to the
genuine singular-vector truncation and its squared singular-value tail.
Source: `sa:volume-theorem`, exact displayed optimal-tail endpoint.
atlas: volume-sampling (partial) -/
theorem integral_complexVolumeSampling_residual_norm_sq_le_mul_truncatedSVD
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) {k : ℕ} (hk : k ≤ A.rank) :
    (∫ S, ‖complexVolumeSamplingResidual A S‖ ^ 2 ∂complexVolumeSamplingLaw A hk) ≤
      (k + 1 : ℝ) * ‖A - complexTruncatedSVD A k‖ ^ 2 := by
  rw [frobenius_norm_sq_sub_complexTruncatedSVD_eq_tail]
  exact integral_complexVolumeSampling_residual_norm_sq_le_mul_tail A hk

end NLAlib
