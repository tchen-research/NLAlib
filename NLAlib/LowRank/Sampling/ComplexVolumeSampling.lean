import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.LowRank.Sampling.ComplexVolumeSamplingError
/-!
# Full actual complex volume-sampling error theorem

The true normalized determinant law and the genuine Hilbert column projector
satisfy the exact elementary spectral ratio and factor-`k+1` optimal error
bound. Empty samples, exact rank and infeasible sizes are proved in the
imported endpoint leaf. Source: `sa:volume-theorem`.
-/

noncomputable section
open MeasureTheory
open scoped Classical Matrix Matrix.Norms.Frobenius
namespace NLAlib

/-- The singular-value tail is the sorted Gram eigenvalue tail (both are padded with zeros
beyond `min (card m) (card n)`). -/
private theorem bestRankFrobSq_eq_complexGramTail {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℂ) (k : ℕ) :
    bestRankFrobSq A k = complexGramTail A k := by
  set f : ℕ → ℝ := fun i => if k ≤ i then singularValues A i ^ 2 else 0
  have hrange : ∀ N, min (Fintype.card m) (Fintype.card n) ≤ N →
      ∑ i ∈ Finset.range N, f i =
        ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), f i := fun N hN =>
    (Finset.sum_subset (Finset.range_mono hN) fun i _ hni => by
      simp [f, singularValues_eq_zero_of_min_le A (not_lt.1 (by simpa using hni))]).symm
  have h2 : complexGramTail A k = ∑ i ∈ Finset.range (Fintype.card n), f i := by
    rw [complexGramTail, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [f, complexGramEigenvalues, sq_singularValues_eq_eigenvalues₀]
  rw [bestRankFrobSq, h2, hrange _ (min_le_left _ _), hrange _ (min_le_right _ _)]

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
      (k + 1 : ℝ) * bestRankFrobSq A k := by
  refine ⟨integral_complexVolumeSampling_residual_norm_sq_eq_elementary_ratio A hk, ?_⟩
  rw [bestRankFrobSq_eq_complexGramTail]
  exact integral_complexVolumeSampling_residual_norm_sq_le_mul_tail A hk

/-- The actual complex volume law has factor-`k+1` error relative to the
genuine singular-vector truncation and its squared singular-value tail.
Source: `sa:volume-theorem`, exact displayed optimal-tail endpoint.
atlas: volume-sampling (partial) -/
theorem integral_complexVolumeSampling_residual_norm_sq_le_mul_truncatedSVD
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) {k : ℕ} (hk : k ≤ A.rank) :
    (∫ S, ‖complexVolumeSamplingResidual A S‖ ^ 2 ∂complexVolumeSamplingLaw A hk) ≤
      (k + 1 : ℝ) * ‖A - truncatedSVD A k‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_norm_sq, ← frobSq_eq_sum_norm_sq,
    frobSq_sub_truncatedSVD_eq_bestRankFrobSq, bestRankFrobSq_eq_complexGramTail]
  exact integral_complexVolumeSampling_residual_norm_sq_le_mul_tail A hk

end NLAlib
