import NLAlib.Matrix.Norms.NuclearNorm
import NLAlib.Matrix.Norms.NuclearPSD
import NLAlib.Matrix.Spectral.EckartYoung

/-!
# Frobenius tails controlled by the nuclear norm

For a square matrix the squared best-rank error is at most the squared nuclear norm divided
by the positive target rank. For positive semidefinite real matrices this is the trace-square
bound used by Hutch++. Source: Meyer–Musco–Musco–Woodruff (2021), Lemma 3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The squared best-rank Frobenius tail is bounded by nuclear norm squared over target rank.
This includes target ranks at or beyond the dimension and empty matrices. -/
theorem bestRankFrobSq_le_nuclearNorm_sq_div (A : Matrix n n 𝕜) {k : ℕ} (hk : 0 < k) :
    bestRankFrobSq A k ≤ nuclearNorm A ^ 2 / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have htotal : nuclearNorm A = ∑ j ∈ Finset.range (Fintype.card n), singularValues A j := by
    rw [nuclearNorm_eq_sum_range, min_self]
  have hpos := singularValues_nonneg A
  by_cases hkN : k ≤ Fintype.card n
  · have hhead : (k : ℝ) * singularValues A k ≤ nuclearNorm A := by
      rw [htotal]
      calc
        _ = ∑ _j ∈ Finset.range k, singularValues A k := by simp
        _ ≤ ∑ j ∈ Finset.range k, singularValues A j := Finset.sum_le_sum fun j hj =>
          singularValues_antitone A (Finset.mem_range.mp hj).le
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkN)
          (fun j _ _ => hpos j)
    have htail : bestRankFrobSq A k ≤ singularValues A k * nuclearNorm A := by
      rw [bestRankFrobSq, htotal, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hkj
      · have hh := mul_le_mul_of_nonneg_right (singularValues_antitone A hkj) (hpos j)
        nlinarith
      · exact mul_nonneg (hpos k) (hpos j)
    apply (le_div_iff₀ hkR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hhead (nuclearNorm_nonneg A),
      mul_le_mul_of_nonneg_left htail hkR.le]
  · have hz : bestRankFrobSq A k = 0 := by
      unfold bestRankFrobSq
      apply Finset.sum_eq_zero
      intro j hj
      have hjN := Finset.mem_range.mp hj
      rw [if_neg (by omega)]
    rw [hz]
    positivity

/-- For a positive semidefinite matrix, the optimal squared Frobenius tail is at most
trace squared divided by the positive target rank, including oversized ranks. -/
theorem bestRankFrobSq_le_trace_sq_div {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {k : ℕ} (hk : 0 < k) : bestRankFrobSq A k ≤ A.trace ^ 2 / k := by
  simpa only [nuclearNorm_eq_trace_of_posSemidef hA] using
    bestRankFrobSq_le_nuclearNorm_sq_div A hk

end NLAlib
