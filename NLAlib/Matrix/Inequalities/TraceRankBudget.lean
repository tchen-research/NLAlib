/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Inequalities.KyFan
import NLAlib.Matrix.Spectral.ThinSVD
import NLAlib.Matrix.Basic.PosSemidefTrace

/-!
# Trace error and the rank budget

Every PSD residual from a rank-at-most-`k` approximation has trace at least
the corresponding spectral trace tail. A thin SVD provides a frame of the
approximation range, and the native Ky Fan principle bounds its capture.
Source: `determinantal.tex`, trace rank budget; helpers for
`rpcholesky-factorial-trace-tail`.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvalue prefix and its complementary trace tail partition the trace,
at every cutoff including cutoffs beyond the dimension. -/
theorem eigenvaluePrefix_add_spectralTraceTail {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) :
    eigenvaluePrefix hA k + spectralTraceTail A hA k = RCLike.re A.trace := by
  rw [eigenvaluePrefix, sumLargest_eq_prefix_of_antitone _ hA.eigenvalues₀_antitone,
    spectralTraceTail, ← Finset.sum_add_distrib]
  have ht : RCLike.re A.trace = ∑ i : Fin (Fintype.card n), hA.eigenvalues₀ i := by
    rw [hA.trace_eq_sum_eigenvalues, map_sum]
    simp only [RCLike.ofReal_re]
    exact sum_eigenvalues_eq_sum_sorted hA id
  rw [ht]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : ℕ) < k
  · simp [hi, not_le.mpr hi]
  · simp [hi, not_lt.mp hi]

/-- Removing more leading PSD eigenvalues can only decrease the trace tail. -/
theorem spectralTraceTail_antitone {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    Antitone (spectralTraceTail A hA.isHermitian) := by
  intro a b hab
  unfold spectralTraceTail
  apply Finset.sum_le_sum
  intro i _
  by_cases hb : b ≤ (i : ℕ)
  · simp [hb, hab.trans hb]
  · by_cases ha : a ≤ (i : ℕ)
    · simpa [hb, ha] using eigenvalues₀_nonneg_of_posSemidef hA i
    · simp [hb, ha]

/-- A PSD residual from any rank-at-most-`k` approximation has trace at least
the optimal trace tail. The approximating difference need not itself be PSD. -/
theorem spectralTraceTail_le_re_trace_of_rank_sub_le {A R : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hR : R.PosSemidef) {k : ℕ} (hr : (A - R).rank ≤ k) :
    spectralTraceTail A hA.isHermitian k ≤ RCLike.re R.trace := by
  let B := A - R
  obtain ⟨U, V, h⟩ := exists_isThinSVD B
  have hFix : (U * Uᴴ) * B = B := by
    rw [← h.mul_moorePenroseInverse_eq]
    exact mul_moorePenroseInverse_mul B
  have hTrace : (Uᴴ * B * U).trace = B.trace := by
    rw [Matrix.trace_mul_cycle, hFix]
  have hNonneg := re_trace_nonneg_of_posSemidef (hR.conjTranspose_mul_mul_same U)
  have hComp : RCLike.re B.trace ≤ RCLike.re (Uᴴ * A * U).trace := by
    have he : Uᴴ * R * U = Uᴴ * A * U - Uᴴ * B * U := by
      dsimp only [B]
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [he, Matrix.trace_sub, map_sub, hTrace] at hNonneg
    linarith
  have hFan := trace_compression_le_eigenvaluePrefix hA.isHermitian h.left_orth
  simp only [Fintype.card_fin] at hFan
  have hSplit := eigenvaluePrefix_add_spectralTraceTail hA.isHermitian B.rank
  have hMono := spectralTraceTail_antitone hA hr
  have he : RCLike.re B.trace = RCLike.re A.trace - RCLike.re R.trace := by
    simp only [B, Matrix.trace_sub, map_sub]
  linarith

end NLAlib
