/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Norms.ComplexSchattenDuality

/-! # Convexity of the nuclear norm over real and complex matrix spaces

The native attained nuclear–spectral trace pairing and the generic von Neumann
inequality imply convexity on the underlying real vector space.
Source: Bhatia (1997), §IV.2; Cai–Candès–Shen (2010), Theorem 2.1.
-/

noncomputable section
open scoped Matrix ENNReal
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

private theorem frobInner_le_nuclearNorm_of_spectral_contraction
    (A T : Matrix m n 𝕜) (hT : specNorm T ≤ 1) : frobInner A T ≤ nuclearNorm A := by
  calc
    frobInner A T ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues T i := frobInner_le_sum_singularValues_mul A T
    _ ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), singularValues A i :=
      Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (singularValues_nonneg A i)
        ((singularValues_le_specNorm T i).trans hT)
    _ = nuclearNorm A := (nuclearNorm_eq_sum_range A).symm

/-- The nuclear norm is convex on the real vector space of arbitrary finite real or
complex rectangular matrices. No rank, dimension, or nonzero assumptions are needed.
Cai–Candès–Shen (2010), Theorem 2.1 (convexity ingredient). -/
theorem convexOn_nuclearNorm : ConvexOn ℝ Set.univ (nuclearNorm : Matrix m n 𝕜 → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro A _ B _ a b ha hb _
  obtain ⟨T, hT, hpair⟩ := exists_schattenNorm_le_one_trace_conjTranspose_mul_eq
    (a • A + b • B) (p := 1) (q := ∞)
  rw [schattenNorm_top] at hT
  rw [schattenNorm_one] at hpair
  have hInner : frobInner (a • A + b • B) T = nuclearNorm (a • A + b • B) := by
    rw [frobInner_eq_trace, hpair, RCLike.ofReal_re]
  rw [← hInner, frobInner_add_left, frobInner_smul_left, frobInner_smul_left]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (frobInner_le_nuclearNorm_of_spectral_contraction A T hT) ha)
    (mul_le_mul_of_nonneg_left (frobInner_le_nuclearNorm_of_spectral_contraction B T hT) hb)

end NLAlib
