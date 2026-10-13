/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Explicit sparse-embedding constants

The public parameter functions `sparseMomentOrder` (`q = max 1 ⌈log₂ (d/δ)⌉`),
`sparseColumnSparsity` (`s`), `sparseBlockRows` (`b`) and `sparseRows` (`m = s * b`), and the
proof-internal constants `convexOrderConstant`, `bandConstant`, `scaleConstant`, `rowTarget`,
`momentDim`, `bandEnvelope` and `momentBase` (namespace `NLAlib.SparseSketch`) with certified
scalar bounds.
Ported from `SparseFockFormal.PaperParameters` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch

/-- The convex-order constant `(1 - exp (-1))⁻¹`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def convexOrderConstant : ℝ := (1 - Real.exp (-1))⁻¹

/-- The common band constant `3 + sqrt 2`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def bandConstant : ℝ := 3 + Real.sqrt 2

/-- The global parameter constant `90 * cStar²`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def scaleConstant : ℝ := 90 * convexOrderConstant ^ 2

/-- The paper's base-two failure order.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def _root_.NLAlib.sparseMomentOrder (d : ℕ) (delta : ℝ) : ℕ :=
  max 1 ⌈Real.logb 2 ((d : ℝ) / delta)⌉₊

/-- `D_q = d + 2q + 1`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def momentDim (d q : ℕ) : ℕ := d + 2 * q + 1

/-- Rounded sparsity `ceil (scaleConstant(2q+1)/epsilon)`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def _root_.NLAlib.sparseColumnSparsity (q : ℕ) (epsilon : ℝ) : ℕ :=
  ⌈scaleConstant * ((2 * q + 1 : ℕ) : ℝ) / epsilon⌉₊

/-- The unrounded row target `L² D_q / epsilon²`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def rowTarget (d q : ℕ) (epsilon : ℝ) : ℝ :=
  scaleConstant ^ 2 * (momentDim d q : ℝ) / epsilon ^ 2

/-- Rounded stack height `ceil (rowTarget/s)`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def _root_.NLAlib.sparseBlockRows (d q : ℕ) (epsilon : ℝ) : ℕ :=
  ⌈rowTarget d q epsilon / sparseColumnSparsity q epsilon⌉₊

/-- Rounded row count, exactly divisible by the sparsity.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def _root_.NLAlib.sparseRows (d q : ℕ) (epsilon : ℝ) : ℕ :=
  sparseColumnSparsity q epsilon * sparseBlockRows d q epsilon

/-- The uniform band envelope evaluated at grade at most `2q`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def bandEnvelope (d q : ℕ) (m s : ℝ) : ℝ :=
  bandConstant * (Real.sqrt ((momentDim d q : ℝ) / m) +
    (momentDim d q : ℝ) / m + ((2 * q + 1 : ℕ) : ℝ) / s)

/-- The Markov moment base after the convex-order factor `cStar²`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def momentBase (d q : ℕ) (epsilon : ℝ) : ℝ :=
  3 * convexOrderConstant ^ 2 *
    bandEnvelope d q (sparseRows d q epsilon) (sparseColumnSparsity q epsilon) / epsilon

/-- The rounded row count is exactly the product of rounded sparsity and block size.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem sparseRows_eq_s_mul_b (d q : ℕ) (epsilon : ℝ) :
    sparseRows d q epsilon = sparseColumnSparsity q epsilon * sparseBlockRows d q epsilon := rfl

/-- The nonzero-support comparison gap one minus exp minus one is positive.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expGap_pos : 0 < 1 - Real.exp (-1) := by
  linarith [Real.exp_neg_one_lt_half]

/-- The nonzero-support comparison gap is strictly below one.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem expGap_lt_one : 1 - Real.exp (-1) < 1 := by
  linarith [Real.exp_pos (-1)]

/-- The reciprocal support-gap comparison constant is positive.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem convexOrderConstant_pos : 0 < convexOrderConstant := by
  exact inv_pos.mpr expGap_pos

/-- The support-gap comparison constant exceeds one.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem one_lt_convexOrderConstant : 1 < convexOrderConstant := by
  rw [convexOrderConstant]
  exact (one_lt_inv₀ expGap_pos).2 expGap_lt_one

/-- Certified decimal bound from the paper: `convexOrderConstant < 1.582`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem convexOrderConstant_lt_1582 : convexOrderConstant < (791 : ℝ) / 500 := by
  rw [convexOrderConstant, inv_lt_iff_one_lt_mul₀ expGap_pos]
  nlinarith [Real.exp_neg_one_lt_d9]

/-- The explicit sparsity constant is positive.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem scaleConstant_pos : 0 < scaleConstant := by
  rw [scaleConstant]
  exact mul_pos (by norm_num) (sq_pos_of_pos convexOrderConstant_pos)

/-- The explicit sparsity constant exceeds ninety.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ninety_lt_scaleConstant : (90 : ℝ) < scaleConstant := by
  have hsq : (1 : ℝ) < convexOrderConstant ^ 2 := by
    nlinarith [one_lt_convexOrderConstant, convexOrderConstant_pos]
  rw [scaleConstant]
  nlinarith

/-- Certified global-constant bound from the paper: `scaleConstant < 226`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem scaleConstant_lt_226 : scaleConstant < (226 : ℝ) := by
  have hsq : convexOrderConstant ^ 2 < ((791 : ℝ) / 500) ^ 2 := by
    simpa [pow_two] using
      mul_self_lt_mul_self convexOrderConstant_pos.le convexOrderConstant_lt_1582
  rw [scaleConstant]
  nlinarith

/-- The square root of two is strictly below 71/50.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sqrt_two_lt_142 : Real.sqrt 2 < (71 : ℝ) / 50 := by
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 71 / 50)).2 (by norm_num)

/-- The numerical moment base in the v1.4 report.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem bandConstant_div_ten_lt_442 : bandConstant / 10 < (221 : ℝ) / 500 := by
  rw [bandConstant]
  nlinarith [sqrt_two_lt_142]

/-- The band constant divided by ten is strictly below one half.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem bandConstant_div_ten_lt_half : bandConstant / 10 < (1 : ℝ) / 2 := by
  exact bandConstant_div_ten_lt_442.trans (by norm_num)

/-- The band constant is positive.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem bandConstant_pos : 0 < bandConstant := by
  rw [bandConstant]
  positivity

/-- The total band envelope is nonnegative at positive row count and sparsity.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem bandEnvelope_nonneg {d q : ℕ} {m s : ℝ}
    (hm : 0 < m) (hs : 0 < s) :
    0 ≤ bandEnvelope d q m s := by
  rw [bandEnvelope]
  exact mul_nonneg bandConstant_pos.le <| add_nonneg
    (add_nonneg (Real.sqrt_nonneg _)
      (div_nonneg (by positivity) hm.le))
    (div_nonneg (by positivity) hs.le)

end NLAlib.SparseSketch
