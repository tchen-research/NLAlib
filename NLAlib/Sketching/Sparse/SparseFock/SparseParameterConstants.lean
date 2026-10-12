/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Explicit sparse-embedding constants

Definitions and certified scalar bounds for the support, band, and sparsity constants.
Ported from `SparseFockFormal.PaperParameters` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace PaperParameters

/-- The convex-order constant `(1 - exp (-1))⁻¹`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def cStar : ℝ := (1 - Real.exp (-1))⁻¹

/-- The common band constant `3 + sqrt 2`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def Cband : ℝ := 3 + Real.sqrt 2

/-- The global parameter constant `90 * cStar²`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def L : ℝ := 90 * cStar ^ 2

/-- The paper's base-two failure order.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def failureOrder (d : ℕ) (delta : ℝ) : ℕ :=
  max 1 ⌈Real.logb 2 ((d : ℝ) / delta)⌉₊

/-- `D_q = d + 2q + 1`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def Dq (d q : ℕ) : ℕ := d + 2 * q + 1

/-- Rounded sparsity `ceil (L(2q+1)/epsilon)`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def roundedS (q : ℕ) (epsilon : ℝ) : ℕ :=
  ⌈L * ((2 * q + 1 : ℕ) : ℝ) / epsilon⌉₊

/-- The unrounded row target `L² D_q / epsilon²`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def M0 (d q : ℕ) (epsilon : ℝ) : ℝ :=
  L ^ 2 * (Dq d q : ℝ) / epsilon ^ 2

/-- Rounded stack height `ceil (M0/s)`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def roundedB (d q : ℕ) (epsilon : ℝ) : ℕ :=
  ⌈M0 d q epsilon / roundedS q epsilon⌉₊

/-- Rounded row count, exactly divisible by the sparsity.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def roundedM (d q : ℕ) (epsilon : ℝ) : ℕ :=
  roundedS q epsilon * roundedB d q epsilon

/-- The uniform band envelope evaluated at grade at most `2q`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def betaEnvelope (d q : ℕ) (m s : ℝ) : ℝ :=
  Cband * (Real.sqrt ((Dq d q : ℝ) / m) +
    (Dq d q : ℝ) / m + ((2 * q + 1 : ℕ) : ℝ) / s)

/-- The Markov moment base after the convex-order factor `cStar²`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
noncomputable def roundedMomentBase (d q : ℕ) (epsilon : ℝ) : ℝ :=
  3 * cStar ^ 2 *
    betaEnvelope d q (roundedM d q epsilon) (roundedS q epsilon) / epsilon

/-- The rounded row count is exactly the product of rounded sparsity and block size.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem roundedM_eq_s_mul_b (d q : ℕ) (epsilon : ℝ) :
    roundedM d q epsilon = roundedS q epsilon * roundedB d q epsilon := rfl

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
theorem cStar_pos : 0 < cStar := by
  exact inv_pos.mpr expGap_pos

/-- The support-gap comparison constant exceeds one.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem one_lt_cStar : 1 < cStar := by
  rw [cStar]
  exact (one_lt_inv₀ expGap_pos).2 expGap_lt_one

/-- Certified decimal bound from the paper: `cStar < 1.582`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem cStar_lt_1582 : cStar < (791 : ℝ) / 500 := by
  rw [cStar, inv_lt_iff_one_lt_mul₀ expGap_pos]
  nlinarith [Real.exp_neg_one_lt_d9]

/-- The explicit sparsity constant is positive.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem L_pos : 0 < L := by
  rw [L]
  exact mul_pos (by norm_num) (sq_pos_of_pos cStar_pos)

/-- The explicit sparsity constant exceeds ninety.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ninety_lt_L : (90 : ℝ) < L := by
  have hsq : (1 : ℝ) < cStar ^ 2 := by
    nlinarith [one_lt_cStar, cStar_pos]
  rw [L]
  nlinarith

/-- Certified global-constant bound from the paper: `L < 226`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem L_lt_226 : L < (226 : ℝ) := by
  have hsq : cStar ^ 2 < ((791 : ℝ) / 500) ^ 2 := by
    simpa [pow_two] using
      mul_self_lt_mul_self cStar_pos.le cStar_lt_1582
  rw [L]
  nlinarith

/-- The square root of two is strictly below 71/50.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sqrt_two_lt_142 : Real.sqrt 2 < (71 : ℝ) / 50 := by
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 71 / 50)).2 (by norm_num)

/-- The numerical moment base in the v1.4 report.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Cband_div_ten_lt_442 : Cband / 10 < (221 : ℝ) / 500 := by
  rw [Cband]
  nlinarith [sqrt_two_lt_142]

/-- The band constant divided by ten is strictly below one half.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Cband_div_ten_lt_half : Cband / 10 < (1 : ℝ) / 2 := by
  exact Cband_div_ten_lt_442.trans (by norm_num)

/-- The band constant is positive.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Cband_pos : 0 < Cband := by
  rw [Cband]
  positivity

/-- The total band envelope is nonnegative at positive row count and sparsity.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem betaEnvelope_nonneg {d q : ℕ} {m s : ℝ}
    (hm : 0 < m) (hs : 0 < s) :
    0 ≤ betaEnvelope d q m s := by
  rw [betaEnvelope]
  exact mul_nonneg Cband_pos.le <| add_nonneg
    (add_nonneg (Real.sqrt_nonneg _)
      (div_nonneg (by positivity) hm.le))
    (div_nonneg (by positivity) hs.le)

end PaperParameters

end NLAlib.SparseFock
