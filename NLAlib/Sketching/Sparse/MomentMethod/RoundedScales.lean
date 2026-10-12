/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.MomentMethod.MomentOrder
set_option autoImplicit false

/-!
# Rounded sparse sketch dimensions

Ceiling estimates and explicit bounds for the rounded sparsity, block size, and row count.
Ported from `SparseFockFormal.PaperParameters` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch

/-- The auxiliary dimension parameter dominates the moment order.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem q_le_momentDim (d q : ℕ) : q ≤ momentDim d q := by
  simp [momentDim]
  omega

/-- The auxiliary dimension parameter is bounded by twice the sum of dimension and moment order.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem momentDim_le_two_mul_add {d q : ℕ} (hd : 1 ≤ d) :
    momentDim d q ≤ 2 * (d + q) := by
  simp [momentDim]
  omega

/-- Rounded sparsity dominates its unrounded ceiling argument.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseColumnSparsity_lower (q : ℕ) (epsilon : ℝ) :
    scaleConstant * ((2 * q + 1 : ℕ) : ℝ) / epsilon ≤ (sparseColumnSparsity q epsilon : ℝ) := by
  simpa [sparseColumnSparsity] using
    (Nat.le_ceil (scaleConstant * ((2 * q + 1 : ℕ) : ℝ) / epsilon))

/-- Rounded sparsity is positive at positive distortion tolerance.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseColumnSparsity_pos {q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < sparseColumnSparsity q epsilon := by
  have htarget : 0 < scaleConstant * ((2 * q + 1 : ℕ) : ℝ) / epsilon := by
    exact div_pos (mul_pos scaleConstant_pos (by positivity)) hepsilon
  have hcast : (0 : ℝ) < sparseColumnSparsity q epsilon :=
    htarget.trans_le (sparseColumnSparsity_lower q epsilon)
  exact_mod_cast hcast

/-- Rounded sparsity is below its unrounded value plus one.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseColumnSparsity_lt_add_one {q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (sparseColumnSparsity q epsilon : ℝ) <
      scaleConstant * ((2 * q + 1 : ℕ) : ℝ) / epsilon + 1 := by
  have htarget : 0 ≤ scaleConstant * ((2 * q + 1 : ℕ) : ℝ) / epsilon := by
    exact (div_pos (mul_pos scaleConstant_pos (by positivity)) hepsilon).le
  simpa [sparseColumnSparsity] using Nat.ceil_lt_add_one htarget

/-- The intermediate sparsity estimate used in line 1474 of the report.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseColumnSparsity_lt_six_scaleConstant_mul_q_div
    {q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (sparseColumnSparsity q epsilon : ℝ) < 6 * scaleConstant * (q : ℝ) / epsilon := by
  have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hcount : (((2 * q + 1 : ℕ) : ℝ)) ≤ 3 * (q : ℝ) := by
    push_cast
    linarith
  have hA :
      scaleConstant * ((2 * q + 1 : ℕ) : ℝ) / epsilon ≤
        3 * scaleConstant * (q : ℝ) / epsilon := by
    apply (div_le_div_iff_of_pos_right hepsilon0).2
    have := mul_le_mul_of_nonneg_left hcount scaleConstant_pos.le
    nlinarith
  have hL : (1 : ℝ) ≤ scaleConstant := by nlinarith [ninety_lt_scaleConstant]
  have hLq : (1 : ℝ) ≤ scaleConstant * (q : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ scaleConstant * (q : ℝ) := mul_le_mul hL hqReal (by norm_num) scaleConstant_pos.le
  have hunit : (1 : ℝ) ≤ 3 * scaleConstant * (q : ℝ) / epsilon := by
    apply (le_div_iff₀ hepsilon0).2
    nlinarith
  calc
    (sparseColumnSparsity q epsilon : ℝ) <
        scaleConstant * ((2 * q + 1 : ℕ) : ℝ) / epsilon + 1 :=
      sparseColumnSparsity_lt_add_one hepsilon0
    _ ≤ 3 * scaleConstant * (q : ℝ) / epsilon +
        (3 * scaleConstant * (q : ℝ) / epsilon) := add_le_add hA hunit
    _ = 6 * scaleConstant * (q : ℝ) / epsilon := by ring

/-- Certified explicit sparsity bound from line 1475: `s < 1356 q / epsilon`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseColumnSparsity_lt_1356
    {q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (sparseColumnSparsity q epsilon : ℝ) < 1356 * (q : ℝ) / epsilon := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hcoefficient : 6 * scaleConstant < (1356 : ℝ) := by
    nlinarith [scaleConstant_lt_226]
  have hnumerator : 6 * scaleConstant * (q : ℝ) < 1356 * (q : ℝ) := by
    exact mul_lt_mul_of_pos_right hcoefficient hqPos
  exact (sparseColumnSparsity_lt_six_scaleConstant_mul_q_div hq hepsilon0 hepsilon1).trans
    ((div_lt_div_iff_of_pos_right hepsilon0).2 hnumerator)

/-- The unrounded target row scale is positive at positive distortion tolerance.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowTarget_pos {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < rowTarget d q epsilon := by
  have hDqNat : 0 < momentDim d q := by simp [momentDim]
  have hDq : (0 : ℝ) < (momentDim d q : ℕ) := by exact_mod_cast hDqNat
  rw [rowTarget]
  exact div_pos (mul_pos (sq_pos_of_pos scaleConstant_pos) hDq)
    (sq_pos_of_pos hepsilon)

/-- Rounded block size dominates its unrounded ceiling argument.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseBlockRows_lower (d q : ℕ) (epsilon : ℝ) :
    rowTarget d q epsilon / (sparseColumnSparsity q epsilon : ℝ) ≤
      (sparseBlockRows d q epsilon : ℝ) := by
  simpa [sparseBlockRows] using
    (Nat.le_ceil (rowTarget d q epsilon / (sparseColumnSparsity q epsilon : ℝ)))

/-- The first scale condition in line 1432: the rounded row count is at least `rowTarget`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseRows_lower
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    rowTarget d q epsilon ≤ (sparseRows d q epsilon : ℝ) := by
  let s := sparseColumnSparsity q epsilon
  have hsNat : 0 < s := sparseColumnSparsity_pos hepsilon
  have hs : (0 : ℝ) < s := by exact_mod_cast hsNat
  have hb : rowTarget d q epsilon / (s : ℝ) ≤ (sparseBlockRows d q epsilon : ℝ) := by
    simpa [s] using sparseBlockRows_lower d q epsilon
  calc
    rowTarget d q epsilon = (s : ℝ) * (rowTarget d q epsilon / (s : ℝ)) := by
      field_simp
    _ ≤ (s : ℝ) * (sparseBlockRows d q epsilon : ℝ) :=
      mul_le_mul_of_nonneg_left hb hs.le
    _ = (sparseRows d q epsilon : ℕ) := by simp [sparseRows, s]

/-- The first scale condition in the literal form displayed in line 1432.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseRows_scale_condition
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    scaleConstant ^ 2 * (momentDim d q : ℝ) / epsilon ^ 2 ≤
      (sparseRows d q epsilon : ℝ) := by
  simpa [rowTarget] using sparseRows_lower (d := d) (q := q) hepsilon

/-- The exact ceiling estimate `m < rowTarget + s`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseRows_lt_rowTarget_add_s
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (sparseRows d q epsilon : ℝ) <
      rowTarget d q epsilon + sparseColumnSparsity q epsilon := by
  let s := sparseColumnSparsity q epsilon
  have hsNat : 0 < s := sparseColumnSparsity_pos hepsilon
  have hs : (0 : ℝ) < s := by exact_mod_cast hsNat
  have hquot : 0 ≤ rowTarget d q epsilon / (s : ℝ) := by
    exact (div_pos (rowTarget_pos hepsilon) hs).le
  have hb : (sparseBlockRows d q epsilon : ℝ) <
      rowTarget d q epsilon / (s : ℝ) + 1 := by
    simpa [sparseBlockRows, s] using Nat.ceil_lt_add_one hquot
  calc
    (sparseRows d q epsilon : ℝ) =
        (s : ℝ) * (sparseBlockRows d q epsilon : ℝ) := by simp [sparseRows, s]
    _ < (s : ℝ) * (rowTarget d q epsilon / (s : ℝ) + 1) :=
      mul_lt_mul_of_pos_left hb hs
    _ = rowTarget d q epsilon + s := by field_simp

/-- A coarse comparison showing that the rounded sparsity is below `rowTarget`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseColumnSparsity_lt_rowTarget
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (sparseColumnSparsity q epsilon : ℝ) < rowTarget d q epsilon := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hqDq : (q : ℝ) ≤ (momentDim d q : ℕ) := by
    exact_mod_cast q_le_momentDim d q
  have hsmall : 6 * (q : ℝ) * epsilon < scaleConstant * (momentDim d q : ℕ) := by
    calc
      6 * (q : ℝ) * epsilon ≤ 6 * (q : ℝ) := by
        simpa using mul_le_mul_of_nonneg_left hepsilon1
          (by positivity : (0 : ℝ) ≤ 6 * (q : ℝ))
      _ < scaleConstant * (q : ℝ) := by
        exact mul_lt_mul_of_pos_right (by nlinarith [ninety_lt_scaleConstant]) hqPos
      _ ≤ scaleConstant * (momentDim d q : ℕ) := mul_le_mul_of_nonneg_left hqDq scaleConstant_pos.le
  have hcore : 6 * scaleConstant * (q : ℝ) * epsilon <
      scaleConstant ^ 2 * (momentDim d q : ℕ) := by
    calc
      6 * scaleConstant * (q : ℝ) * epsilon = scaleConstant * (6 * (q : ℝ) * epsilon) := by ring
      _ < scaleConstant * (scaleConstant * (momentDim d q : ℕ)) := mul_lt_mul_of_pos_left hsmall
          scaleConstant_pos
      _ = scaleConstant ^ 2 * (momentDim d q : ℕ) := by ring
  have hscaled : 6 * scaleConstant * (q : ℝ) / epsilon < rowTarget d q epsilon := by
    rw [rowTarget]
    apply (div_lt_div_iff₀ hepsilon0 (sq_pos_of_pos hepsilon0)).2
    have hmul := mul_lt_mul_of_pos_right hcore hepsilon0
    nlinarith [sq_nonneg epsilon]
  exact (sparseColumnSparsity_lt_six_scaleConstant_mul_q_div hq hepsilon0 hepsilon1).trans hscaled

/-- The main rounded parameters always have at least two rows per stack.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem two_le_sparseBlockRows
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    2 ≤ sparseBlockRows d q epsilon := by
  have hsNat : 0 < sparseColumnSparsity q epsilon := sparseColumnSparsity_pos hepsilon0
  have hs : (0 : ℝ) < sparseColumnSparsity q epsilon := by exact_mod_cast hsNat
  have hsM : (sparseColumnSparsity q epsilon : ℝ) < rowTarget d q epsilon :=
    sparseColumnSparsity_lt_rowTarget hq hepsilon0 hepsilon1
  have hratio : (1 : ℝ) < rowTarget d q epsilon / sparseColumnSparsity q epsilon := by
    apply (lt_div_iff₀ hs).2
    simpa using hsM
  have hbCast : (1 : ℝ) < sparseBlockRows d q epsilon :=
    hratio.trans_le (sparseBlockRows_lower d q epsilon)
  exact_mod_cast hbCast

/-- The main rounded block size is at least two under the stated parameter hypotheses.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem two_le_main_sparseBlockRows
    {d : ℕ} {delta epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    2 ≤ sparseBlockRows d (sparseMomentOrder d delta) epsilon :=
  two_le_sparseBlockRows (one_le_sparseMomentOrder d delta) hepsilon0 hepsilon1

/-- The paper's `m < 2 rowTarget` rounding estimate.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseRows_lt_two_rowTarget
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (sparseRows d q epsilon : ℝ) < 2 * rowTarget d q epsilon := by
  have hm := sparseRows_lt_rowTarget_add_s (d := d) (q := q) hepsilon0
  have hs := sparseColumnSparsity_lt_rowTarget (d := d) hq hepsilon0 hepsilon1
  linarith

/-- The rounded row count is below three times the unrounded row scale.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseRows_lt_three_rowTarget
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (sparseRows d q epsilon : ℝ) < 3 * rowTarget d q epsilon := by
  exact (sparseRows_lt_two_rowTarget hq hepsilon0 hepsilon1).trans
    (by nlinarith [rowTarget_pos (d := d) (q := q) hepsilon0])

/-- The numerical upper bound for `3 rowTarget` used in lines 1492--1498.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem three_rowTarget_lt_306456
    {d q : ℕ} {epsilon : ℝ}
    (hd : 1 ≤ d) (hepsilon : 0 < epsilon) :
    3 * rowTarget d q epsilon <
      306456 * ((d : ℝ) + q) / epsilon ^ 2 := by
  have hDqNat : momentDim d q ≤ 2 * (d + q) := momentDim_le_two_mul_add hd
  have hDq : (momentDim d q : ℝ) ≤ 2 * ((d : ℝ) + q) := by
    exact_mod_cast hDqNat
  have hDqPosNat : 0 < momentDim d q := by simp [momentDim]
  have hDqPos : (0 : ℝ) < (momentDim d q : ℕ) := by exact_mod_cast hDqPosNat
  have hLsq : scaleConstant ^ 2 < (226 : ℝ) ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self scaleConstant_pos.le scaleConstant_lt_226
  have hnum : 3 * (scaleConstant ^ 2 * (momentDim d q : ℕ)) <
      306456 * ((d : ℝ) + q) := by
    calc
      3 * (scaleConstant ^ 2 * (momentDim d q : ℕ)) <
          3 * ((226 : ℝ) ^ 2 * (momentDim d q : ℕ)) := by
        exact mul_lt_mul_of_pos_left
          (mul_lt_mul_of_pos_right hLsq hDqPos) (by norm_num)
      _ ≤ 3 * ((226 : ℝ) ^ 2 * (2 * ((d : ℝ) + q))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hDq (by positivity)) (by norm_num)
      _ = 306456 * ((d : ℝ) + q) := by ring
  calc
    3 * rowTarget d q epsilon =
        (3 * (scaleConstant ^ 2 * (momentDim d q : ℕ))) / epsilon ^ 2 := by
      rw [rowTarget]
      ring
    _ < (306456 * ((d : ℝ) + q)) / epsilon ^ 2 :=
      (div_lt_div_iff_of_pos_right (sq_pos_of_pos hepsilon)).2 hnum
    _ = 306456 * ((d : ℝ) + q) / epsilon ^ 2 := rfl

/-- Certified explicit row bound from line 1497.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sparseRows_lt_306456
    {d q : ℕ} {epsilon : ℝ}
    (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (sparseRows d q epsilon : ℝ) <
      306456 * ((d : ℝ) + q) / epsilon ^ 2 :=
  (sparseRows_lt_three_rowTarget hq hepsilon0 hepsilon1).trans
    (three_rowTarget_lt_306456 hd hepsilon0)

end NLAlib.SparseSketch
