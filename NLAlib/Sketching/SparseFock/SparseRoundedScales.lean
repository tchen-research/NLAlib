/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.SparseFailureOrder

set_option autoImplicit false

/-!
# Rounded sparse sketch dimensions

Ceiling estimates and explicit bounds for the rounded sparsity, block size, and row count.
Ported from `SparseFockFormal.PaperParameters` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace PaperParameters

/-- The auxiliary dimension parameter dominates the moment order.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem q_le_Dq (d q : ℕ) : q ≤ Dq d q := by
  simp [Dq]
  omega

/-- The auxiliary dimension parameter is bounded by twice the sum of dimension and moment order.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Dq_le_two_mul_add {d q : ℕ} (hd : 1 ≤ d) :
    Dq d q ≤ 2 * (d + q) := by
  simp [Dq]
  omega

/-- Rounded sparsity dominates its unrounded ceiling argument.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedS_lower (q : ℕ) (epsilon : ℝ) :
    L * ((2 * q + 1 : ℕ) : ℝ) / epsilon ≤ (roundedS q epsilon : ℝ) := by
  simpa [roundedS] using
    (Nat.le_ceil (L * ((2 * q + 1 : ℕ) : ℝ) / epsilon))

/-- Rounded sparsity is positive at positive distortion tolerance.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedS_pos {q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < roundedS q epsilon := by
  have htarget : 0 < L * ((2 * q + 1 : ℕ) : ℝ) / epsilon := by
    exact div_pos (mul_pos L_pos (by positivity)) hepsilon
  have hcast : (0 : ℝ) < roundedS q epsilon :=
    htarget.trans_le (roundedS_lower q epsilon)
  exact_mod_cast hcast

/-- Rounded sparsity is below its unrounded value plus one.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedS_lt_add_one {q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (roundedS q epsilon : ℝ) <
      L * ((2 * q + 1 : ℕ) : ℝ) / epsilon + 1 := by
  have htarget : 0 ≤ L * ((2 * q + 1 : ℕ) : ℝ) / epsilon := by
    exact (div_pos (mul_pos L_pos (by positivity)) hepsilon).le
  simpa [roundedS] using Nat.ceil_lt_add_one htarget

/-- The intermediate sparsity estimate used in line 1474 of the report.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedS_lt_six_L_mul_q_div
    {q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedS q epsilon : ℝ) < 6 * L * (q : ℝ) / epsilon := by
  have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hcount : (((2 * q + 1 : ℕ) : ℝ)) ≤ 3 * (q : ℝ) := by
    push_cast
    linarith
  have hA :
      L * ((2 * q + 1 : ℕ) : ℝ) / epsilon ≤
        3 * L * (q : ℝ) / epsilon := by
    apply (div_le_div_iff_of_pos_right hepsilon0).2
    have := mul_le_mul_of_nonneg_left hcount L_pos.le
    nlinarith
  have hL : (1 : ℝ) ≤ L := by nlinarith [ninety_lt_L]
  have hLq : (1 : ℝ) ≤ L * (q : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ L * (q : ℝ) := mul_le_mul hL hqReal (by norm_num) L_pos.le
  have hunit : (1 : ℝ) ≤ 3 * L * (q : ℝ) / epsilon := by
    apply (le_div_iff₀ hepsilon0).2
    nlinarith
  calc
    (roundedS q epsilon : ℝ) <
        L * ((2 * q + 1 : ℕ) : ℝ) / epsilon + 1 :=
      roundedS_lt_add_one hepsilon0
    _ ≤ 3 * L * (q : ℝ) / epsilon +
        (3 * L * (q : ℝ) / epsilon) := add_le_add hA hunit
    _ = 6 * L * (q : ℝ) / epsilon := by ring

/-- Certified explicit sparsity bound from line 1475: `s < 1356 q / epsilon`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedS_lt_1356
    {q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedS q epsilon : ℝ) < 1356 * (q : ℝ) / epsilon := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hcoefficient : 6 * L < (1356 : ℝ) := by
    nlinarith [L_lt_226]
  have hnumerator : 6 * L * (q : ℝ) < 1356 * (q : ℝ) := by
    exact mul_lt_mul_of_pos_right hcoefficient hqPos
  exact (roundedS_lt_six_L_mul_q_div hq hepsilon0 hepsilon1).trans
    ((div_lt_div_iff_of_pos_right hepsilon0).2 hnumerator)

/-- The unrounded target row scale is positive at positive distortion tolerance.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem M0_pos {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < M0 d q epsilon := by
  have hDqNat : 0 < Dq d q := by simp [Dq]
  have hDq : (0 : ℝ) < (Dq d q : ℕ) := by exact_mod_cast hDqNat
  rw [M0]
  exact div_pos (mul_pos (sq_pos_of_pos L_pos) hDq)
    (sq_pos_of_pos hepsilon)

/-- Rounded block size dominates its unrounded ceiling argument.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedB_lower (d q : ℕ) (epsilon : ℝ) :
    M0 d q epsilon / (roundedS q epsilon : ℝ) ≤
      (roundedB d q epsilon : ℝ) := by
  simpa [roundedB] using
    (Nat.le_ceil (M0 d q epsilon / (roundedS q epsilon : ℝ)))

/-- The first scale condition in line 1432: the rounded row count is at least `M0`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedM_lower
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    M0 d q epsilon ≤ (roundedM d q epsilon : ℝ) := by
  let s := roundedS q epsilon
  have hsNat : 0 < s := roundedS_pos hepsilon
  have hs : (0 : ℝ) < s := by exact_mod_cast hsNat
  have hb : M0 d q epsilon / (s : ℝ) ≤ (roundedB d q epsilon : ℝ) := by
    simpa [s] using roundedB_lower d q epsilon
  calc
    M0 d q epsilon = (s : ℝ) * (M0 d q epsilon / (s : ℝ)) := by
      field_simp
    _ ≤ (s : ℝ) * (roundedB d q epsilon : ℝ) :=
      mul_le_mul_of_nonneg_left hb hs.le
    _ = (roundedM d q epsilon : ℕ) := by simp [roundedM, s]

/-- The first scale condition in the literal form displayed in line 1432.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedM_scale_condition
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    L ^ 2 * (Dq d q : ℝ) / epsilon ^ 2 ≤
      (roundedM d q epsilon : ℝ) := by
  simpa [M0] using roundedM_lower (d := d) (q := q) hepsilon

/-- The exact ceiling estimate `m < M0 + s`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedM_lt_M0_add_s
    {d q : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (roundedM d q epsilon : ℝ) <
      M0 d q epsilon + roundedS q epsilon := by
  let s := roundedS q epsilon
  have hsNat : 0 < s := roundedS_pos hepsilon
  have hs : (0 : ℝ) < s := by exact_mod_cast hsNat
  have hquot : 0 ≤ M0 d q epsilon / (s : ℝ) := by
    exact (div_pos (M0_pos hepsilon) hs).le
  have hb : (roundedB d q epsilon : ℝ) <
      M0 d q epsilon / (s : ℝ) + 1 := by
    simpa [roundedB, s] using Nat.ceil_lt_add_one hquot
  calc
    (roundedM d q epsilon : ℝ) =
        (s : ℝ) * (roundedB d q epsilon : ℝ) := by simp [roundedM, s]
    _ < (s : ℝ) * (M0 d q epsilon / (s : ℝ) + 1) :=
      mul_lt_mul_of_pos_left hb hs
    _ = M0 d q epsilon + s := by field_simp

/-- A coarse comparison showing that the rounded sparsity is below `M0`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedS_lt_M0
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedS q epsilon : ℝ) < M0 d q epsilon := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hqDq : (q : ℝ) ≤ (Dq d q : ℕ) := by
    exact_mod_cast q_le_Dq d q
  have hsmall : 6 * (q : ℝ) * epsilon < L * (Dq d q : ℕ) := by
    calc
      6 * (q : ℝ) * epsilon ≤ 6 * (q : ℝ) := by
        simpa using mul_le_mul_of_nonneg_left hepsilon1
          (by positivity : (0 : ℝ) ≤ 6 * (q : ℝ))
      _ < L * (q : ℝ) := by
        exact mul_lt_mul_of_pos_right (by nlinarith [ninety_lt_L]) hqPos
      _ ≤ L * (Dq d q : ℕ) := mul_le_mul_of_nonneg_left hqDq L_pos.le
  have hcore : 6 * L * (q : ℝ) * epsilon <
      L ^ 2 * (Dq d q : ℕ) := by
    calc
      6 * L * (q : ℝ) * epsilon = L * (6 * (q : ℝ) * epsilon) := by ring
      _ < L * (L * (Dq d q : ℕ)) := mul_lt_mul_of_pos_left hsmall L_pos
      _ = L ^ 2 * (Dq d q : ℕ) := by ring
  have hscaled : 6 * L * (q : ℝ) / epsilon < M0 d q epsilon := by
    rw [M0]
    apply (div_lt_div_iff₀ hepsilon0 (sq_pos_of_pos hepsilon0)).2
    have hmul := mul_lt_mul_of_pos_right hcore hepsilon0
    nlinarith [sq_nonneg epsilon]
  exact (roundedS_lt_six_L_mul_q_div hq hepsilon0 hepsilon1).trans hscaled

/-- The main rounded parameters always have at least two rows per stack.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem two_le_roundedB
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    2 ≤ roundedB d q epsilon := by
  have hsNat : 0 < roundedS q epsilon := roundedS_pos hepsilon0
  have hs : (0 : ℝ) < roundedS q epsilon := by exact_mod_cast hsNat
  have hsM : (roundedS q epsilon : ℝ) < M0 d q epsilon :=
    roundedS_lt_M0 hq hepsilon0 hepsilon1
  have hratio : (1 : ℝ) < M0 d q epsilon / roundedS q epsilon := by
    apply (lt_div_iff₀ hs).2
    simpa using hsM
  have hbCast : (1 : ℝ) < roundedB d q epsilon :=
    hratio.trans_le (roundedB_lower d q epsilon)
  exact_mod_cast hbCast

/-- The main rounded block size is at least two under the stated parameter hypotheses.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem two_le_main_roundedB
    {d : ℕ} {delta epsilon : ℝ}
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    2 ≤ roundedB d (failureOrder d delta) epsilon :=
  two_le_roundedB (one_le_failureOrder d delta) hepsilon0 hepsilon1

/-- The paper's `m < 2 M0` rounding estimate.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedM_lt_two_M0
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedM d q epsilon : ℝ) < 2 * M0 d q epsilon := by
  have hm := roundedM_lt_M0_add_s (d := d) (q := q) hepsilon0
  have hs := roundedS_lt_M0 (d := d) hq hepsilon0 hepsilon1
  linarith

/-- The rounded row count is below three times the unrounded row scale.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedM_lt_three_M0
    {d q : ℕ} {epsilon : ℝ}
    (hq : 1 ≤ q) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedM d q epsilon : ℝ) < 3 * M0 d q epsilon := by
  exact (roundedM_lt_two_M0 hq hepsilon0 hepsilon1).trans
    (by nlinarith [M0_pos (d := d) (q := q) hepsilon0])

/-- The numerical upper bound for `3 M0` used in lines 1492--1498.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem three_M0_lt_306456
    {d q : ℕ} {epsilon : ℝ}
    (hd : 1 ≤ d) (hepsilon : 0 < epsilon) :
    3 * M0 d q epsilon <
      306456 * ((d : ℝ) + q) / epsilon ^ 2 := by
  have hDqNat : Dq d q ≤ 2 * (d + q) := Dq_le_two_mul_add hd
  have hDq : (Dq d q : ℝ) ≤ 2 * ((d : ℝ) + q) := by
    exact_mod_cast hDqNat
  have hDqPosNat : 0 < Dq d q := by simp [Dq]
  have hDqPos : (0 : ℝ) < (Dq d q : ℕ) := by exact_mod_cast hDqPosNat
  have hLsq : L ^ 2 < (226 : ℝ) ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self L_pos.le L_lt_226
  have hnum : 3 * (L ^ 2 * (Dq d q : ℕ)) <
      306456 * ((d : ℝ) + q) := by
    calc
      3 * (L ^ 2 * (Dq d q : ℕ)) <
          3 * ((226 : ℝ) ^ 2 * (Dq d q : ℕ)) := by
        exact mul_lt_mul_of_pos_left
          (mul_lt_mul_of_pos_right hLsq hDqPos) (by norm_num)
      _ ≤ 3 * ((226 : ℝ) ^ 2 * (2 * ((d : ℝ) + q))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hDq (by positivity)) (by norm_num)
      _ = 306456 * ((d : ℝ) + q) := by ring
  calc
    3 * M0 d q epsilon =
        (3 * (L ^ 2 * (Dq d q : ℕ))) / epsilon ^ 2 := by
      rw [M0]
      ring
    _ < (306456 * ((d : ℝ) + q)) / epsilon ^ 2 :=
      (div_lt_div_iff_of_pos_right (sq_pos_of_pos hepsilon)).2 hnum
    _ = 306456 * ((d : ℝ) + q) / epsilon ^ 2 := rfl

/-- Certified explicit row bound from line 1497.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem roundedM_lt_306456
    {d q : ℕ} {epsilon : ℝ}
    (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    (roundedM d q epsilon : ℝ) <
      306456 * ((d : ℝ) + q) / epsilon ^ 2 :=
  (roundedM_lt_three_M0 hq hepsilon0 hepsilon1).trans
    (three_M0_lt_306456 hd hepsilon0)

end PaperParameters

end NLAlib.SparseFock
