/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.SparseParameterConstants

set_option autoImplicit false

/-!
# Sparse failure-moment order

The explicit logarithmic failure order and its exponential probability bounds.
Ported from `SparseFockFormal.PaperParameters` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock

namespace PaperParameters

/-- The chosen failure-moment order is at least one.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem one_le_failureOrder (d : ℕ) (delta : ℝ) :
    1 ≤ failureOrder d delta := by
  exact Nat.le_max_left _ _

/-- The chosen failure-moment order dominates the base-two dimension-to-failure logarithm.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem log2_ratio_le_failureOrder (d : ℕ) (delta : ℝ) :
    Real.logb 2 ((d : ℝ) / delta) ≤ (failureOrder d delta : ℝ) := by
  calc
    Real.logb 2 ((d : ℝ) / delta) ≤
        (⌈Real.logb 2 ((d : ℝ) / delta)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (failureOrder d delta : ℕ) := by
      exact_mod_cast Nat.le_max_right 1 ⌈Real.logb 2 ((d : ℝ) / delta)⌉₊

/-- The base-two ceiling gives `d/delta ≤ 2^q`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ratio_le_two_pow_failureOrder
    {d : ℕ} {delta : ℝ} (hd : 1 ≤ d) (hdelta : 0 < delta) :
    (d : ℝ) / delta ≤ (2 : ℝ) ^ failureOrder d delta := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast Nat.zero_lt_of_lt hd
  have hratio : 0 < (d : ℝ) / delta := div_pos hdReal hdelta
  have hlog := log2_ratio_le_failureOrder d delta
  have hrpow :=
    (Real.logb_le_iff_le_rpow (b := (2 : ℝ)) (by norm_num) hratio).mp hlog
  simpa [Real.rpow_natCast] using hrpow

/-- Equivalently, `2⁻q ≤ delta/d`.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem half_pow_failureOrder_le
    {d : ℕ} {delta : ℝ} (hd : 1 ≤ d) (hdelta : 0 < delta) :
    ((1 : ℝ) / 2) ^ failureOrder d delta ≤ delta / d := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast Nat.zero_lt_of_lt hd
  have hratio : 0 < (d : ℝ) / delta := div_pos hdReal hdelta
  have hinv := one_div_le_one_div_of_le hratio
    (ratio_le_two_pow_failureOrder hd hdelta)
  calc
    ((1 : ℝ) / 2) ^ failureOrder d delta =
        1 / ((2 : ℝ) ^ failureOrder d delta) := by
      rw [one_div_pow]
    _ ≤ 1 / ((d : ℝ) / delta) := hinv
    _ = delta / d := by field_simp

/-- The failure-order arithmetic in lines 1457--1464.

Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem four_pow_failureOrder_le
    {d : ℕ} {delta : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (d : ℝ) * ((1 : ℝ) / 4) ^ failureOrder d delta ≤ delta := by
  let q := failureOrder d delta
  have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdPos : (0 : ℝ) < d := zero_lt_one.trans_le hdReal
  have hhalf : ((1 : ℝ) / 2) ^ q ≤ delta / d := by
    simpa [q] using half_pow_failureOrder_le hd hdelta0
  have hhalf0 : 0 ≤ ((1 : ℝ) / 2) ^ q := by positivity
  have hsq : (((1 : ℝ) / 2) ^ q) ^ 2 ≤ (delta / d) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hhalf0 hhalf
  have hfour : ((1 : ℝ) / 4) ^ q = (((1 : ℝ) / 2) ^ q) ^ 2 := by
    rw [show ((1 : ℝ) / 4) = ((1 : ℝ) / 2) * ((1 : ℝ) / 2) by norm_num]
    simp [mul_pow, pow_two]
  have hfirst : (d : ℝ) * ((1 : ℝ) / 4) ^ q ≤ delta ^ 2 / d := by
    rw [hfour]
    calc
      (d : ℝ) * (((1 : ℝ) / 2) ^ q) ^ 2 ≤
          (d : ℝ) * (delta / d) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hdPos.le
      _ = delta ^ 2 / d := by field_simp
  have hdeltaD : delta ≤ (d : ℝ) := hdelta1.trans hdReal
  have hmul : delta * delta ≤ delta * (d : ℝ) :=
    mul_le_mul_of_nonneg_left hdeltaD hdelta0.le
  have hsecond : delta ^ 2 / (d : ℝ) ≤ delta := by
    apply (div_le_iff₀ hdPos).2
    simpa [pow_two] using hmul
  exact hfirst.trans hsecond

/-- The auxiliary natural dimension parameter casts to its explicit real formula.
Source: ported from `SparseFockFormal.PaperParameters`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem cast_Dq (d q : ℕ) :
    (Dq d q : ℝ) = (d : ℝ) + 2 * (q : ℝ) + 1 := by
  simp [Dq]

end PaperParameters

end NLAlib.SparseFock
