import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Elementary factorial inequalities for finite moment budgets

The central binomial estimate and the first-factor refinement of `n! ≤ n^n`
give geometric envelopes without Stirling's formula.
Atlas: `khatri-rao-sharp-growth`.
-/

namespace NLAlib

/-- The central binomial coefficient bounds the doubled factorial.
Source: the binomial sum at one. Atlas: `khatri-rao-sharp-growth`. -/
theorem factorial_two_mul_le_four_pow_mul_factorial_sq (n : ℕ) :
    (2 * n).factorial ≤ 4 ^ n * n.factorial ^ 2 := by
  have he : (2 * n).choose n * n.factorial * n.factorial = (2 * n).factorial := by
    simpa only [show 2 * n - n = n by omega] using
      Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [← he]
  have hpow : 2 ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  have h := Nat.mul_le_mul_right (n.factorial ^ 2) (Nat.choose_le_two_pow (2 * n) n)
  simpa only [hpow, pow_two, mul_assoc] using h

/-- Keeping the initial unit factor saves one power in an elementary factorial bound.
Source: comparison of each remaining factor with `n+1`.
Atlas: `khatri-rao-sharp-growth`. -/
theorem factorial_le_succ_pow_pred (n : ℕ) : n.factorial ≤ (n + 1) ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · simp [hn]
    have hn1 : 1 ≤ n := by omega
    rw [Nat.factorial_succ]
    calc
      (n + 1) * n.factorial ≤ (n + 1) * (n + 1) ^ (n - 1) := Nat.mul_le_mul_left _ ih
      _ = (n + 1) ^ n := by rw [← pow_succ']; congr 1; omega
      _ ≤ (n + 1 + 1) ^ (n + 1 - 1) := by
        simpa using Nat.pow_le_pow_left (show n + 1 ≤ n + 1 + 1 by omega) n

/-- A direction-preserving radial budget fits a factorial envelope with explicit
geometric constants. Source: elementary factorial and binomial comparisons.
Atlas: `khatri-rao-sharp-growth`. -/
theorem factorial_radial_coefficient_le {r p d : ℕ} (hr : 1 ≤ r) (hp : 2 ≤ p) (hd : 2 ≤ d) :
    2 * 4 ^ d * 2 ^ ((p - 1) * (d - 1)) * (p - 1).factorial ^ (d - 1) *
        (r + 4 * p) ^ (p - 1) ≤
      p.factorial * 2 ^ (3 * d + 4) * r *
        (2 ^ (d - 1) * p ^ (d - 2) * (r + 4 * p)) ^ (p - 2) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  simp only [Nat.add_sub_cancel_left]
  let F := (k + 1).factorial
  let S := r + 4 * (k + 2)
  let C := 2 ^ (e + 1)
  let L := 2 * 4 ^ (e + 2) * C
  have hf : F ≤ (k + 2) ^ k := by
    simpa only [Nat.add_sub_cancel, Nat.add_assoc] using factorial_le_succ_pow_pred (k + 1)
  have hfp : F ^ e ≤ ((k + 2) ^ e) ^ k := by
    simpa only [← pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hf e
  have hS : S ≤ 5 * r * (k + 2) := by
    dsimp [S]
    nlinarith
  have hL : 2 ^ (3 * (e + 2) + 4) = 16 * L := by
    dsimp [L, C]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    change 2 ^ (3 * (e + 2) + 4) = 2 ^ 4 * (2 ^ 1 * 2 ^ (2 * (e + 2)) * 2 ^ (e + 1))
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have hco : L * S ≤ (k + 2) * (16 * L) * r := by
    have h := Nat.mul_le_mul_left L hS
    nlinarith
  have he1 :
      2 * 4 ^ (e + 2) * 2 ^ ((k + 1) * (e + 1)) * F ^ (e + 1) * S ^ (k + 1) =
        L * F * S * (C ^ k * F ^ e * S ^ k) := by
    rw [show (k + 1) * (e + 1) = (e + 1) * (k + 1) by ring, pow_mul, pow_succ,
      pow_succ, pow_succ]
    dsimp [L, C]
    ring
  have he2 :
      (k + 2).factorial * 2 ^ (3 * (e + 2) + 4) * r *
          (C * (k + 2) ^ e * S) ^ k =
        (k + 2) * (16 * L) * r * F *
          (C ^ k * ((k + 2) ^ e) ^ k * S ^ k) := by
    rw [Nat.factorial_succ, hL, mul_pow, mul_pow]
    dsimp [F]
    ring
  have h1 := Nat.mul_le_mul_left (L * F * S)
    (Nat.mul_le_mul_right (S ^ k) (Nat.mul_le_mul_left (C ^ k) hfp))
  have h2 := Nat.mul_le_mul_right (F * (C ^ k * ((k + 2) ^ e) ^ k * S ^ k)) hco
  have hfinal :
      2 * 4 ^ (e + 2) * 2 ^ ((k + 1) * (e + 1)) * F ^ (e + 1) * S ^ (k + 1) ≤
        (k + 2).factorial * 2 ^ (3 * (e + 2) + 4) * r *
          (C * (k + 2) ^ e * S) ^ k := by
    rw [he1, he2]
    nlinarith
  simpa only [F, C, S,
    show 2 + e = e + 2 by omega, show 2 + k = k + 2 by omega,
    show e + 2 - 1 = e + 1 by omega, show k + 2 - 1 = k + 1 by omega] using hfinal

end NLAlib
