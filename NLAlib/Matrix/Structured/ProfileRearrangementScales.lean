import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.WellFounded
import Mathlib.Tactic

/-!
# Cutoff scales for finite profile rearrangement

The double-exponential cutoffs and their neighboring-set budgets used in
Latała--van Handel--Youssef 2018, Lemma 3.10. The indexing starts with the
previous cutoff `2` and main cutoff `4`.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

/-- Previous cutoff `2^(2^k)` in the profile rearrangement construction. -/
def profilePreviousCutoff (k : ℕ) : ℕ := 2 ^ (2 ^ k)

/-- Main cutoff `2^(2^(k+1))` in the profile rearrangement construction. -/
def profileCutoff (k : ℕ) : ℕ := 2 ^ (2 ^ (k + 1))

/-- Budget for a main cutoff and its neighboring entries. -/
def profileNeighborCutoff (k : ℕ) : ℕ :=
  profileCutoff k + profileCutoff k * profilePreviousCutoff k

/-- Every main cutoff is the square of its previous cutoff. -/
theorem profileCutoff_eq_previous_sq (k : ℕ) :
    profileCutoff k = profilePreviousCutoff k ^ 2 := by
  unfold profileCutoff profilePreviousCutoff
  rw [← pow_mul]
  congr 1

/-- Advancing the previous cutoff gives the current main cutoff. -/
@[simp] theorem profilePreviousCutoff_succ (k : ℕ) :
    profilePreviousCutoff (k + 1) = profileCutoff k := rfl

/-- Consecutive main cutoffs are related by squaring. -/
@[simp] theorem profileCutoff_succ (k : ℕ) :
    profileCutoff (k + 1) = profileCutoff k ^ 2 := by
  rw [profileCutoff_eq_previous_sq, profilePreviousCutoff_succ]

/-- Previous cutoffs are at least two. -/
theorem two_le_profilePreviousCutoff (k : ℕ) : 2 ≤ profilePreviousCutoff k := by
  exact (show 2 ^ 1 ≤ 2 ^ (2 ^ k) from
    Nat.pow_le_pow_right (by decide) (Nat.one_le_pow k 2 (by decide)))

/-- Main cutoffs are at least four. -/
theorem four_le_profileCutoff (k : ℕ) : 4 ≤ profileCutoff k := by
  rw [profileCutoff_eq_previous_sq]
  nlinarith [two_le_profilePreviousCutoff k]

/-- The previous cutoff never exceeds the main cutoff. -/
theorem profilePreviousCutoff_le (k : ℕ) : profilePreviousCutoff k ≤ profileCutoff k := by
  rw [profileCutoff_eq_previous_sq]
  nlinarith [two_le_profilePreviousCutoff k]

/-- Previous cutoffs increase monotonically. -/
theorem monotone_profilePreviousCutoff : Monotone profilePreviousCutoff := by
  intro i j hij
  exact Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hij)

/-- Main cutoffs increase strictly at every step. -/
theorem strictMono_profileCutoff : StrictMono profileCutoff := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [profileCutoff_succ]
  nlinarith [four_le_profileCutoff k]

/-- Main cutoffs increase monotonically. -/
theorem monotone_profileCutoff : Monotone profileCutoff := strictMono_profileCutoff.monotone

/-- The neighboring-entry budgets increase monotonically. -/
theorem monotone_profileNeighborCutoff : Monotone profileNeighborCutoff := by
  intro i j hij
  exact Nat.add_le_add (monotone_profileCutoff hij)
    (Nat.mul_le_mul (monotone_profileCutoff hij) (monotone_profilePreviousCutoff hij))

/-- The neighboring-entry budget contains its main cutoff. -/
theorem profileCutoff_le_neighborCutoff (k : ℕ) :
    profileCutoff k ≤ profileNeighborCutoff k := Nat.le_add_right _ _

/-- Exact adjacent-block budget: the neighboring set and the next previous
cutoff fit inside the next main cutoff. -/
theorem profileNeighborCutoff_add_previous_succ_le (k : ℕ) :
    profileNeighborCutoff k + profilePreviousCutoff (k + 1) ≤ profileCutoff (k + 1) := by
  have hbase : profilePreviousCutoff k + 2 ≤ profileCutoff k := by
    rw [profileCutoff_eq_previous_sq]
    nlinarith [two_le_profilePreviousCutoff k]
  have hmul := Nat.mul_le_mul_left (profileCutoff k) hbase
  rw [profilePreviousCutoff_succ, profileCutoff_succ, profileNeighborCutoff]
  nlinarith

/-- Each neighboring-entry budget lies strictly below the next main cutoff. -/
theorem profileNeighborCutoff_lt_cutoff_succ (k : ℕ) :
    profileNeighborCutoff k < profileCutoff (k + 1) := by
  have h := profileNeighborCutoff_add_previous_succ_le k
  have hp := two_le_profilePreviousCutoff (k + 1)
  omega

/-- Main cutoffs dominate their index, so every finite dimension is eventually
covered without an extra growth hypothesis. -/
theorem le_profileCutoff (k : ℕ) : k ≤ profileCutoff k := strictMono_profileCutoff.le_apply

/-- Every finite natural budget lies below some main cutoff. -/
theorem exists_le_profileCutoff (b : ℕ) : ∃ k, b ≤ profileCutoff k := ⟨b, le_profileCutoff b⟩

/-- Exact natural logarithm of a main cutoff, viewed as a real number. -/
theorem log_profileCutoff (k : ℕ) :
    Real.log (profileCutoff k : ℝ) = (2 : ℝ) ^ (k + 1) * Real.log 2 := by
  simp [profileCutoff, Real.log_pow]

/-- Previous cutoffs have strictly positive real square roots. -/
theorem sqrt_profilePreviousCutoff_pos (k : ℕ) :
    0 < Real.sqrt (profilePreviousCutoff k : ℝ) := by
  apply Real.sqrt_pos.2
  exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (two_le_profilePreviousCutoff k)

/-- The inverse square root of a previous cutoff is strictly positive. -/
theorem inv_sqrt_profilePreviousCutoff_pos (k : ℕ) :
    0 < (Real.sqrt (profilePreviousCutoff k : ℝ))⁻¹ :=
  inv_pos.mpr (sqrt_profilePreviousCutoff_pos k)

/-- The real square root of a main cutoff is exactly its previous cutoff. -/
theorem sqrt_profileCutoff_eq_previous (k : ℕ) :
    Real.sqrt (profileCutoff k : ℝ) = (profilePreviousCutoff k : ℝ) := by
  rw [profileCutoff_eq_previous_sq, Nat.cast_pow, Real.sqrt_sq (by positivity)]

end NLAlib
