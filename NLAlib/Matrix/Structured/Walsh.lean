/-
Copyright (c) 2026 Diar Heidary.

Ported and adapted from Rerandomized-Subsampled-Trigonometric-Transforms,
SRHT/Walsh.lean, commit 929653a019eb4910fc6efb9cb34cc3c3c2f949d4.

MIT License

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Concrete normalized Walsh–Hadamard matrices

The actual transform on `(ZMod 2)^b` has order `2^b`, constant-magnitude
entries and orthonormal rows and columns. Only Walsh algebra is ported;
the classical one-sign SRHT law is constructed separately.
Source: operator re-derivation `sh:srht`; supports atlas `srht-ose`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix
namespace NLAlib

/-- The binary group indexing a Walsh matrix of order `2^b`.
Source: operator re-derivation `sh:srht`. -/
abbrev WalshIndex (b : ℕ) := Fin b → ZMod 2

/-- The Walsh row and column index set has `2^b` elements.
Source: operator re-derivation `sh:srht`. -/
@[simp] theorem card_walshIndex (b : ℕ) : Fintype.card (WalshIndex b) = 2 ^ b := by
  simp [WalshIndex]

/-- The real sign associated to one binary bit.
Source: Walsh character construction; supports `srht-ose`. -/
def walshBitSign (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- Addition of bits multiplies their real signs.
Source: Walsh character construction; supports `srht-ose`. -/
theorem walshBitSign_add (a b : ZMod 2) :
    walshBitSign (a + b) = walshBitSign a * walshBitSign b := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl <;>
    simp [walshBitSign, hone]

/-- Every bit sign has squared value one.
Source: Walsh character construction; supports `srht-ose`. -/
@[simp] theorem walshBitSign_sq (a : ZMod 2) : walshBitSign a ^ 2 = 1 := by
  unfold walshBitSign
  split_ifs <;> norm_num

/-- Summing a Walsh bit character vanishes unless its frequency is zero.
Source: Walsh character orthogonality; supports `srht-ose`. -/
theorem sum_walshBitSign_mul (a : ZMod 2) :
    (∑ b : ZMod 2, walshBitSign (a * b)) = if a = 0 then 2 else 0 := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc a with rfl | rfl
  · simp [walshBitSign]
  · rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    norm_num [walshBitSign]

/-- The actual unnormalized real Walsh character.
Source: operator re-derivation `sh:srht`. -/
def walshCharacter {b : ℕ} (a c : WalshIndex b) : ℝ :=
  ∏ i, walshBitSign (a i * c i)

/-- Walsh characters are symmetric in the row and column labels.
Source: Walsh construction; supports `srht-ose`. -/
theorem walshCharacter_comm {b : ℕ} (a c : WalshIndex b) :
    walshCharacter a c = walshCharacter c a := by simp [walshCharacter, mul_comm]

/-- Addition of row labels multiplies Walsh characters.
Source: Walsh construction; supports `srht-ose`. -/
theorem walshCharacter_add_left {b : ℕ} (a c z : WalshIndex b) :
    walshCharacter (a + c) z = walshCharacter a z * walshCharacter c z := by
  simp only [walshCharacter, Pi.add_apply, add_mul, walshBitSign_add, Finset.prod_mul_distrib]

/-- Every Walsh character has squared value one.
Source: Walsh construction; supports `srht-ose`. -/
@[simp] theorem walshCharacter_sq {b : ℕ} (a c : WalshIndex b) : walshCharacter a c ^ 2 = 1 := by
  simp [walshCharacter, ← Finset.prod_pow]

/-- Binary-vector addition is zero precisely when its two inputs agree.
Source: Walsh character orthogonality; supports `srht-ose`. -/
theorem walshIndex_add_eq_zero_iff {b : ℕ} (a c : WalshIndex b) : a + c = 0 ↔ a = c := by
  have hc : ∀ z : WalshIndex b, z + z = 0 := by
    intro z
    ext i
    exact CharTwo.add_self_eq_zero (z i)
  constructor
  · intro h
    have hh := congrArg (fun z : WalshIndex b => z + c) h
    simpa only [add_assoc, hc, add_zero, zero_add] using hh
  · rintro rfl
    exact hc a

/-- The sum of a Walsh character is zero at every nonzero frequency.
Source: Walsh character orthogonality; supports `srht-ose`. -/
theorem sum_walshCharacter {b : ℕ} (a : WalshIndex b) :
    (∑ c, walshCharacter a c) = if a = 0 then (Fintype.card (WalshIndex b) : ℝ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, walshCharacter, walshBitSign]
  · rw [if_neg ha]
    unfold walshCharacter
    rw [← Fintype.prod_sum (fun i : Fin b => fun c : ZMod 2 => walshBitSign (a i * c))]
    simp_rw [sum_walshBitSign_mul]
    have hex : ∃ i, a i ≠ 0 := by
      by_contra hh
      push Not at hh
      exact ha (funext hh)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Distinct Walsh characters are orthogonal over the binary group.
Source: Walsh construction; supports `srht-ose`. -/
theorem sum_mul_walshCharacter {b : ℕ} (a c : WalshIndex b) :
    (∑ z, walshCharacter a z * walshCharacter c z) =
      if a = c then (Fintype.card (WalshIndex b) : ℝ) else 0 := by
  simp_rw [← walshCharacter_add_left]
  rw [sum_walshCharacter]
  simp only [walshIndex_add_eq_zero_iff]

/-- The actual normalized symmetric Walsh–Hadamard matrix.
Source: operator re-derivation `sh:srht`. -/
def walshMatrix (b : ℕ) : Matrix (WalshIndex b) (WalshIndex b) ℝ := fun a c =>
  (Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ * walshCharacter a c

/-- The normalized Walsh matrix is symmetric.
Source: Walsh construction; supports `srht-ose`. -/
@[simp] theorem walshMatrix_transpose (b : ℕ) : (walshMatrix b)ᵀ = walshMatrix b := by
  ext a c
  exact congrArg ((Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ * ·) (walshCharacter_comm c a)

/-- The normalized Walsh matrix is an involution.
Source: Walsh orthogonality; supports `srht-ose`. -/
theorem walshMatrix_mul_self (b : ℕ) : walshMatrix b * walshMatrix b = 1 := by
  classical
  have hn : (0 : ℝ) < Fintype.card (WalshIndex b) := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card (WalshIndex b) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  ext a c
  simp only [Matrix.mul_apply, walshMatrix, Matrix.one_apply]
  have hsum : (∑ z,
      (Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ * walshCharacter a z *
        ((Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ * walshCharacter z c)) =
      (Real.sqrt (Fintype.card (WalshIndex b) : ℝ))⁻¹ ^ 2 *
        ∑ z, walshCharacter a z * walshCharacter c z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [walshCharacter_comm z c]
    ring
  rw [hsum, sum_mul_walshCharacter]
  split_ifs
  · have hs2 := Real.sq_sqrt hn.le
    field_simp
    exact hs2.symm
  · simp

/-- The actual normalized Walsh matrix has orthonormal columns.
Source: operator re-derivation `sh:srht`. -/
@[simp] theorem walshMatrix_transpose_mul_self (b : ℕ) : (walshMatrix b)ᵀ * walshMatrix b = 1 := by
  rw [walshMatrix_transpose, walshMatrix_mul_self]

/-- Every normalized Walsh entry has squared magnitude `1/2^b`.
Source: operator re-derivation `sh:srht`; the literal flatness hypothesis. -/
theorem walshMatrix_apply_sq (b : ℕ) (a c : WalshIndex b) :
    walshMatrix b a c ^ 2 = 1 / (2 ^ b : ℝ) := by
  rw [walshMatrix, mul_pow, walshCharacter_sq, mul_one, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), card_walshIndex]
  simp

end NLAlib
