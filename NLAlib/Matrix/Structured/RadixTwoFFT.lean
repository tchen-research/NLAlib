import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # The radix-two butterfly algorithm and its arithmetic costs

The recursion splits input into its actual even and odd coordinates. Each
butterfly shares one supplied-twiddle multiplication between one addition
and one subtraction. Splits, permutations, and supplied constants are free
in this arithmetic model. Costs are accumulated from the recursive calls
and the actual butterfly nodes, rather than assumed as a recurrence.
Source: Golub–Van Loan, Matrix Computations, §1.4.
-/
noncomputable section
open Finset
namespace NLAlib.RadixTwoFFT

/-- Recursive transform length, definitionally doubled at each stage. -/
def size : ℕ → ℕ
  | 0 => 1
  | s + 1 => size s + size s

/-- The recursive length is exactly `2^s`. -/
theorem size_eq_two_pow (s : ℕ) : size s = 2 ^ s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [size, ih, Nat.pow_succ]; omega

/-- Every transform length is positive, including the scalar stage. -/
theorem size_pos (s : ℕ) : 0 < size s := by rw [size_eq_two_pow]; positivity

/-- A transform length is never zero. -/
instance instNeZeroSize (s : ℕ) : NeZero (size s) := ⟨(size_pos s).ne'⟩

/-- Position of an even-indexed input coordinate in a doubled vector. -/
def evenIndex {N : ℕ} (j : Fin N) : Fin (N + N) := ⟨2 * j.val, by omega⟩

/-- Position of an odd-indexed input coordinate in a doubled vector. -/
def oddIndex {N : ℕ} (j : Fin N) : Fin (N + N) := ⟨2 * j.val + 1, by omega⟩

/-- A value accompanied by the number of complex supplied-constant
multiplications and complex additions/subtractions used to construct it. -/
structure ArithmeticResult (α : Type*) where
  /-- The computed mathematical value. -/
  value : α
  /-- Count of complex supplied-constant multiplications. -/
  mulCount : ℕ
  /-- Count of complex additions and subtractions. -/
  addCount : ℕ

/-- One shared butterfly: one twiddle multiplication, one sum, one difference. -/
def butterfly (twiddle a b : ℂ) : ArithmeticResult (ℂ × ℂ) :=
  let t := twiddle * b
  ⟨(a + t, a - t), 1, 2⟩

/-- Literal radix-two even/odd recursion with supplied powers of the root.
At length one it returns the input with no arithmetic operations. -/
def run : (s : ℕ) → ℂ → (Fin (size s) → ℂ) → ArithmeticResult (Fin (size s) → ℂ)
  | 0, _, x => ⟨x, 0, 0⟩
  | s + 1, ζ, x =>
    let e := run s (ζ ^ 2) (fun j => x (evenIndex j))
    let o := run s (ζ ^ 2) (fun j => x (oddIndex j))
    let b : Fin (size s) → ArithmeticResult (ℂ × ℂ) :=
      fun k => butterfly (ζ ^ k.val) (e.value k) (o.value k)
    ⟨Fin.addCases (fun k => (b k).value.1) (fun k => (b k).value.2),
      e.mulCount + o.mulCount + ∑ k, (b k).mulCount,
      e.addCount + o.addCount + ∑ k, (b k).addCount⟩

/-- The length-one transform is the identity with zero arithmetic costs.
atlas: radix-two-fft-realization (partial) -/
theorem run_zero (ζ : ℂ) (x : Fin (size 0) → ℂ) :
    (run 0 ζ x).value = x ∧ (run 0 ζ x).mulCount = 0 ∧ (run 0 ζ x).addCount = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Multiplication cost is the sum of the two recursive costs and one
supplied-twiddle multiplication for each actual butterfly. -/
theorem run_mulCount_succ (s : ℕ) (ζ : ℂ) (x : Fin (size (s + 1)) → ℂ) :
    (run (s + 1) ζ x).mulCount =
      (run s (ζ ^ 2) (fun j => x (evenIndex j))).mulCount +
      (run s (ζ ^ 2) (fun j => x (oddIndex j))).mulCount + size s := by
  simp only [run, butterfly, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]

/-- Addition/subtraction cost is accumulated from the two recursive calls
and the two arithmetic operations in each actual butterfly. -/
theorem run_addCount_succ (s : ℕ) (ζ : ℂ) (x : Fin (size (s + 1)) → ℂ) :
    (run (s + 1) ζ x).addCount =
      (run s (ζ ^ 2) (fun j => x (evenIndex j))).addCount +
      (run s (ζ ^ 2) (fun j => x (oddIndex j))).addCount + 2 * size s := by
  simp only [run, butterfly, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, mul_comm]

/-- The actual recursion uses exactly `s 2^(s-1)` complex constant multiplications
at every positive stage; length one uses zero.
Source: Golub–Van Loan, §1.4.
atlas: radix-two-fft-realization (partial) -/
theorem run_mulCount_succ_eq (s : ℕ) (ζ : ℂ) (x : Fin (size (s + 1)) → ℂ) :
    (run (s + 1) ζ x).mulCount = (s + 1) * 2 ^ s := by
  induction s generalizing ζ with
  | zero => norm_num [run, butterfly, size]
  | succ s ih =>
    rw [run_mulCount_succ, ih, ih, size_eq_two_pow, Nat.pow_succ]
    ring

/-- The actual recursion uses exactly `s 2^s` complex additions/subtractions.
Source: Golub–Van Loan, §1.4.
atlas: radix-two-fft-realization (partial) -/
theorem run_addCount_eq (s : ℕ) (ζ : ℂ) (x : Fin (size s) → ℂ) :
    (run s ζ x).addCount = s * 2 ^ s := by
  induction s generalizing ζ with
  | zero => simp [run]
  | succ s ih =>
    rw [run_addCount_succ, ih, ih, size_eq_two_pow, Nat.pow_succ]
    ring

end NLAlib.RadixTwoFFT
