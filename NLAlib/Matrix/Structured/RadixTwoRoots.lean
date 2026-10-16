import NLAlib.Matrix.Structured.RadixTwoFFT
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # The supplied roots for radix-two Fourier butterflies

The negative standard character gives a primitive root at every transform
length. Squaring moves to the next smaller length, and the half-length power
is minus one. Source: Golub–Van Loan, Matrix Computations, §1.4.
-/
noncomputable section
namespace NLAlib.RadixTwoFFT

/-- The exact root identities used by the recursive butterflies. -/
def HasRootSchedule : ℕ → ℂ → Prop
  | 0, _ => True
  | s + 1, ζ => ζ ^ size s = -1 ∧ HasRootSchedule s (ζ ^ 2)

/-- Every primitive root of power-of-two order supplies all butterfly roots. -/
theorem hasRootSchedule_of_isPrimitiveRoot (s : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (size s)) : HasRootSchedule s ζ := by
  induction s generalizing ζ with
  | zero => trivial
  | succ s ih =>
    have hpow : (ζ ^ size s) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_two]
      exact hζ.pow_eq_one
    have hne : ζ ^ size s ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (size_pos s).ne' (by
      change size s < size s + size s
      have hs := size_pos s
      omega)
    have hhalf : ζ ^ size s = -1 := (sq_eq_one_iff.mp hpow).resolve_left hne
    have hprod : size (s + 1) = 2 * size s := by simp only [size]; omega
    exact ⟨hhalf, ih (IsPrimitiveRoot.pow (size_pos (s + 1)) hζ hprod)⟩

/-- Powers of the supplied negative character root are exactly character values. -/
theorem standardRoot_pow {n : ℕ} [NeZero n] (k : ℕ) :
    ZMod.stdAddChar (-1 : ZMod n) ^ k = ZMod.stdAddChar (-(k : ZMod n)) := by
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul, mul_neg, mul_one]

/-- The negative standard character at one is a primitive root of the actual
transform length. No root property is assumed by the final transform theorem. -/
theorem isPrimitiveRoot_standardRoot {n : ℕ} [NeZero n] :
    IsPrimitiveRoot (ZMod.stdAddChar (-1 : ZMod n)) n := by
  constructor
  · rw [standardRoot_pow]
    simp
  · intro k hk
    have hchar : ZMod.stdAddChar (-(k : ZMod n)) = ZMod.stdAddChar (0 : ZMod n) := by
      rw [← standardRoot_pow, hk, AddChar.map_zero_eq_one]
    have hzero : (k : ZMod n) = 0 := neg_eq_zero.mp (ZMod.injective_stdAddChar hchar)
    exact (ZMod.natCast_eq_zero_iff k n).mp hzero

/-- The concrete roots used by the negative-exponent DFT satisfy every recursive
butterfly identity. Source: Golub–Van Loan, §1.4.
atlas: radix-two-fft-realization (partial) -/
theorem hasRootSchedule_standardRoot (s : ℕ) :
    HasRootSchedule s (ZMod.stdAddChar (-1 : ZMod (size s))) :=
  hasRootSchedule_of_isPrimitiveRoot s isPrimitiveRoot_standardRoot

end NLAlib.RadixTwoFFT
