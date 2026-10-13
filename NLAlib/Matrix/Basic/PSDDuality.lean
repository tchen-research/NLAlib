import Mathlib.Analysis.Matrix.Order

/-!
# Self-duality of the positive semidefinite cone

The trace pairing detects positive semidefiniteness and has a precise zero
case on two positive semidefinite matrices. All results hold for real or
complex matrices, including empty dimensions.
Source: Horn--Johnson (2013), Theorem 7.5.4. Atlas: `psd-cone-self-dual`.
-/

noncomputable section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace NLAlib

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

omit [DecidableEq n] in
/-- For a Hermitian second argument, the trace pairing is the entrywise
Hermitian pairing. Horn--Johnson (2013), Theorem 7.5.4;
helper for `psd-cone-self-dual`. -/
theorem trace_mul_eq_sum_mul_star {A B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    (A * B).trace = ∑ i, ∑ j, A i j * star (B i j) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hB.apply i j, star_star]

/-- The trace pairing of two PSD matrices is the trace of a Gram matrix
formed from their square roots. Horn--Johnson (2013), Theorem 7.5.4;
helper for `psd-cone-self-dual`. -/
theorem trace_mul_eq_trace_sqrt_conjTranspose_mul {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace =
      ((CFC.sqrt A * CFC.sqrt B)ᴴ * (CFC.sqrt A * CFC.sqrt B)).trace := by
  have hSA := (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have hSB := (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hAA := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hBB := CFC.sqrt_mul_sqrt_self B hB.nonneg
  symm
  calc
    _ = (CFC.sqrt B * A * CFC.sqrt B).trace := by
      rw [conjTranspose_mul, hSA, hSB]
      rw [Matrix.mul_assoc (CFC.sqrt B) (CFC.sqrt A),
        ← Matrix.mul_assoc (CFC.sqrt A), hAA, ← Matrix.mul_assoc]
    _ = (B * A).trace := by
      rw [trace_mul_cycle, hBB]
    _ = (A * B).trace := trace_mul_comm _ _

/-- The trace of the product of PSD matrices is nonnegative, and therefore
real for complex matrices. Horn--Johnson (2013), Theorem 7.5.4.
atlas: psd-cone-self-dual (partial) -/
theorem trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  rw [trace_mul_eq_trace_sqrt_conjTranspose_mul hA hB]
  exact (posSemidef_conjTranspose_mul_self _).trace_nonneg

/-- For PSD matrices the trace pairing vanishes exactly when their product
vanishes. Horn--Johnson (2013), Theorem 7.5.4.
atlas: psd-cone-self-dual (partial) -/
theorem trace_mul_eq_zero_iff_of_posSemidef {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A * B).trace = 0 ↔ A * B = 0 := by
  constructor
  · intro h
    rw [trace_mul_eq_trace_sqrt_conjTranspose_mul hA hB,
      trace_conjTranspose_mul_self_eq_zero_iff] at h
    calc
      A * B = CFC.sqrt A * (CFC.sqrt A * CFC.sqrt B) * CFC.sqrt B := by
        simp only [← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self A hA.nonneg,
          Matrix.mul_assoc A, CFC.sqrt_mul_sqrt_self B hB.nonneg]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    rw [h, trace_zero]

/-- A Hermitian matrix is PSD precisely when its trace pairing with every
PSD matrix is nonnegative. Horn--Johnson (2013), Theorem 7.5.4.
atlas: psd-cone-self-dual (partial) -/
theorem posSemidef_iff_trace_mul_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ B : Matrix n n 𝕜, B.PosSemidef → 0 ≤ (A * B).trace := by
  constructor
  · exact fun hA B hB => trace_mul_nonneg_of_posSemidef hA hB
  · intro h
    apply PosSemidef.of_dotProduct_mulVec_nonneg hA
    intro x
    have hx := h (vecMulVec x (star x)) (posSemidef_vecMulVec_self_star x)
    simpa only [mul_vecMulVec, trace_vecMulVec, dotProduct_comm] using hx

/-- Multiplication in the trace pairing by a PSD matrix preserves Loewner
order. Horn--Johnson (2013), Theorem 7.5.4.
atlas: psd-cone-self-dual (partial) -/
theorem trace_mul_le_trace_mul_of_posSemidef {A B C : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hBC : B ≤ C) : (A * B).trace ≤ (A * C).trace := by
  have h := trace_mul_nonneg_of_posSemidef hA (Matrix.le_iff.mp hBC)
  simpa only [Matrix.mul_sub, trace_sub, sub_nonneg] using h

/-- The PSD cone is self-dual under the trace pairing; the pairing vanishes
exactly on zero products and is monotone in either PSD argument.
Horn--Johnson (2013), Theorem 7.5.4.
atlas: psd-cone-self-dual -/
theorem psd_trace_pairing_characterizations {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (A.PosSemidef ↔ ∀ B : Matrix n n 𝕜, B.PosSemidef → 0 ≤ (A * B).trace) ∧
    (∀ B : Matrix n n 𝕜, A.PosSemidef → B.PosSemidef →
      ((A * B).trace = 0 ↔ A * B = 0)) ∧
    (∀ B C : Matrix n n 𝕜, A.PosSemidef → B ≤ C →
      (A * B).trace ≤ (A * C).trace) :=
  ⟨posSemidef_iff_trace_mul_nonneg hA,
    fun _ hA hB => trace_mul_eq_zero_iff_of_posSemidef hA hB,
    fun _ _ hA hBC => trace_mul_le_trace_mul_of_posSemidef hA hBC⟩

end NLAlib
