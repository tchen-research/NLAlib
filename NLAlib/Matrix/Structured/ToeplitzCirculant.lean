import NLAlib.Matrix.Structured.StructuredMatrices
import NLAlib.Matrix.Structured.FourierSolve

/-! # Rectangular Toeplitz matrices as cropped circulants

The first column uses the negative Toeplitz diagonals at its beginning and the
positive diagonals at its end. The padding inequality proves that they do not
overlap. All coordinate maps are actual zero-extension/cropping matrices.
Source: Meyer, §5.5, convolution theorem (5.5.37) and Exercises 5.5.22, 5.5.25.
-/
noncomputable section
open scoped Matrix
namespace NLAlib

/-- The first column of the padded circulant, for the convention `Tᵢⱼ = t(j-i)`. -/
def toeplitzCirculantColumn (m n L : ℕ) (t : ℤ → ℂ) (k : ZMod L) : ℂ :=
  if k.val < m then t (-(k.val : ℤ))
  else if L - k.val < n then t ((L - k.val : ℕ) : ℤ) else 0

/-- Crop a cyclic vector to its first `m` coordinates. -/
def cyclicCropMatrix (m L : ℕ) : Matrix (Fin m) (ZMod L) ℂ :=
  fun i k => if k = (i.val : ZMod L) then 1 else 0

/-- Extend an `n`-vector by zeros in cyclic coordinates. -/
def cyclicPadMatrix (n L : ℕ) : Matrix (ZMod L) (Fin n) ℂ :=
  fun k j => if k = (j.val : ZMod L) then 1 else 0

/-- Cropping evaluates the input at precisely the retained residues. -/
theorem cyclicCropMatrix_mulVec {m L : ℕ} [NeZero L] (x : ZMod L → ℂ) (i : Fin m) :
    (cyclicCropMatrix m L *ᵥ x) i = x (i.val : ZMod L) := by
  simp [Matrix.mulVec, dotProduct, cyclicCropMatrix]

/-- A padded column is the corresponding coordinate unit vector. -/
theorem cyclicPadMatrix_apply {n L : ℕ} (j : Fin n) (k : ZMod L) :
    cyclicPadMatrix n L k j = if k = (j.val : ZMod L) then 1 else 0 := rfl

/-- The padding matrix is literal zero extension in the canonical cyclic labels. -/
theorem cyclicPadMatrix_mulVec {n L : ℕ} [NeZero L] (hnL : n ≤ L)
    (x : Fin n → ℂ) (k : ZMod L) :
    (cyclicPadMatrix n L *ᵥ x) k = if h : k.val < n then x ⟨k.val, h⟩ else 0 := by
  classical
  by_cases hk : k.val < n
  · rw [dif_pos hk]
    change (∑ j : Fin n, (if k = (j.val : ZMod L) then 1 else 0) * x j) = _
    rw [Finset.sum_eq_single (⟨k.val, hk⟩ : Fin n)]
    · simp only [ZMod.natCast_zmod_val, if_true, one_mul]
    · intro j _ hj
      have he : k ≠ (j.val : ZMod L) := by
        intro he
        have hv := congrArg ZMod.val he
        rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le j.isLt hnL)] at hv
        exact hj (Fin.ext hv.symm)
      simp only [if_neg he, zero_mul]
    · simp
  · rw [dif_neg hk]
    change (∑ j : Fin n, (if k = (j.val : ZMod L) then 1 else 0) * x j) = 0
    apply Finset.sum_eq_zero
    intro j _
    have he : k ≠ (j.val : ZMod L) := by
      intro he
      have hv := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le j.isLt hnL)] at hv
      exact hk (hv ▸ j.isLt)
    simp only [if_neg he, zero_mul]

private theorem residue_difference_val {L : ℕ} [NeZero L] {i j : ℕ}
    (hi : i < L) (hj : j < L) (hij : i < j) :
    ((i : ZMod L) - (j : ZMod L)).val = L - (j - i) := by
  have hp : ((j : ZMod L) - (i : ZMod L)).val = j - i := by
    simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using
      (ZMod.val_sub (a := (j : ZMod L)) (b := (i : ZMod L)) (by
        simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hij.le))
  have hn : (j : ZMod L) - (i : ZMod L) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [hp, ZMod.val_zero] at hv
    omega
  rw [show (i : ZMod L) - (j : ZMod L) = -((j : ZMod L) - (i : ZMod L)) by ring,
    ZMod.neg_val, if_neg hn, hp]

/-- The padded circulant has exactly the original Toeplitz entries on the
retained rectangle; the padding condition is proved sufficient entrywise. -/
theorem toeplitzCirculantColumn_sub {m n L : ℕ} [NeZero L]
    (hm : 0 < m) (hn : 0 < n) (hL : m + n - 1 ≤ L)
    (t : ℤ → ℂ) (i : Fin m) (j : Fin n) :
    toeplitzCirculantColumn m n L t ((i.val : ZMod L) - (j.val : ZMod L)) =
      t ((j.val : ℤ) - (i.val : ℤ)) := by
  have hi : i.val < L := by have := i.isLt; omega
  have hj : j.val < L := by have := j.isLt; omega
  by_cases hij : j.val ≤ i.val
  · have hv : ((i.val : ZMod L) - (j.val : ZMod L)).val = i.val - j.val := by
      simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using
        (ZMod.val_sub (a := (i.val : ZMod L)) (b := (j.val : ZMod L)) (by
          simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hij))
    have hfirst : i.val - j.val < m := by have := i.isLt; omega
    rw [toeplitzCirculantColumn, hv, if_pos hfirst, Int.natCast_sub hij]
    congr 1
    ring
  · have hij' : i.val < j.val := by omega
    have hv := residue_difference_val hi hj hij'
    have hfirst : ¬ L - (j.val - i.val) < m := by have := j.isLt; omega
    have hsecond : L - (L - (j.val - i.val)) < n := by have := j.isLt; omega
    rw [toeplitzCirculantColumn, hv, if_neg hfirst, if_pos hsecond]
    congr 1
    rw [Nat.sub_sub_self (by omega : j.val - i.val ≤ L), Int.natCast_sub hij'.le]

/-- Exact rectangular Toeplitz/circulant factorization, including every
sufficient padding length and dimensions one.
Source: Meyer, §5.5, Exercises 5.5.22, 5.5.25.
atlas: toeplitz-circulant-fft-product (partial) -/
theorem toeplitzMatrix_eq_crop_circulant_pad {m n L : ℕ} [NeZero L]
    (hm : 0 < m) (hn : 0 < n) (hL : m + n - 1 ≤ L) (t : ℤ → ℂ) :
    toeplitzMatrix (m := m) (n := n) t = cyclicCropMatrix m L *
      Matrix.circulant (toeplitzCirculantColumn m n L t) * cyclicPadMatrix n L := by
  ext i j
  simp only [Matrix.mul_apply, cyclicCropMatrix, cyclicPadMatrix,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    mul_ite, mul_one, mul_zero, Matrix.circulant_apply, toeplitzMatrix]
  exact (toeplitzCirculantColumn_sub hm hn hL t i j).symm

/-- Exact Fourier formula for a rectangular Toeplitz product, with actual
zero-padding and cropping matrices.
Source: Meyer, §5.5, convolution theorem (5.5.37).
atlas: toeplitz-circulant-fft-product (partial) -/
theorem toeplitzMatrix_mulVec_eq_invDFT {m n L : ℕ} [NeZero L]
    (hm : 0 < m) (hn : 0 < n) (hL : m + n - 1 ≤ L)
    (t : ℤ → ℂ) (x : Fin n → ℂ) :
    toeplitzMatrix (m := m) t *ᵥ x = cyclicCropMatrix m L *ᵥ
      ZMod.dft.symm (fun j => ZMod.dft (toeplitzCirculantColumn m n L t) j *
        ZMod.dft (cyclicPadMatrix n L *ᵥ x) j) := by
  rw [toeplitzMatrix_eq_crop_circulant_pad (L := L) hm hn hL,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, circulant_mulVec_eq_invDFT]

end NLAlib
