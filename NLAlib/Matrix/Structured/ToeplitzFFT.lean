import NLAlib.Matrix.Structured.ToeplitzCirculant
import NLAlib.Matrix.Structured.RadixTwoDFT

/-! # A counted FFT implementation of rectangular Toeplitz multiplication

With the padded column's DFT supplied as a precomputed constant, each call
performs one forward FFT, one pointwise multiplication per coordinate, and
one inverse FFT. Its value is proved equal to the dense Toeplitz product;
the explicit operation count gives the claimed `O(L log L)` arithmetic cost.
Source: Meyer, §5.5, convolution theorem (5.5.37).
-/
noncomputable section
open scoped Matrix
namespace NLAlib
open RadixTwoFFT

/-- The actual FFT product algorithm with the column transform precomputed.
Coordinate extension and restriction require no complex arithmetic. -/
def toeplitzFFTProduct (m n s : ℕ) (columnDFT : ZMod (size s) → ℂ)
    (x : Fin n → ℂ) : ArithmeticResult (Fin m → ℂ) :=
  let forward := transform s (cyclicPadMatrix n (size s) *ᵥ x)
  let multiplied := fun j => columnDFT j * forward.value j
  let backward := inverseTransform s multiplied
  ⟨cyclicCropMatrix m (size s) *ᵥ backward.value,
    forward.mulCount + size s + backward.mulCount,
    forward.addCount + backward.addCount⟩

/-- The counted FFT implementation returns the exact Toeplitz product.
No dense Toeplitz or circulant multiplication is used by this algorithm.
Source: Meyer, §5.5, convolution theorem (5.5.37).
atlas: toeplitz-circulant-fft-product (partial) -/
theorem toeplitzFFTProduct_value {m n s : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hL : m + n - 1 ≤ size s) (t : ℤ → ℂ) (x : Fin n → ℂ) :
    (toeplitzFFTProduct m n s (ZMod.dft (toeplitzCirculantColumn m n (size s) t)) x).value =
      toeplitzMatrix (m := m) t *ᵥ x := by
  simp only [toeplitzFFTProduct, inverseTransform_value_eq_invDFT, transform_value_eq_dft]
  exact (toeplitzMatrix_mulVec_eq_invDFT hm hn hL t x).symm

/-- Exact multiplication and addition counts of the actual FFT Toeplitz
algorithm, including the length-one case. The two inverse-normalization and
pointwise phases account for `2L` multiplications beyond the butterflies. -/
theorem toeplitzFFTProduct_cost (m n s : ℕ) (columnDFT : ZMod (size s) → ℂ)
    (x : Fin n → ℂ) :
    (toeplitzFFTProduct m n s columnDFT x).mulCount = s * size s + 2 * size s ∧
      (toeplitzFFTProduct m n s columnDFT x).addCount = 2 * s * size s := by
  let forward := transform s (cyclicPadMatrix n (size s) *ᵥ x)
  let multiplied := fun j => columnDFT j * forward.value j
  have hf := transform_mulCount_twice s (cyclicPadMatrix n (size s) *ᵥ x)
  have hb := transform_mulCount_twice s multiplied
  constructor
  · change forward.mulCount + size s + ((transform s multiplied).mulCount + size s) = _
    change 2 * forward.mulCount = _ at hf
    omega
  · change forward.addCount + (transform s multiplied).addCount = _
    dsimp only [forward]
    rw [transform_addCount, transform_addCount, size_eq_two_pow]
    ring

/-- An explicit nearly linear arithmetic bound attached to the implemented
algorithm: at length `L = 2^s`, the total is `3sL + 2L` operations.
Supplied roots, the precomputed column DFT, and coordinate permutations are free.
Source: Meyer, §5.5, and the radix-two butterfly count.
atlas: toeplitz-circulant-fft-product -/
theorem toeplitzFFTProduct_totalCost (m n s : ℕ) (columnDFT : ZMod (size s) → ℂ)
    (x : Fin n → ℂ) :
    (toeplitzFFTProduct m n s columnDFT x).mulCount +
      (toeplitzFFTProduct m n s columnDFT x).addCount = (3 * s + 2) * 2 ^ s := by
  rw [(toeplitzFFTProduct_cost m n s columnDFT x).1,
    (toeplitzFFTProduct_cost m n s columnDFT x).2, size_eq_two_pow]
  ring

end NLAlib
