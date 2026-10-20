import NLAlib.Matrix.Norms.TraceSpectral
import NLAlib.ForMathlib.Analysis.Matrix.QuadraticPositiveMap
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Native imaginary parts of the normalized matrix trace

The normalized trace commutes with imaginary parts, preserves their
positivity, and is contractive in the actual spectral norm.
-/

noncomputable section
set_option autoImplicit false
open Matrix
open scoped ComplexOrder ComplexStarModule MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The dimension-normalized trace commutes with native imaginary
parts, including empty matrix dimensions. -/
theorem normalizedTrace_imaginaryPart (A : Matrix n n ℂ) :
    normalizedTrace (imaginaryPart A : Matrix n n ℂ)=((normalizedTrace A).im : ℂ) := by
  have he := map_imaginaryPart (Matrix.tracePositiveLinearMap n ℂ ℂ) A
  simp only [Matrix.tracePositiveLinearMap_apply,Complex.coe_imaginaryPart] at he
  have hd : (Fintype.card n : ℂ)⁻¹=(((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv,Complex.ofReal_natCast]
  simp only [normalizedTrace,he,hd,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,add_zero,Complex.ofReal_mul]

/-- The imaginary part of the normalized trace is bounded by the
spectral norm of the actual matrix imaginary part. -/
theorem im_normalizedTrace_le_specNorm_imaginaryPart (A : Matrix n n ℂ) :
    (normalizedTrace A).im≤specNorm (imaginaryPart A : Matrix n n ℂ) := by
  calc
    _ ≤ |(normalizedTrace A).im| := le_abs_self _
    _ = ‖normalizedTrace (imaginaryPart A : Matrix n n ℂ)‖ := by
      rw [normalizedTrace_imaginaryPart,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := norm_normalizedTrace_le_specNorm _

/-- A positive semidefinite native matrix imaginary part gives
nonnegative imaginary normalized trace. -/
theorem im_normalizedTrace_nonneg_of_posSemidef_imaginaryPart
    (A : Matrix n n ℂ) (hA : (imaginaryPart A : Matrix n n ℂ).PosSemidef) :
    0≤(normalizedTrace A).im := by
  have he := map_imaginaryPart (Matrix.tracePositiveLinearMap n ℂ ℂ) A
  simp only [Matrix.tracePositiveLinearMap_apply,Complex.coe_imaginaryPart] at he
  have htrace : 0≤A.trace.im := by
    have hn := hA.trace_nonneg
    rw [he] at hn
    exact (RCLike.nonneg_iff.mp hn).1
  have hd : (Fintype.card n : ℂ)⁻¹=(((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [normalizedTrace,hd]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) htrace

end NLAlib
