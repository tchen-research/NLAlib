import NLAlib.Matrix.Spectral.PositiveTraceNorm
import NLAlib.Matrix.Norms.TraceImaginary

/-! # Native norm domination by a positive imaginary trace

The PSD cone and the ordinary normalized trace bound the actual matrix
imaginary part. No matrix measure or support premise is involved.
-/

noncomputable section
set_option autoImplicit false
open Matrix
open scoped MatrixOrder ComplexOrder ComplexStarModule
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- PSD matrix imaginary part is bounded by the actual normalized trace
imaginary part times the dimension. -/
theorem norm_imaginaryPart_le_card_mul_im_normalizedTrace
    (A : M) (hA : (imaginaryPart A : M).PosSemidef) :
    ‖(imaginaryPart A : M)‖≤(Fintype.card n : ℝ)*(NLAlib.normalizedTrace A).im := by
  have hd : (Fintype.card n : ℂ)⁻¹=(((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv,Complex.ofReal_natCast]
  have hh := congrArg Complex.re (NLAlib.normalizedTrace_imaginaryPart A)
  rw [NLAlib.normalizedTrace,hd] at hh
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hh
  have hcard : (Fintype.card n : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ht : (imaginaryPart A : M).trace.re=
      (Fintype.card n : ℝ)*(NLAlib.normalizedTrace A).im := by
    rw [← hh]
    field_simp [hcard]
  have hn : ‖(imaginaryPart A : M)‖≤(imaginaryPart A : M).trace.re := by
    simpa only [NLAlib.specNorm_eq_norm] using hA.specNorm_le_re_trace
  exact hn.trans_eq ht

end Matrix
