import NLAlib.ForMathlib.MeasureTheory.PositiveMatrixMeasureStieltjes

/-!
# Uniqueness of positive matrix Stieltjes measures

Hermitian symmetry recovers the signed real and imaginary entry transforms
from the two transposed complex entry transforms. Signed uniqueness then
determines every native entry measure and hence the matrix vector measure.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace MeasureTheory.PositiveMatrixMeasure
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hermitian entry measures have symmetric signed real parts. -/
theorem re_entry_transpose (P : PositiveMatrixMeasure ℝ n) (i j : n) :
    ComplexMeasure.re (P.entry j i) = ComplexMeasure.re (P.entry i j) := by
  apply VectorMeasure.ext
  intro E hE
  change (P E j i).re = (P E i j).re
  simpa only [Complex.star_def, Complex.conj_re] using
    congrArg Complex.re ((P.isHermitian E hE).apply i j)

/-- Hermitian entry measures have skew-symmetric signed imaginary parts. -/
theorem im_entry_transpose (P : PositiveMatrixMeasure ℝ n) (i j : n) :
    ComplexMeasure.im (P.entry j i) = -ComplexMeasure.im (P.entry i j) := by
  apply VectorMeasure.ext
  intro E hE
  change (P E j i).im = -(P E i j).im
  have h := congrArg Complex.im ((P.isHermitian E hE).apply i j)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

/-- Entrywise upper-half-plane Stieltjes transforms uniquely determine a
positive matrix measure. No extra support or moment premise is required. -/
theorem eq_of_entryStieltjesTransform_eq
    (P Q : PositiveMatrixMeasure ℝ n)
    (h : ∀ z : ℂ, 0 < z.im → ∀ i j : n,
      P.entryStieltjesTransform z i j = Q.entryStieltjesTransform z i j) : P = Q := by
  have hre (i j : n) : ComplexMeasure.re (P.entry i j) = ComplexMeasure.re (Q.entry i j) := by
    apply SignedMeasure.eq_of_stieltjesTransform_eq
    intro z hz
    have hij := h z hz i j
    have hji := h z hz j i
    rw [entryStieltjesTransform, entryStieltjesTransform] at hij
    rw [entryStieltjesTransform, entryStieltjesTransform, re_entry_transpose P i j,
      re_entry_transpose Q i j, im_entry_transpose P i j, im_entry_transpose Q i j,
      SignedMeasure.stieltjesTransform_neg, SignedMeasure.stieltjesTransform_neg] at hji
    linear_combination (1 / 2 : ℂ) * hij + (1 / 2 : ℂ) * hji
  have him (i j : n) : ComplexMeasure.im (P.entry i j) = ComplexMeasure.im (Q.entry i j) := by
    apply SignedMeasure.eq_of_stieltjesTransform_eq
    intro z hz
    have hij := h z hz i j
    have hji := h z hz j i
    rw [entryStieltjesTransform, entryStieltjesTransform] at hij
    rw [entryStieltjesTransform, entryStieltjesTransform, re_entry_transpose P i j,
      re_entry_transpose Q i j, im_entry_transpose P i j, im_entry_transpose Q i j,
      SignedMeasure.stieltjesTransform_neg, SignedMeasure.stieltjesTransform_neg] at hji
    have hd : (2 * Complex.I) * (ComplexMeasure.im (P.entry i j)).stieltjesTransform z =
        (2 * Complex.I) * (ComplexMeasure.im (Q.entry i j)).stieltjesTransform z := by
      linear_combination hij - hji
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num) Complex.I_ne_zero) hd
  have hv : P.toVectorMeasure = Q.toVectorMeasure := by
    apply VectorMeasure.ext
    intro E _
    ext i j
    apply Complex.ext
    · exact congrArg (fun s : SignedMeasure ℝ => s E) (hre i j)
    · exact congrArg (fun s : SignedMeasure ℝ => s E) (him i j)
  cases P
  cases Q
  cases hv
  rfl

end MeasureTheory.PositiveMatrixMeasure
