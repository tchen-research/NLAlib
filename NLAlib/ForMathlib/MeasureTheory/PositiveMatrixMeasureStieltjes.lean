import NLAlib.ForMathlib.MeasureTheory.PositiveMatrixMeasure
import NLAlib.ForMathlib.Analysis.Matrix.HermitianSpanning
import NLAlib.ForMathlib.Analysis.Complex.Harmonic.SignedStieltjes

/-!
# Entrywise Stieltjes transforms of positive matrix measures

Native complex entry measures are integrated by their real and imaginary
signed parts. Finite polarization relates these exact entry integrals to
all scalar quadratic transforms.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace MeasureTheory.PositiveMatrixMeasure
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Stieltjes integral of a native complex entry measure, written
through its real and imaginary signed parts and the native vector integral. -/
def entryStieltjesTransform (P : PositiveMatrixMeasure ℝ n) (z : ℂ) (i j : n) : ℂ :=
  (ComplexMeasure.re (P.entry i j)).stieltjesTransform z +
    Complex.I * (ComplexMeasure.im (P.entry i j)).stieltjesTransform z

/-- Real parts of entry measures are polarized scalar quadratic signed measures. -/
theorem re_entry_eq_quadraticForm (P : PositiveMatrixMeasure ℝ n) (i j : n) :
    ComplexMeasure.re (P.entry i j) = (1 / 4 : ℝ) •
      (P.quadraticForm (Pi.single i 1 + Pi.single j 1) -
        P.quadraticForm (Pi.single i 1 - Pi.single j 1)) := by
  apply VectorMeasure.ext
  intro E hE
  change (P E i j).re = (1 / 4 : ℝ) *
    ((star (Pi.single i 1 + Pi.single j 1) ⬝ᵥ (P E *ᵥ (Pi.single i 1 + Pi.single j 1))).re -
      (star (Pi.single i 1 - Pi.single j 1) ⬝ᵥ (P E *ᵥ (Pi.single i 1 - Pi.single j 1))).re)
  have hQ := congrArg Complex.re (matrixQuadraticFormCLM_single_add_sub (P E) i j)
  have hsym : P E j i = star (P E i j) := ((P.isHermitian E hE).apply j i).symm
  simp only [matrixQuadraticFormCLM_apply, Complex.sub_re, Complex.mul_re,
    Complex.add_re, hsym, Complex.star_def, Complex.conj_re] at hQ
  norm_num only [show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl, mul_zero, zero_mul, sub_zero, mul_one, add_zero] at hQ
  linarith

/-- Imaginary parts of entry measures are polarized scalar quadratic signed measures. -/
theorem im_entry_eq_quadraticForm (P : PositiveMatrixMeasure ℝ n) (i j : n) :
    ComplexMeasure.im (P.entry i j) = (-1 / 4 : ℝ) •
      (P.quadraticForm (Pi.single i 1 + Complex.I • Pi.single j 1) -
        P.quadraticForm (Pi.single i 1 - Complex.I • Pi.single j 1)) := by
  apply VectorMeasure.ext
  intro E hE
  change (P E i j).im = (-1 / 4 : ℝ) *
    ((star (Pi.single i 1 + Complex.I • Pi.single j 1) ⬝ᵥ
      (P E *ᵥ (Pi.single i 1 + Complex.I • Pi.single j 1))).re -
      (star (Pi.single i 1 - Complex.I • Pi.single j 1) ⬝ᵥ
        (P E *ᵥ (Pi.single i 1 - Complex.I • Pi.single j 1))).re)
  have hQ := congrArg Complex.re (matrixQuadraticFormCLM_single_add_sub_I (P E) i j)
  have hsym : P E j i = star (P E i j) := ((P.isHermitian E hE).apply j i).symm
  simp only [matrixQuadraticFormCLM_apply, Complex.sub_re, Complex.mul_re,
    Complex.mul_im, Complex.sub_im, hsym, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im] at hQ
  norm_num only [show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl, mul_zero, zero_mul, sub_zero, mul_one, add_zero] at hQ
  linarith

/-- All quadratic integral identities imply literal entrywise Stieltjes
integral identities for the native complex entry measures. -/
theorem entryStieltjesTransform_eq_of_quadraticForm
    (P : PositiveMatrixMeasure ℝ n) (M : ℂ → Matrix n n ℂ)
    (hrep : ∀ v : n → ℂ, ∀ z : ℂ, 0 < z.im →
      (P.quadraticForm v).stieltjesTransform z = matrixQuadraticFormCLM v (M z))
    {z : ℂ} (hz : 0 < z.im) (i j : n) :
    P.entryStieltjesTransform z i j = M z i j := by
  rw [entryStieltjesTransform, re_entry_eq_quadraticForm, im_entry_eq_quadraticForm]
  simp only [SignedMeasure.stieltjesTransform_smul,
    SignedMeasure.stieltjesTransform_sub _ _ hz, Complex.real_smul, hrep _ z hz]
  rw [matrixQuadraticFormCLM_single_add_sub, matrixQuadraticFormCLM_single_add_sub_I]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

end MeasureTheory.PositiveMatrixMeasure
