import NLAlib.Probability.Gaussian.Moments.ComplexLinearMoments
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Ring

/-!
# Actual multicolor Gaussian unitary ensemble

The matrices are constructed from independent real standard Gaussian
coordinates. Pointwise Hermitian symmetry, real linearity, joint Gaussian
law of the entire matrix array and of all real/imaginary entries, exact zero
mean, and exact complex bilinear entry covariance follow from the construction.
The diagonal variance is 1/N and each off-diagonal real/imaginary variance is
1/(2N), including the dimension-one case.

Source: Chen--Garza-Vargas--van Handel, arXiv:2412.00593v2, Definition 2.8;
this native covariance is an input to the word encoding in Lemma 4.7.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- Independent coordinates are indexed by color, ordered entry, and real or
imaginary component. Fin 2 is a coordinate label, not a covariance dimension. -/
abbrev GUECoordinate (c n : Type*) := c × n × n × Fin 2

/-- The unsymmetrized complex standard Gaussian matrix, before GUE scaling. -/
def gueRawMatrix {c n : Type*} (x : GUECoordinate c n → ℝ) (i : c) :
    Matrix n n ℂ :=
  fun a b => (x (i, a, b, 0) : ℂ) + Complex.I * (x (i, a, b, 1) : ℂ)

/-- Actual multicolor normalized GUE matrices on the canonical product Gaussian
space. For N>0 this has diagonal variance 1/N and off-diagonal complex variance
1/N; no extra diagonal normalization is needed. -/
def gueMatrix {c n : Type*} [Fintype n]
    (x : GUECoordinate c n → ℝ) (i : c) : Matrix n n ℂ :=
  ((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) •
    (gueRawMatrix x i + (gueRawMatrix x i)ᴴ)

/-- The symmetrized Gaussian construction is Hermitian at every sample point. -/
theorem gueMatrix_isHermitian {c n : Type*} [Fintype n]
    (x : GUECoordinate c n → ℝ) (i : c) : (gueMatrix x i).IsHermitian := by
  exact (Matrix.isHermitian_add_transpose_self (gueRawMatrix x i)).smul (by rfl)

private def gueRawEntryCoefficient {c n : Type*} [DecidableEq c] [DecidableEq n]
    (i : c) (a b : n) : GUECoordinate c n → ℂ :=
  Pi.single (i, a, b, 0) 1 + Pi.single (i, b, a, 0) 1 +
    Complex.I • (Pi.single (i, a, b, 1) 1 - Pi.single (i, b, a, 1) 1)

/-- The complex coefficient vector of an actual GUE entry in the independent
real coordinate family, including its exact `1/(2 sqrt N)` normalization.
This is the finite linear-form interface for entry-product Wick calculations. -/
def gueEntryCoefficient {c n : Type*} [Fintype n] [DecidableEq c] [DecidableEq n]
    (i : c) (a b : n) : GUECoordinate c n → ℂ :=
  ((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) • gueRawEntryCoefficient i a b

private theorem gueRawEntryCoefficient_dot
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n]
    (i j : c) (a b d e : n) :
    gueRawEntryCoefficient i a b ⬝ᵥ gueRawEntryCoefficient j d e =
      if i = j ∧ a = e ∧ b = d then 4 else 0 := by
  simp only [gueRawEntryCoefficient, add_dotProduct, sub_dotProduct,
    smul_dotProduct, single_dotProduct, one_mul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    by_cases had : a = d <;> by_cases hae : a = e <;>
      by_cases hbd : b = d <;> by_cases hbe : b = e <;>
      simp_all [mul_add, mul_sub, Complex.I_mul_I] <;> norm_num
  · simp [hij]

private theorem gueMatrix_apply_eq_linearForm
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n]
    (x : GUECoordinate c n → ℝ) (i : c) (a b : n) :
    gueMatrix x i a b = complexGaussianLinearForm
      (((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) • gueRawEntryCoefficient i a b) x := by
  change _ = (((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) •
    gueRawEntryCoefficient i a b) ⬝ᵥ (fun k => (x k : ℂ))
  simp only [smul_dotProduct, gueRawEntryCoefficient, add_dotProduct,
    sub_dotProduct, single_dotProduct, one_mul]
  simp [gueMatrix, gueRawMatrix, Matrix.conjTranspose_apply, smul_eq_mul]
  ring

/-- Every actual colored GUE entry is the complex Gaussian linear form with
its normalized public entry-coefficient vector. -/
theorem gueMatrix_apply_eq_complexGaussianLinearForm
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n]
    (x : GUECoordinate c n → ℝ) (i : c) (a b : n) :
    gueMatrix x i a b = complexGaussianLinearForm (gueEntryCoefficient i a b) x := by
  simpa only [gueEntryCoefficient] using gueMatrix_apply_eq_linearForm x i a b

/-- The full colored GUE array is an actual real continuous linear image of
its independent real Gaussian coordinates. -/
def gueMatrixCLM
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n] :
    (GUECoordinate c n → ℝ) →L[ℝ] (c → Matrix n n ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun a =>
    ContinuousLinearMap.pi fun b => complexGaussianLinearFormCLM
      (((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) • gueRawEntryCoefficient i a b)

/-- Evaluate the continuous linear array map as the actual colored GUE matrices. -/
@[simp] theorem gueMatrixCLM_apply
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n]
    (x : GUECoordinate c n → ℝ) : gueMatrixCLM x = fun i => gueMatrix x i := by
  ext i a b
  change complexGaussianLinearFormCLM
    (((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) • gueRawEntryCoefficient i a b) x = _
  rw [complexGaussianLinearFormCLM_apply, gueMatrix_apply_eq_linearForm]

/-- The actual full matrix-array map is measurable. -/
@[fun_prop] theorem measurable_gueMatrix
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n] :
    Measurable (fun x : GUECoordinate c n → ℝ => fun i => gueMatrix x i) := by
  apply measurable_pi_lambda
  intro i
  apply Matrix.measurable_iff_entries.mpr
  intro a b
  have h := (complexGaussianLinearFormCLM
    (((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) • gueRawEntryCoefficient i a b)).continuous.measurable
  change Measurable (fun x : GUECoordinate c n → ℝ => complexGaussianLinearFormCLM
    (((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) • gueRawEntryCoefficient i a b) x) at h
  simpa only [complexGaussianLinearFormCLM_apply, gueMatrix_apply_eq_linearForm] using h

open scoped Matrix.Norms.L2Operator in
/-- Joint Gaussian law of the actual entire colored complex matrix array,
viewed as a real vector space. -/
theorem hasGaussianLaw_gueMatrix
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n] :
    HasGaussianLaw (fun x : GUECoordinate c n → ℝ => fun i => gueMatrix x i)
      (gaussianVector (GUECoordinate c n)) := by
  simpa only [gueMatrixCLM_apply] using
    (hasGaussianLaw_id_gaussianVector (GUECoordinate c n)).map_fun (gueMatrixCLM (c := c) (n := n))

open scoped Matrix.Norms.L2Operator in
/-- The actual full colored GUE matrix-array mean is zero. -/
theorem integral_gueMatrix_eq_zero
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n] :
    (∫ x : GUECoordinate c n → ℝ, (fun i => gueMatrix x i)
      ∂gaussianVector (GUECoordinate c n)) = 0 := by
  let K := GUECoordinate c n
  have hint := (hasGaussianLaw_id_gaussianVector K).integrable
  have hmean : (∫ x : K → ℝ, x ∂gaussianVector K) = 0 := by
    ext k
    have he := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : K => ℝ) k).integral_comp_comm hint
    change (∫ x : K → ℝ, x ∂gaussianVector K) k = 0
    have he' : (∫ x : K → ℝ, x ∂gaussianVector K) k =
        ∫ x : K → ℝ, x k ∂gaussianVector K := by
      simpa only [ContinuousLinearMap.proj_apply] using he.symm
    exact he'.trans (integral_eq_zero_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k))
  have he := (gueMatrixCLM (c := c) (n := n)).integral_comp_comm hint
  simpa only [gueMatrixCLM_apply, hmean, map_zero] using he

/-- Full real and imaginary coordinates of the actual colored GUE array.
The label 0 selects the real part; label 1 selects the imaginary part. -/
def gueRealCoordinates {c n : Type*} [Fintype n]
    (x : GUECoordinate c n → ℝ) (k : GUECoordinate c n) : ℝ :=
  if k.2.2.2 = 0 then (gueMatrix x k.1 k.2.1 k.2.2.1).re
  else (gueMatrix x k.1 k.2.1 k.2.2.1).im

/-- Joint Gaussian law in the explicit full real/imaginary entry coordinates. -/
theorem hasGaussianLaw_gueRealCoordinates
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n] :
    HasGaussianLaw (gueRealCoordinates : (GUECoordinate c n → ℝ) → GUECoordinate c n → ℝ)
      (gaussianVector (GUECoordinate c n)) := by
  let T : (GUECoordinate c n → ℝ) →L[ℝ] (GUECoordinate c n → ℝ) :=
    ContinuousLinearMap.pi fun k =>
      let L := complexGaussianLinearFormCLM
        (((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) •
          gueRawEntryCoefficient k.1 k.2.1 k.2.2.1)
      if k.2.2.2 = 0 then Complex.reCLM.comp L else Complex.imCLM.comp L
  have hT : ∀ x, T x = gueRealCoordinates x := by
    intro x
    ext k
    simp only [T, ContinuousLinearMap.pi_apply, gueRealCoordinates]
    split <;> simp only [ContinuousLinearMap.comp_apply,
      complexGaussianLinearFormCLM_apply, gueMatrix_apply_eq_linearForm]
    rfl
    rfl
  simpa only [hT] using
    (hasGaussianLaw_id_gaussianVector (GUECoordinate c n)).map_fun T

/-- Exact colored GUE entry covariance, with the complex product rather than
its Hermitian/sesquilinear counterpart. All factors are actual functions on the
canonical Gaussian probability space. It includes diagonal entries and N=1. -/
theorem integral_gueMatrix_entry_mul
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n]
    [Nonempty n] (i j : c) (a b d e : n) :
    (∫ x : GUECoordinate c n → ℝ, gueMatrix x i a b * gueMatrix x j d e
      ∂gaussianVector (GUECoordinate c n)) =
      if i = j ∧ a = e ∧ b = d then (Fintype.card n : ℂ)⁻¹ else 0 := by
  simp_rw [gueMatrix_apply_eq_linearForm]
  rw [integral_complexGaussianLinearForm_mul, smul_dotProduct, dotProduct_smul,
    gueRawEntryCoefficient_dot]
  by_cases h : i = j ∧ a = e ∧ b = d
  · rw [if_pos h, if_pos h]
    have hnonneg : (0 : ℝ) ≤ Fintype.card n := by positivity
    have hscale : 4 * ((2 * Real.sqrt (Fintype.card n))⁻¹ : ℝ) ^ 2 =
        (Fintype.card n : ℝ)⁻¹ := by
      calc
        _ = ((Real.sqrt (Fintype.card n)) ^ 2)⁻¹ := by
          simp only [mul_inv_rev, mul_pow, inv_pow]
          ring
        _ = _ := by rw [Real.sq_sqrt hnonneg]
    have hscaleC := congrArg (fun r : ℝ => (r : ℂ)) hscale
    push_cast at hscaleC
    convert hscaleC using 1
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  · simp [h]

/-- The exact bilinear covariance above concerns genuinely integrable products. -/
theorem integrable_gueMatrix_entry_mul
    {c n : Type*} [Fintype c] [Fintype n] [DecidableEq c] [DecidableEq n]
    (i j : c) (a b d e : n) :
    Integrable (fun x : GUECoordinate c n → ℝ => gueMatrix x i a b * gueMatrix x j d e)
      (gaussianVector (GUECoordinate c n)) := by
  simp_rw [gueMatrix_apply_eq_linearForm]
  exact integrable_complexGaussianLinearForm_mul _ _

end NLAlib
