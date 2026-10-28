import NLAlib.RandomMatrix.Gaussian.Basic.ComplexGaussianMatrix
import NLAlib.ForMathlib.MeasureTheory.PolynomialZeroSetsField
import NLAlib.ForMathlib.LinearAlgebra.Matrix.RankInvertibility
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Almost-sure full rank of native complex Gaussian matrices

The transpose Gram determinant is a nonzero holomorphic polynomial in the
entries. Its almost-sure nonvanishing gives full row rank. The Hermitian Gram
matrix is then invertible by the exact algebraic rank identity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder
namespace NLAlib

instance nullSingletonClass_circularComplexGaussian : NullSingletonClass circularComplexGaussian := by
  refine ⟨fun z => ?_⟩
  have hm : Measurable (fun p : ℝ × ℝ => (⟨p.1,p.2⟩ : ℂ)) :=
    Complex.equivRealProdCLM.symm.continuous.measurable
  rw [circularComplexGaussian, Measure.map_apply hm (measurableSet_singleton z)]
  have he : (fun p : ℝ × ℝ => (⟨p.1,p.2⟩ : ℂ)) ⁻¹' {z} = {(z.re,z.im)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)
    · rintro rfl
      exact Complex.ext rfl rfl
  rw [he]
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact measure_singleton _

private theorem eval_det_complexPolynomial_mul_transpose (r s : ℕ)
    (G : Matrix (Fin r) (Fin s) ℂ) :
    MvPolynomial.eval (fun ij : Fin r × Fin s => G ij.1 ij.2)
      (Matrix.mvPolynomialX (Fin r) (Fin s) ℂ * (Matrix.mvPolynomialX (Fin r) (Fin s) ℂ)ᵀ).det =
        (G*Gᵀ).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
  have hX : (Matrix.mvPolynomialX (Fin r) (Fin s) ℂ).map
      (MvPolynomial.eval fun ij : Fin r × Fin s => G ij.1 ij.2) = G := by
    ext i j
    simp
  rw [hX]

private theorem det_complexPolynomial_mul_transpose_ne_zero {r s : ℕ} (h : r ≤ s) :
    (Matrix.mvPolynomialX (Fin r) (Fin s) ℂ * (Matrix.mvPolynomialX (Fin r) (Fin s) ℂ)ᵀ).det ≠ 0 := by
  intro h0
  let G0 : Matrix (Fin r) (Fin s) ℂ := Matrix.of fun i j => if j = Fin.castLE h i then 1 else 0
  have hE : G0*G0ᵀ=1 := by
    ext i j
    simp [G0, Matrix.mul_apply, Matrix.one_apply, Fin.castLE_inj, eq_comm]
  have he := eval_det_complexPolynomial_mul_transpose r s G0
  rw [h0, map_zero, hE, Matrix.det_one] at he
  exact zero_ne_one he

/-- A native circular complex Gaussian matrix of width at least its height
has full row rank almost surely, including empty row spaces. -/
theorem circularComplexGaussianMatrix_ae_rank_eq {r s : ℕ} (hrs : r ≤ s) :
    ∀ᵐ G ∂circularComplexGaussianMatrix (Fin r) (Fin s), G.rank = r := by
  have h := MvPolynomial.ae_eval_ne_zero_normedField circularComplexGaussian _
    (det_complexPolynomial_mul_transpose_ne_zero hrs)
  have hf := circularComplexGaussianMatrix_map_uncurry (m := Fin r) (n := Fin s)
  change _ = Measure.pi (fun _ : Fin r × Fin s => circularComplexGaussian) at hf
  rw [← hf] at h
  have h' := ae_of_ae_map (by fun_prop : Measurable
    (fun G : Matrix (Fin r) (Fin s) ℂ => fun ij : Fin r × Fin s => G ij.1 ij.2)).aemeasurable h
  filter_upwards [h'] with G hG
  rw [eval_det_complexPolynomial_mul_transpose] at hG
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hG)
  have hr := Matrix.rank_of_isUnit _ hu
  have hlo := Matrix.rank_mul_le_left G Gᵀ
  have hhi := Matrix.rank_le_height G
  rw [Fintype.card_fin] at hr
  omega

/-- The Hermitian row Gram matrix of a wide native circular complex Gaussian
matrix is invertible almost surely. -/
theorem circularComplexGaussianMatrix_ae_isUnit_mul_conjTranspose {r s : ℕ} (hrs : r ≤ s) :
    ∀ᵐ G ∂circularComplexGaussianMatrix (Fin r) (Fin s), IsUnit (G*Gᴴ) := by
  filter_upwards [circularComplexGaussianMatrix_ae_rank_eq hrs] with G hG
  apply Matrix.isUnit_of_rank_eq_card
  rw [Matrix.rank_self_mul_conjTranspose, hG, Fintype.card_fin]

/-- Full Hermitian row rank transports to random matrices on any sample
space with the exact native complex Gaussian matrix law. -/
theorem ae_isUnit_mul_conjTranspose_of_hasLaw_circularComplexGaussianMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {r s : ℕ}
    {G : Ω → Matrix (Fin r) (Fin s) ℂ}
    (hG : HasLaw G (circularComplexGaussianMatrix (Fin r) (Fin s)) μ) (hrs : r ≤ s) :
    ∀ᵐ ω ∂μ, IsUnit (G ω*(G ω)ᴴ) := by
  have h := circularComplexGaussianMatrix_ae_isUnit_mul_conjTranspose hrs
  rw [← hG.map_eq] at h
  exact ae_of_ae_map hG.aemeasurable h

end NLAlib
