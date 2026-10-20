import NLAlib.Probability.Free.WordMatrixAmplification
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Dimension-free norm control of actual matrix-coefficient free fields

The native matrix-amplified creation sum has exactly the coefficient Gram
norm. The concrete field sum is creation plus its adjoint, giving the sharp
factor two bound with no matrix-dimension factor. These are deterministic
facts about the actual word-space realization; no law or norm conclusion is
assumed. Source: arXiv:2406.11453v2, the free Khintchine input to Lemma 4.7.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical ComplexOrder Matrix

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "K" => WordMatrixHilbertSpace D ι
local notation "B" => W →L[ℂ] W

/-- Amplified coefficient blocks preserve addition in the operator factor. -/
theorem wordMatrixTensor_add (A : Matrix D D ℂ) (T U : B) :
    wordMatrixTensor A (T + U) = wordMatrixTensor A T + wordMatrixTensor A U := by
  unfold wordMatrixTensor
  rw [← map_add]
  congr 1
  apply CStarMatrix.ext
  intro i j
  change A i j • (T + U) = A i j • T + A i j • U
  exact smul_add _ _ _

/-- A zero word operator gives a zero native coefficient block. -/
@[simp]
theorem wordMatrixTensor_zero (A : Matrix D D ℂ) :
    wordMatrixTensor A (0 : B) = 0 := by
  unfold wordMatrixTensor
  rw [← map_zero (CStarMatrix.toPiLpStarAlgHom (D := D) (H := W))]
  congr 1
  apply CStarMatrix.ext
  intro i j
  change A i j • (0 : B) = 0
  exact smul_zero _

/-- Native adjoints act on both the scalar coefficient and word operator. -/
theorem star_wordMatrixTensor (A : Matrix D D ℂ) (T : B) :
    star (wordMatrixTensor A T) = wordMatrixTensor Aᴴ (star T) := by
  unfold wordMatrixTensor
  rw [← map_star]
  congr 1
  apply CStarMatrix.ext
  intro i j
  change star (A j i • T) = star (A j i) • star T
  exact star_smul _ _

/-- The genuine block action multiplies coefficient tensors in their actual
operator order. -/
theorem wordMatrixTensor_mul (A E : Matrix D D ℂ) (T U : B) :
    wordMatrixTensor A T * wordMatrixTensor E U = wordMatrixTensor (A * E) (T * U) := by
  unfold wordMatrixTensor
  rw [← map_mul]
  congr 1
  apply CStarMatrix.ext
  intro i j
  change (∑ l, (A i l • T) * (E l j • U)) = (∑ l, A i l * E l j) • (T * U)
  simp only [Finset.sum_smul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

/-- Tensoring with the identity word operator is the actual faithful scalar
coefficient embedding. -/
theorem wordMatrixTensor_one (A : Matrix D D ℂ) :
    wordMatrixTensor A (1 : B) = wordMatrixCoefficientHom A := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  simp only [wordMatrixTensor_apply, wordMatrixCoefficientHom_apply,
    one_apply_eq_self]

/-- The actual native creation sum for a finite family of matrix coefficients. -/
def wordMatrixCreationSum [Fintype ι] (A : ι → Matrix D D ℂ) : K →L[ℂ] K :=
  ∑ i, wordMatrixTensor (A i) (wordCreation i).toContinuousLinearMap

omit [DecidableEq D] in
private theorem star_sum_wordMatrixOperator [Fintype ι] (f : ι → K →L[ℂ] K) :
    star (∑ i, f i) = ∑ i, star (f i) := by
  change ContinuousLinearMap.adjoint (∑ i, f i) = ∑ i, ContinuousLinearMap.adjoint (f i)
  exact map_sum _ _ _

/-- Orthogonality of prefix creation gives the exact coefficient Gram
operator for the actual amplified creation sum. Empty families and empty
matrix dimension are included. -/
theorem star_wordMatrixCreationSum_mul [Fintype ι] (A : ι → Matrix D D ℂ) :
    star (wordMatrixCreationSum A) * wordMatrixCreationSum A =
      wordMatrixCoefficientHom (∑ i, (A i)ᴴ * A i) := by
  unfold wordMatrixCreationSum
  rw [star_sum_wordMatrixOperator, Finset.sum_mul]
  simp_rw [Finset.mul_sum, star_wordMatrixTensor, wordMatrixTensor_mul,
    star_wordCreation_mul_wordCreation]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, wordMatrixTensor_one]
  · intro j _ hji
    simp only [if_neg (Ne.symm hji), wordMatrixTensor_zero]
  · simp

/-- The squared norm of the actual matrix-coefficient creation sum equals
the native spectral norm of the coefficient Gram sum, with no dimension loss. -/
theorem norm_wordMatrixCreationSum_sq [Fintype ι] (A : ι → Matrix D D ℂ) :
    ‖wordMatrixCreationSum A‖ ^ 2 = specNorm (∑ i, (A i)ᴴ * A i) := by
  have hnorm := CStarRing.norm_star_mul_self (x := wordMatrixCreationSum A)
  rw [star_wordMatrixCreationSum_mul, norm_wordMatrixCoefficientHom] at hnorm
  simpa only [pow_two] using hnorm.symm

/-- The exact creation norm is the square root of the actual coefficient
Gram spectral norm. In particular it is valid in zero matrix dimension. -/
theorem norm_wordMatrixCreationSum [Fintype ι] (A : ι → Matrix D D ℂ) :
    ‖wordMatrixCreationSum A‖ = Real.sqrt (specNorm (∑ i, (A i)ᴴ * A i)) := by
  rw [← norm_wordMatrixCreationSum_sq, Real.sqrt_sq (norm_nonneg _)]

/-- For Hermitian coefficients, the concrete centered free linear field is
the actual amplified creation sum plus its native adjoint. -/
theorem sum_wordMatrixTensor_wordField_eq [Fintype ι]
    (A : ι → Matrix D D ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (∑ i, wordMatrixTensor (A i) (wordField i)) =
      wordMatrixCreationSum A + star (wordMatrixCreationSum A) := by
  simp only [wordField, wordAnnihilation, ← ContinuousLinearMap.star_eq_adjoint,
    wordMatrixTensor_add, Finset.sum_add_distrib, wordMatrixCreationSum,
    star_sum_wordMatrixOperator,
    star_wordMatrixTensor]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(hA i).eq]

/-- Actual Hermitian matrix-coefficient free fields have the dimension-free
factor two norm bound. The variance mass is the genuine sum of coefficient
squares, including the zero and empty-family cases.
Source: arXiv:2406.11453v2, the centered norm input to Lemma 4.7. -/
theorem norm_sum_wordMatrixTensor_wordField_le [Fintype ι]
    (A : ι → Matrix D D ℂ) (hA : ∀ i, (A i).IsHermitian) :
    ‖∑ i, wordMatrixTensor (A i) (wordField i)‖ ≤
      2 * Real.sqrt (specNorm (∑ i, A i ^ 2)) := by
  rw [sum_wordMatrixTensor_wordField_eq A hA]
  calc
    _ ≤ ‖wordMatrixCreationSum A‖ + ‖star (wordMatrixCreationSum A)‖ := norm_add_le _ _
    _ = 2 * Real.sqrt (specNorm (∑ i, A i ^ 2)) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint.norm_map,
        norm_wordMatrixCreationSum]
      simp only [fun i => (hA i).eq, ← pow_two]
      ring

/-- Centering the actual amplified linear reference removes its full mean
exactly and leaves the dimension-free free-series norm bound. -/
theorem norm_wordMatrixLinearCombination_sub_mean_le [Fintype ι]
    (A₀ : Matrix D D ℂ) (A : ι → Matrix D D ℂ) (hA : ∀ i, (A i).IsHermitian) :
    ‖wordMatrixLinearCombination A₀ A - wordMatrixCoefficientHom A₀‖ ≤
      2 * Real.sqrt (specNorm (∑ i, A i ^ 2)) := by
  simpa only [wordMatrixLinearCombination, add_sub_cancel_left] using
    norm_sum_wordMatrixTensor_wordField_le A hA

end NLAlib
