import NLAlib.RandomMatrix.Gaussian.Basic.LinearForms
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The unnormalized symmetric Gaussian sum

The map `G ↦ G + Gᴴ` gives a real symmetric Gaussian ensemble whose covariance
is twice the sum of the two endpoint orientations. Its scale is explicit:
off-diagonal entries have variance two and diagonal entries variance four.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace NLAlib

/-- The unnormalized symmetric Gaussian sum `G + Gᴴ`. For a real standard
Gaussian matrix this has off-diagonal variance two and diagonal variance four. -/
def gaussianSymmetricSum {n : Type*} (G : Matrix n n ℝ) : Matrix n n ℝ := G + Gᴴ

/-- The symmetric Gaussian sum is Hermitian at every sample. -/
theorem gaussianSymmetricSum_isHermitian {n : Type*} (G : Matrix n n ℝ) :
    (gaussianSymmetricSum G).IsHermitian := by
  change (G + Gᴴ)ᴴ = G + Gᴴ
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  exact add_comm _ _

/-- The symmetric-sum ensemble map is continuous. -/
theorem continuous_gaussianSymmetricSum {n : Type*} [Fintype n] :
    Continuous (gaussianSymmetricSum (n := n)) := by
  unfold gaussianSymmetricSum
  fun_prop

/-- The coefficient array of one symmetric-sum entry is the sum of its two
oriented matrix units. A diagonal entry therefore has coefficient two. -/
def gaussianSymmetricSumEntryCoefficient {n : Type*} [DecidableEq n] (i j : n) : Matrix n n ℝ :=
  Matrix.single i j 1 + Matrix.single j i 1

/-- The symmetric-sum entry is exactly the Gaussian matrix linear form with
the corresponding two matrix-unit coefficients. -/
theorem gaussianSymmetricSum_apply_eq_linForm {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (i j : n) :
    gaussianSymmetricSum G i j = linForm (gaussianSymmetricSumEntryCoefficient i j) G := by
  simp [gaussianSymmetricSum, gaussianSymmetricSumEntryCoefficient, linForm, Matrix.single,
    add_mul, Finset.sum_add_distrib, ite_mul, ite_and]

/-- The coefficient inner product of two symmetric-sum entries is twice
the sum of the two endpoint-equality indicators, including diagonal entries. -/
theorem sum_gaussianSymmetricSumEntryCoefficient_mul {n : Type*} [Fintype n] [DecidableEq n]
    (i j k l : n) :
    (∑ u, ∑ v, gaussianSymmetricSumEntryCoefficient i j u v *
      gaussianSymmetricSumEntryCoefficient k l u v) =
        2 * ((if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) := by
  have hsingle (a b c d : n) :
      (∑ u, ∑ v, (Matrix.single a b 1 : Matrix n n ℝ) u v *
        (Matrix.single c d 1 : Matrix n n ℝ) u v) =
          if a = c ∧ b = d then 1 else 0 := by
    simp [Matrix.single, ite_and, mul_ite]
  simp only [gaussianSymmetricSumEntryCoefficient, Matrix.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib, hsingle]
  by_cases h1 : i = k ∧ j = l <;> by_cases h2 : i = l ∧ j = k <;>
    simp_all [eq_comm, and_comm] <;> ring

end NLAlib
