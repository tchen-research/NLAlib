import NLAlib.RandomMatrix.Gaussian.Basic.SymmetricProfile
import NLAlib.RandomMatrix.Gaussian.Basic.LinearForms
import NLAlib.Matrix.Functions.VarianceProfileGeometry
import NLAlib.Matrix.Basic.QuadForm

/-!
# Quadratic forms of the actual symmetric Gaussian ensemble

Collecting the two equal off-diagonal terms writes every quadratic form as
an explicit linear form of the independent lower-triangular Gaussian
coordinates. Its exact coefficient metric is bounded by the full ordered
variance-profile metric, including the smaller diagonal contribution.

Source: van Handel, arXiv:1502.05003v4, proof of Lemma 4.6.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

private theorem sum_symmetric_eq_lower (F : n → n → ℝ) (hF : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) =
      ∑ i, ∑ j, if j < i then 2 * F i j else if i = j then F i j else 0 := by
  have hswap : (∑ i, ∑ j, if i < j then F i j else 0) =
      ∑ i, ∑ j, if j < i then F i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hF j i]
  have hsplit : (∑ i, ∑ j, F i j) =
      (∑ i, ∑ j, if j < i then F i j else 0) +
        (∑ i, ∑ j, if i < j then F i j else 0) +
          (∑ i, ∑ j, if i = j then F i j else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> first | order | ring
  rw [hsplit, hswap]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> first | order | ring

/-- The coefficient array of a symmetric Gaussian quadratic form in the
actual independent lower-triangular coordinates. -/
def symmetricGaussianQuadraticCoefficient (b : Matrix n n ℝ) (v : n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => if j < i then 2 * b i j * v i * v j
    else if i = j then b i j * v i * v j else 0

/-- The actual symmetric Gaussian quadratic form equals the explicit
linear form of its independent Gaussian coordinates. -/
theorem quadForm_symmetricGaussianMatrix_eq_linForm
    (b G : Matrix n n ℝ) (v : n → ℝ) :
    quadForm (symmetricGaussianMatrix b G) v =
      linForm (symmetricGaussianQuadraticCoefficient b v) G := by
  rw [quadForm_eq_sum_mul_mul]
  simp only [star_trivial]
  rw [sum_symmetric_eq_lower _ (fun i j => by
    rw [(symmetricGaussianMatrix_isSymm b G).apply i j]
    ring)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [symmetricGaussianQuadraticCoefficient]
  by_cases hij : j < i
  · simp only [hij, if_true, symmetricGaussianMatrix, Matrix.of_apply,
      max_eq_left hij.le, min_eq_right hij.le]
    ring
  · by_cases heq : i = j
    · subst j
      simp only [hij, if_false, if_true, symmetricGaussianMatrix, Matrix.of_apply,
        max_self, min_self]
      ring
    · simp only [hij, heq, if_false, zero_mul]

/-- The exact independent-coordinate metric of the actual symmetric
Gaussian quadratic forms is bounded by the full ordered variance metric.
The diagonal variance is counted once on the left and twice on the right. -/
theorem sum_sq_symmetricGaussianQuadraticCoefficient_sub_le
    (b : Matrix n n ℝ) (hb : b.IsSymm) (v w : n → ℝ) :
    (∑ i, ∑ j, (symmetricGaussianQuadraticCoefficient b v i j -
      symmetricGaussianQuadraticCoefficient b w i j) ^ 2) ≤
        varianceProfileQuadraticDistanceSq (Matrix.of fun i j => b i j ^ 2) v w := by
  have hsymm : ∀ i j, b i j ^ 2 * (v i * v j - w i * w j) ^ 2 =
      b j i ^ 2 * (v j * v i - w j * w i) ^ 2 := by
    intro i j
    rw [hb.apply i j]
    ring
  rw [varianceProfileQuadraticDistanceSq]
  simp only [Matrix.of_apply]
  rw [sum_symmetric_eq_lower _ hsymm]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  dsimp [symmetricGaussianQuadraticCoefficient]
  split_ifs <;> nlinarith [sq_nonneg (b i j * (v i * v j - w i * w j))]

end NLAlib
