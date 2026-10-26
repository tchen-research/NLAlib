import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic

/-!
# Nonlinear geometry of a symmetric variance profile

The nonlinear deformation `v_i sqrt (sum_j B_ij v_j²)` converts the
quadratic Gaussian increment metric into a Euclidean metric, up to a
quadratic correction in the squared coordinates. This is the deterministic
geometric kernel behind the dimension-free Gaussian norm estimate.

Source: van Handel, arXiv:1502.05003v4, Lemma 4.6, with parameter gamma one.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- The Euclidean radius of a vector weighted by one row of a variance
profile. The profile entries, rather than their square roots, are variances. -/
def varianceProfileRadius (B : Matrix n n ℝ) (v : n → ℝ) (i : n) : ℝ :=
  Real.sqrt (∑ j, B i j * v j ^ 2)

/-- The nonlinear deformation of a vector by its variance-profile radii. -/
def varianceProfileDeformation (B : Matrix n n ℝ) (v : n → ℝ) (i : n) : ℝ :=
  v i * varianceProfileRadius B v i

/-- The variance-profile quadratic form in differences of squared coordinates. -/
def varianceProfileSquareDifferenceForm (B : Matrix n n ℝ) (v w : n → ℝ) : ℝ :=
  ∑ i, ∑ j, (v i ^ 2 - w i ^ 2) * B i j * (v j ^ 2 - w j ^ 2)

/-- Twice the full weighted squared increments of the quadratic coordinate
products. It dominates the actual symmetric Gaussian quadratic increment
variance, because diagonal coefficients are counted twice. -/
def varianceProfileQuadraticDistanceSq (B : Matrix n n ℝ) (v w : n → ℝ) : ℝ :=
  2 * ∑ i, ∑ j, B i j * (v i * v j - w i * w j) ^ 2

/-- A variance-profile radius is nonnegative. -/
theorem varianceProfileRadius_nonneg (B : Matrix n n ℝ) (v : n → ℝ) (i : n) :
    0 ≤ varianceProfileRadius B v i := Real.sqrt_nonneg _

/-- The square of a row radius is its exact weighted quadratic energy. -/
theorem varianceProfileRadius_sq (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (v : n → ℝ) (i : n) :
    varianceProfileRadius B v i ^ 2 = ∑ j, B i j * v j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun j _ => mul_nonneg (hB i j) (sq_nonneg _))

/-- A row radius is the Euclidean norm of the corresponding weighted
vector, including rows with vanishing variances. -/
theorem varianceProfileRadius_eq_norm (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (v : n → ℝ) (i : n) :
    varianceProfileRadius B v i =
      ‖(WithLp.toLp 2 (fun j => Real.sqrt (B i j) * v j) : EuclideanSpace ℝ n)‖ := by
  have hsq := EuclideanSpace.norm_sq_eq
    (WithLp.toLp 2 (fun j => Real.sqrt (B i j) * v j) : EuclideanSpace ℝ n)
  simp only [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hB i _)] at hsq
  have hr := varianceProfileRadius_sq B hB v i
  nlinarith [varianceProfileRadius_nonneg B v i,
    norm_nonneg (WithLp.toLp 2 (fun j => Real.sqrt (B i j) * v j) : EuclideanSpace ℝ n)]

/-- Every row radius obeys the triangle inequality, including degenerate
rows. It is the Euclidean norm after multiplication by the square roots of
the row variances. -/
theorem varianceProfileRadius_add_le (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (v w : n → ℝ) (i : n) :
    varianceProfileRadius B (v + w) i ≤ varianceProfileRadius B v i + varianceProfileRadius B w i := by
  simp only [varianceProfileRadius_eq_norm B hB]
  have hv : (WithLp.toLp 2 (fun j => Real.sqrt (B i j) * (v + w) j) : EuclideanSpace ℝ n) =
      WithLp.toLp 2 (fun j => Real.sqrt (B i j) * v j) +
        WithLp.toLp 2 (fun j => Real.sqrt (B i j) * w j) := by
    rw [WithLp.ext_iff]
    funext j
    simp only [WithLp.ofLp_add, Pi.add_apply]
    ring
  rw [hv]
  exact norm_add_le _ _

/-- A row radius has Euclidean Lipschitz constant at most `L` when every
variance in that row is at most `L²`. -/
theorem abs_varianceProfileRadius_sub_le
    (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j) (v w : n → ℝ) (i : n)
    (L : ℝ) (hL : 0 ≤ L) (hrow : ∀ j, B i j ≤ L ^ 2) :
    |varianceProfileRadius B v i - varianceProfileRadius B w i| ≤
      L * Real.sqrt (∑ j, (v j - w j) ^ 2) := by
  have hdiff :
      (WithLp.toLp 2 (fun j => Real.sqrt (B i j) * v j) : EuclideanSpace ℝ n) -
        WithLp.toLp 2 (fun j => Real.sqrt (B i j) * w j) =
          WithLp.toLp 2 (fun j => Real.sqrt (B i j) * (v - w) j) := by
    rw [WithLp.ext_iff]
    funext j
    simp only [WithLp.ofLp_sub, Pi.sub_apply]
    ring
  have hnorm := abs_norm_sub_norm_le
    (WithLp.toLp 2 (fun j => Real.sqrt (B i j) * v j) : EuclideanSpace ℝ n)
    (WithLp.toLp 2 (fun j => Real.sqrt (B i j) * w j))
  rw [hdiff, ← varianceProfileRadius_eq_norm B hB,
    ← varianceProfileRadius_eq_norm B hB, ← varianceProfileRadius_eq_norm B hB] at hnorm
  apply hnorm.trans
  have hsq : varianceProfileRadius B (v - w) i ^ 2 ≤
      (L * Real.sqrt (∑ j, (v j - w j) ^ 2)) ^ 2 := by
    rw [varianceProfileRadius_sq B hB, mul_pow,
      Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (hrow j) (sq_nonneg _)
  nlinarith [varianceProfileRadius_nonneg B (v - w) i,
    mul_nonneg hL (Real.sqrt_nonneg (∑ j, (v j - w j) ^ 2))]

private theorem squareDifferenceForm_eq_radius_sum
    (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j) (v w : n → ℝ) :
    varianceProfileSquareDifferenceForm B v w =
      ∑ i, (v i ^ 2 - w i ^ 2) *
        (varianceProfileRadius B v i ^ 2 - varianceProfileRadius B w i ^ 2) := by
  simp only [varianceProfileSquareDifferenceForm, varianceProfileRadius_sq B hB,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The nonlinear deformation controls the row-radius metric proxy with its
exact quadratic correction. This inequality requires only nonnegative
variance entries and holds for all vectors, with no unit-ball restriction. -/
theorem sum_sq_mul_varianceProfileRadius_add_sq_add_form_le
    (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j) (v w : n → ℝ) :
    (∑ i, (v i - w i) ^ 2 * varianceProfileRadius B (v + w) i ^ 2) +
        varianceProfileSquareDifferenceForm B v w ≤
      4 * (∑ i, (varianceProfileDeformation B v i - varianceProfileDeformation B w i) ^ 2) -
        varianceProfileSquareDifferenceForm B v w := by
  have htri : (∑ i, (v i - w i) ^ 2 * varianceProfileRadius B (v + w) i ^ 2) ≤
      ∑ i, (v i - w i) ^ 2 * (varianceProfileRadius B v i + varianceProfileRadius B w i) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (varianceProfileRadius_nonneg _ _ _)
        (varianceProfileRadius_add_le B hB v w i) 2) (sq_nonneg _)
  have hcoord (i : n) :
      (v i - w i) ^ 2 * (varianceProfileRadius B v i + varianceProfileRadius B w i) ^ 2 +
          2 * ((v i ^ 2 - w i ^ 2) *
            (varianceProfileRadius B v i ^ 2 - varianceProfileRadius B w i ^ 2)) ≤
        4 * (varianceProfileDeformation B v i - varianceProfileDeformation B w i) ^ 2 := by
    dsimp [varianceProfileDeformation]
    nlinarith [sq_nonneg ((v i + w i) * (varianceProfileRadius B v i - varianceProfileRadius B w i))]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset n)) => hcoord i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← squareDifferenceForm_eq_radius_sum B hB] at hsum
  linarith

/-- Symmetry identifies the full quadratic coordinate metric with the
row-radius metric and its exact squared-coordinate correction. -/
theorem varianceProfileQuadraticDistanceSq_eq_radius_add_form
    (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j) (hsymm : B.IsSymm) (v w : n → ℝ) :
    varianceProfileQuadraticDistanceSq B v w =
      (∑ i, (v i - w i) ^ 2 * varianceProfileRadius B (v + w) i ^ 2) +
        varianceProfileSquareDifferenceForm B v w := by
  have hswap : (∑ i, ∑ j, (v j - w j) ^ 2 * B i j * (v i + w i) ^ 2) =
      ∑ i, ∑ j, (v i - w i) ^ 2 * B i j * (v j + w j) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm.apply j i]
  have hpoint : (2 * ∑ i, ∑ j, B i j * (v i * v j - w i * w j) ^ 2) =
      ((∑ i, ∑ j, (v i - w i) ^ 2 * B i j * (v j + w j) ^ 2) +
        (∑ i, ∑ j, (v j - w j) ^ 2 * B i j * (v i + w i) ^ 2)) / 2 +
        varianceProfileSquareDifferenceForm B v w := by
    simp only [varianceProfileSquareDifferenceForm, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [varianceProfileQuadraticDistanceSq, hpoint, hswap]
  have hradius : (∑ i, (v i - w i) ^ 2 * varianceProfileRadius B (v + w) i ^ 2) =
      ∑ i, ∑ j, (v i - w i) ^ 2 * B i j * (v j + w j) ^ 2 := by
    simp only [varianceProfileRadius_sq B hB, Finset.mul_sum, Pi.add_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hradius]
  ring

/-- The variance-profile quadratic metric is controlled by the nonlinear
Euclidean deformation, with the exact negative quadratic correction. This
is the gamma-one case of van Handel's Gaussian increment inequality. -/
theorem varianceProfileQuadraticDistanceSq_le_deformation
    (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j) (hsymm : B.IsSymm) (v w : n → ℝ) :
    varianceProfileQuadraticDistanceSq B v w ≤
      4 * (∑ i, (varianceProfileDeformation B v i - varianceProfileDeformation B w i) ^ 2) -
        varianceProfileSquareDifferenceForm B v w := by
  rw [varianceProfileQuadraticDistanceSq_eq_radius_add_form B hB hsymm]
  exact sum_sq_mul_varianceProfileRadius_add_sq_add_form_le B hB v w

/-- A linear Gaussian probe of the nonlinear deformation is controlled by
the largest weighted row radius. This is the deterministic Cauchy--Schwarz
step used after Gaussian comparison on the Euclidean unit ball. -/
theorem sum_mul_varianceProfileDeformation_le
    (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j) (v g : n → ℝ)
    (hv : ∑ i, v i ^ 2 ≤ 1) (R : ℝ) (hR : 0 ≤ R)
    (hrows : ∀ j, ∑ i, B i j * g i ^ 2 ≤ R ^ 2) :
    ∑ i, g i * varianceProfileDeformation B v i ≤ R := by
  have he : (∑ i, (g i * varianceProfileRadius B v i) ^ 2) ≤ R ^ 2 := by
    simp only [mul_pow, varianceProfileRadius_sq B hB, Finset.mul_sum]
    have heq : (∑ i, ∑ j, g i ^ 2 * (B i j * v j ^ 2)) =
        ∑ j, v j ^ 2 * ∑ i, B i j * g i ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq]
    calc _ ≤ ∑ j, v j ^ 2 * R ^ 2 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hrows j) (sq_nonneg _)
      _ = (∑ j, v j ^ 2) * R ^ 2 := (Finset.sum_mul ..).symm
      _ ≤ R ^ 2 := by nlinarith [sq_nonneg R]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v
    (fun i => g i * varianceProfileRadius B v i)
  have he0 : 0 ≤ ∑ i, (g i * varianceProfileRadius B v i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hprod : (∑ i, v i ^ 2) * (∑ i, (g i * varianceProfileRadius B v i) ^ 2) ≤ R ^ 2 := by
    calc _ ≤ ∑ i, (g i * varianceProfileRadius B v i) ^ 2 := by nlinarith
      _ ≤ R ^ 2 := he
  have heq : (∑ i, g i * varianceProfileDeformation B v i) =
      ∑ i, v i * (g i * varianceProfileRadius B v i) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [varianceProfileDeformation]
    ring
  rw [heq]
  nlinarith [hcs.trans hprod]

end NLAlib
