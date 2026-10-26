import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianGramWick
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Symmetric Gaussian matrices with a variance profile

The lower-triangular entries of a genuine standard Gaussian matrix supply the
independent coordinates. Each lower entry is multiplied by the corresponding
profile coefficient and copied to its symmetric upper entry. The unused upper
Gaussian coordinates do not affect the resulting matrix.

This module proves the actual ensemble's entry moments and exact Wick
expansion. It supplies the Gaussian model for the heterogeneous Schatten
moment and row-comparison results of Latała–van Handel–Youssef,
arXiv:1711.00807v2, Theorem 1.1 and Corollary 1.4.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- The symmetric variance-profile Gaussian construction. The entry in
position `(i,j)` uses the Gaussian coordinate `(max i j,min i j)` and the
profile at that lower-triangular position. For a symmetric profile this
coefficient is exactly `b i j`. -/
def symmetricGaussianMatrix (b G : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => b (max i j) (min i j) * G (max i j) (min i j)

omit [Fintype n] in
/-- The symmetric Gaussian construction is pointwise symmetric for every
profile, since both entries use the same lower-triangular coordinate. -/
theorem symmetricGaussianMatrix_isSymm (b G : Matrix n n ℝ) :
    (symmetricGaussianMatrix b G).IsSymm := by
  ext i j
  simp only [symmetricGaussianMatrix, Matrix.transpose_apply, Matrix.of_apply,
    max_comm j i, min_comm j i]

omit [Fintype n] in
/-- The ensemble map is measurable in the genuine Gaussian matrix sample. -/
theorem measurable_symmetricGaussianMatrix (b : Matrix n n ℝ) :
    Measurable (symmetricGaussianMatrix b) := by
  apply Matrix.measurable_iff_entries.mpr
  intro i j
  exact measurable_const.mul (Matrix.measurable_entry (max i j) (min i j))

omit [Fintype n] in
/-- A symmetric profile has its original coefficient at every copied entry. -/
theorem symmetricGaussianMatrix_apply_of_isSymm (b : Matrix n n ℝ) (hb : b.IsSymm)
    (G : Matrix n n ℝ) (i j : n) :
    symmetricGaussianMatrix b G i j = b i j * G (max i j) (min i j) := by
  by_cases hij : i ≤ j
  · simp only [symmetricGaussianMatrix, Matrix.of_apply, max_eq_right hij,
      min_eq_left hij, hb.apply i j]
  · simp only [symmetricGaussianMatrix, Matrix.of_apply, max_eq_left (le_of_not_ge hij),
      min_eq_right (le_of_not_ge hij)]

/-- Every entry of the symmetric ensemble has all finite absolute moments. -/
theorem memLp_symmetricGaussianMatrix_entry (b : Matrix n n ℝ) (i j : n)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun G => symmetricGaussianMatrix b G i j) p (gaussianMatrix n n) :=
  (memLp_gaussianMatrix_entry (max i j) (min i j) p hp).const_mul _

/-- Every entry of the symmetric Gaussian ensemble is centered. -/
theorem integral_symmetricGaussianMatrix_entry (b : Matrix n n ℝ) (i j : n) :
    (∫ G, symmetricGaussianMatrix b G i j ∂gaussianMatrix n n) = 0 := by
  unfold symmetricGaussianMatrix
  simp only [Matrix.of_apply, integral_const_mul, integral_gaussianMatrix_entry_eq_zero,
    mul_zero]

/-- The variance of a symmetric-profile Gaussian entry is the square of
the specified profile coefficient. -/
theorem integral_symmetricGaussianMatrix_entry_sq
    (b : Matrix n n ℝ) (hb : b.IsSymm) (i j : n) :
    (∫ G, symmetricGaussianMatrix b G i j ^ 2 ∂gaussianMatrix n n) = b i j ^ 2 := by
  simp_rw [symmetricGaussianMatrix_apply_of_isSymm b hb, mul_pow]
  rw [integral_const_mul, integral_gaussianMatrix_entry_sq_eq_one, mul_one]

/-- Any finite product of entries of the actual symmetric ensemble is
integrable, including products with repeated coordinates. -/
theorem integrable_prod_symmetricGaussianMatrix_entry {k : ℕ}
    (b : Matrix n n ℝ) (idx : Fin k → n × n) :
    Integrable (fun G => ∏ r, symmetricGaussianMatrix b G (idx r).1 (idx r).2)
      (gaussianMatrix n n) :=
  integrable_prod_gaussianMatrix_entry_weighted b
    (fun r => (max (idx r).1 (idx r).2, min (idx r).1 (idx r).2))

/-- The actual symmetric Gaussian ensemble has the exact Wick pairing
expansion. Two entry occurrences have nonzero covariance precisely when
their canonical lower-triangular coordinates agree. -/
theorem integral_prod_symmetricGaussianMatrix_entry_eq_sum_pairings {k : ℕ}
    (b : Matrix n n ℝ) (idx : Fin k → n × n) :
    (∫ G, ∏ r, symmetricGaussianMatrix b G (idx r).1 (idx r).2 ∂gaussianMatrix n n) =
      ∑ π : GaussianPairings k, gaussianPairingWeight
        (fun r s =>
          if (max (idx r).1 (idx r).2, min (idx r).1 (idx r).2) =
              (max (idx s).1 (idx s).2, min (idx s).1 (idx s).2)
          then b (max (idx r).1 (idx r).2) (min (idx r).1 (idx r).2) ^ 2 else 0) π :=
  integral_prod_gaussianMatrix_entry_weighted_eq_sum_pairings b
    (fun r => (max (idx r).1 (idx r).2, min (idx r).1 (idx r).2))

/-- Every positive trace power of the actual symmetric Gaussian ensemble
is integrable, by its exact finite cycle expansion and Gaussian moments. -/
theorem integrable_trace_symmetricGaussianMatrix_pow
    (b : Matrix n n ℝ) (k : ℕ) :
    Integrable (fun G => ((symmetricGaussianMatrix b G) ^ (k + 1)).trace)
      (gaussianMatrix n n) := by
  have htrace (G : Matrix n n ℝ) :
      ((symmetricGaussianMatrix b G) ^ (k + 1)).trace =
        ∑ x : Fin (k + 1) → n, ∏ r,
          symmetricGaussianMatrix b G (x r) (x (finRotate (k + 1) r)) := by
    have hh := Matrix.trace_list_ofFn_prod_eq_sum_cyclic
      (fun _ : Fin (k + 1) => symmetricGaussianMatrix b G)
    simpa only [List.ofFn_const, List.prod_replicate] using hh
  simp_rw [htrace]
  exact integrable_finsetSum _ fun x _ =>
    integrable_prod_symmetricGaussianMatrix_entry b (fun r => (x r, x (finRotate (k + 1) r)))

/-- The positive trace moments of the actual symmetric Gaussian ensemble
are exactly the finite cycle sum of their Wick pairing weights. -/
theorem integral_trace_symmetricGaussianMatrix_pow_eq_sum_pairings
    (b : Matrix n n ℝ) (k : ℕ) :
    (∫ G, ((symmetricGaussianMatrix b G) ^ (k + 1)).trace ∂gaussianMatrix n n) =
      ∑ x : Fin (k + 1) → n, ∑ π : GaussianPairings (k + 1),
        gaussianPairingWeight (fun r s =>
          if (max (x r) (x (finRotate (k + 1) r)), min (x r) (x (finRotate (k + 1) r))) =
              (max (x s) (x (finRotate (k + 1) s)), min (x s) (x (finRotate (k + 1) s)))
          then b (max (x r) (x (finRotate (k + 1) r)))
            (min (x r) (x (finRotate (k + 1) r))) ^ 2 else 0) π := by
  have htrace (G : Matrix n n ℝ) := Matrix.trace_list_ofFn_prod_eq_sum_cyclic
    (fun _ : Fin (k + 1) => symmetricGaussianMatrix b G)
  have htrace' (G : Matrix n n ℝ) :
      ((symmetricGaussianMatrix b G) ^ (k + 1)).trace =
        ∑ x : Fin (k + 1) → n, ∏ r,
          symmetricGaussianMatrix b G (x r) (x (finRotate (k + 1) r)) := by
    simpa only [List.ofFn_const, List.prod_replicate] using htrace G
  simp_rw [htrace']
  rw [integral_finsetSum _ (fun x _ =>
    integrable_prod_symmetricGaussianMatrix_entry b (fun r => (x r, x (finRotate (k + 1) r))))]
  apply Finset.sum_congr rfl
  intro x _
  exact integral_prod_symmetricGaussianMatrix_entry_eq_sum_pairings b
    (fun r => (x r, x (finRotate (k + 1) r)))

end NLAlib
