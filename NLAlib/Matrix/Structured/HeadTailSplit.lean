import NLAlib.Matrix.Norms.SchattenComparison
import NLAlib.Matrix.Norms.SpectralNormBounds
import NLAlib.ForMathlib.Analysis.FiniteHeavySets

/-!
# Finite head and principal-tail matrix split

Removing a principal tail leaves a matrix of rank at most twice the number
of retained head coordinates. Its spectral norm is at most twice the original
norm, so its finite Schatten norm has the expected low-rank bound.
Source: Latała--van Handel--Youssef (2018), Section 3.2, finite-exponent step.
-/

noncomputable section
namespace NLAlib

/-- Coordinate projection onto the first `r` zero-based positions. -/
def headCoordinateProjection (n r : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => if i.val < r then 1 else 0

/-- Coordinate projection onto positions from `r` onward. -/
def tailCoordinateProjection (n r : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => if r ≤ i.val then 1 else 0

/-- The principal tail of a finite matrix. -/
def principalTailPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if r ≤ i.val ∧ r ≤ j.val then A i j else 0

/-- The remainder after removing the principal tail. -/
def headTailRemainder {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := A - principalTailPart A r

/-- A principal tail is exactly its two-sided coordinate compression. -/
theorem principalTailPart_eq_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    principalTailPart A r = tailCoordinateProjection n r * A * tailCoordinateProjection n r := by
  ext i j
  simp only [tailCoordinateProjection, Matrix.mul_diagonal, Matrix.diagonal_mul, principalTailPart]
  split_ifs <;> simp_all

/-- The head remainder factors into two terms through the head projection. -/
theorem headTailRemainder_eq_add_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    headTailRemainder A r = headCoordinateProjection n r * A +
      tailCoordinateProjection n r * A * headCoordinateProjection n r := by
  ext i j
  simp only [headTailRemainder, principalTailPart, Matrix.sub_apply, Matrix.add_apply,
    headCoordinateProjection, tailCoordinateProjection, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp_all <;> omega

/-- The head coordinate projection has rank at most the requested head size,
also when the request exceeds the ambient dimension. -/
theorem rank_headCoordinateProjection_le (n r : ℕ) :
    (headCoordinateProjection n r).rank ≤ r := by
  classical
  rw [headCoordinateProjection, Matrix.rank_diagonal, Fintype.card_subtype]
  have h := Finset.card_filter_le_of_imp_val_lt (fun i : Fin n => i.val < r) (fun _ hi => hi)
  convert h using 1
  congr 1
  ext i
  by_cases hi : i.val < r <;> simp [hi]

/-- The actual head remainder has rank at most twice the head size. -/
theorem rank_headTailRemainder_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    (headTailRemainder A r).rank ≤ 2 * r := by
  rw [headTailRemainder_eq_add_mul]
  have hhead := rank_headCoordinateProjection_le n r
  exact (rank_add_le _ _).trans (by
    have hleft := Matrix.rank_mul_le_left (headCoordinateProjection n r) A
    have hright := Matrix.rank_mul_le_right (tailCoordinateProjection n r * A)
      (headCoordinateProjection n r)
    omega)

/-- Coordinate tail projections have spectral norm at most one. -/
theorem specNorm_tailCoordinateProjection_le_one (n r : ℕ) :
    specNorm (tailCoordinateProjection n r) ≤ 1 := by
  apply specNorm_diagonal_le (by norm_num)
  intro i
  split_ifs <;> norm_num

/-- The spectral norm decreases under principal-tail compression. -/
theorem specNorm_principalTailPart_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    specNorm (principalTailPart A r) ≤ specNorm A := by
  rw [principalTailPart_eq_mul]
  calc
    _ ≤ specNorm (tailCoordinateProjection n r * A) * specNorm (tailCoordinateProjection n r) :=
      specNorm_mul_le _ _
    _ ≤ (specNorm (tailCoordinateProjection n r) * specNorm A) *
        specNorm (tailCoordinateProjection n r) := mul_le_mul_of_nonneg_right
      (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ ≤ (1 * specNorm A) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (specNorm_tailCoordinateProjection_le_one n r) (specNorm_nonneg A))
      (specNorm_tailCoordinateProjection_le_one n r) (specNorm_nonneg _)
      (by simpa only [one_mul] using specNorm_nonneg A)
    _ = specNorm A := by ring

/-- The head remainder's spectral norm is at most twice the original norm. -/
theorem specNorm_headTailRemainder_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) :
    specNorm (headTailRemainder A r) ≤ 2 * specNorm A := by
  have h := specNorm_sub_le A (principalTailPart A r)
  change specNorm (headTailRemainder A r) ≤ _ at h
  linarith [specNorm_principalTailPart_le A r]

/-- Exact finite head-size loss for every positive real Schatten exponent. -/
theorem schattenNormReal_headTailRemainder_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) {p : ℝ} (hp : 0 < p) :
    schattenNormReal (headTailRemainder A r) p ≤
      (2 * r : ℝ) ^ (1 / p) * (2 * specNorm A) := by
  apply (schattenNormReal_le_rank_rpow_mul_specNorm _ hp).trans
  apply mul_le_mul
  · apply Real.rpow_le_rpow (Nat.cast_nonneg _)
    · exact_mod_cast rank_headTailRemainder_le A r
    · positivity
  · exact specNorm_headTailRemainder_le A r
  · exact specNorm_nonneg _
  · positivity

/-- A principal tail of a symmetric matrix is symmetric. -/
theorem isSymm_principalTailPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (r : ℕ) : (principalTailPart A r).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, principalTailPart, hA.apply i j, and_comm]

end NLAlib
