import NLAlib.Matrix.Perturbation.CoupledNormBounds
/-!
# Coupled rectangular residual norm bounds

A diagonal coefficient bounded below and a rectangular coupling bounded above
produce the exact maximum-operator and paired-Frobenius estimates.
Wedin (1972), Section 3; toolkit derivations, two coupled inequalities.
-/
noncomputable section
open scoped Matrix
namespace NLAlib
variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
  [DecidableEq m] [DecidableEq n] [DecidableEq k]

/-- A nonnegative lower diagonal bound expands Euclidean lengths.
Wedin (1972), diagonal singular coefficient in the coupled residual proof. -/
theorem mulVec_diagonal_sq_ge {t : k → ℝ} {α : ℝ} (hα : 0 ≤ α)
    (ht : ∀ j, α ≤ t j) (x : k → ℝ) :
    α ^ 2 * (x ⬝ᵥ x) ≤ ((Matrix.diagonal t) *ᵥ x) ⬝ᵥ ((Matrix.diagonal t) *ᵥ x) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hs := pow_le_pow_left₀ hα (ht j) 2
  have hx := mul_le_mul_of_nonneg_right hs (sq_nonneg (x j))
  nlinarith

/-- Right multiplication by a diagonal bounded below expands the spectral norm.
Wedin (1972), Section 3; arbitrary finite indices and empty spaces. -/
theorem mul_specNorm_le_specNorm_mul_diagonal {t : k → ℝ} {α : ℝ} (hα : 0 ≤ α)
    (ht : ∀ j, α ≤ t j) (X : Matrix m k ℝ) :
    α * specNorm X ≤ specNorm (X * Matrix.diagonal t) := by
  have h := mul_specNorm_le_specNorm_mul_of_mulVec_sq_le hα
    (mulVec_diagonal_sq_ge hα ht) Xᵀ
  have heq : Matrix.diagonal t * Xᵀ = (X * Matrix.diagonal t)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  rw [heq, specNorm_transpose, specNorm_transpose] at h
  exact h

omit [DecidableEq m] in
/-- The same right diagonal expansion holds in Frobenius norm.
Wedin (1972), Section 3; no nonempty or invertibility premise is added. -/
theorem mul_frobNorm_le_frobNorm_mul_diagonal {t : k → ℝ} {α : ℝ} (hα : 0 ≤ α)
    (ht : ∀ j, α ≤ t j) (X : Matrix m k ℝ) :
    α * frobNorm X ≤ frobNorm (X * Matrix.diagonal t) := by
  have h := mul_frobSq_le_frobSq_mul_of_mulVec_sq_le (mulVec_diagonal_sq_ge hα ht) Xᵀ
  have heq : Matrix.diagonal t * Xᵀ = (X * Matrix.diagonal t)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  rw [heq, frobSq_transpose, frobSq_transpose] at h
  rw [← frobNorm_sq, ← frobNorm_sq, ← mul_pow] at h
  exact le_of_pow_le_pow_left₀ two_ne_zero (frobNorm_nonneg _) h

private theorem coupled_specNorm_component {D : Matrix m n ℝ} {t : k → ℝ}
    {α β : ℝ} (hα : 0 ≤ α) (ht : ∀ j, α ≤ t j) (hD : specNorm D ≤ β)
    (X : Matrix m k ℝ) (Y : Matrix n k ℝ) :
    α * specNorm X ≤ β * specNorm Y + specNorm (D * Y - X * Matrix.diagonal t) := by
  have hlow := mul_specNorm_le_specNorm_mul_diagonal hα ht X
  have heq : X * Matrix.diagonal t = D * Y - (D * Y - X * Matrix.diagonal t) := by abel
  rw [heq] at hlow
  have htri := specNorm_sub_le (D * Y) (D * Y - X * Matrix.diagonal t)
  have hmul := (specNorm_mul_le D Y).trans
    (mul_le_mul_of_nonneg_right hD (specNorm_nonneg Y))
  linarith

omit [DecidableEq m] in
private theorem coupled_frobNorm_component {D : Matrix m n ℝ} {t : k → ℝ}
    {α β : ℝ} (hα : 0 ≤ α) (ht : ∀ j, α ≤ t j) (hD : specNorm D ≤ β)
    (X : Matrix m k ℝ) (Y : Matrix n k ℝ) :
    α * frobNorm X ≤ β * frobNorm Y + frobNorm (D * Y - X * Matrix.diagonal t) := by
  have hlow := mul_frobNorm_le_frobNorm_mul_diagonal hα ht X
  have heq : X * Matrix.diagonal t = D * Y - (D * Y - X * Matrix.diagonal t) := by abel
  rw [heq] at hlow
  have htri := frobNorm_sub_le (D * Y) (D * Y - X * Matrix.diagonal t)
  have hmul := (frobNorm_mul_le_specNorm_mul_frobNorm D Y).trans
    (mul_le_mul_of_nonneg_right hD (frobNorm_nonneg Y))
  linarith

/-- Wedin's two coupled residual equations imply the exact maximum-operator
separation bound. Wedin (1972), Section 3; all rectangular ambient spaces and
empty selected frames are allowed. -/
theorem sub_mul_max_specNorm_le_max_coupled_residual {D : Matrix m n ℝ} {t : k → ℝ}
    {α β : ℝ} (hα : 0 ≤ α) (ht : ∀ j, α ≤ t j) (hD : specNorm D ≤ β)
    (X : Matrix m k ℝ) (Y : Matrix n k ℝ) :
    (α - β) * max (specNorm X) (specNorm Y) ≤
      max (specNorm (D * Y - X * Matrix.diagonal t))
        (specNorm (Dᵀ * X - Y * Matrix.diagonal t)) := by
  apply sub_mul_max_le_max_of_coupled ((specNorm_nonneg D).trans hD)
    (coupled_specNorm_component hα ht hD X Y)
  apply coupled_specNorm_component hα ht _ Y X
  simpa only [specNorm_transpose] using hD

/-- Wedin's coupled residual equations retain constant one for the paired
Frobenius square. Wedin (1972), Section 3; no rank assumptions occur. -/
theorem sub_sq_mul_add_sq_frobNorm_le_add_sq_coupled_residual
    {D : Matrix m n ℝ} {t : k → ℝ} {α β : ℝ}
    (hα : 0 ≤ α) (ht : ∀ j, α ≤ t j) (hD : specNorm D ≤ β) (hδ : 0 ≤ α - β)
    (X : Matrix m k ℝ) (Y : Matrix n k ℝ) :
    (α - β) ^ 2 * (frobNorm X ^ 2 + frobNorm Y ^ 2) ≤
      frobNorm (D * Y - X * Matrix.diagonal t) ^ 2 +
        frobNorm (Dᵀ * X - Y * Matrix.diagonal t) ^ 2 := by
  apply sub_sq_mul_add_sq_le_add_sq_of_coupled hδ ((specNorm_nonneg D).trans hD)
    (frobNorm_nonneg _) (frobNorm_nonneg _) (frobNorm_nonneg _) (frobNorm_nonneg _)
    (coupled_frobNorm_component hα ht hD X Y)
  apply coupled_frobNorm_component hα ht _ Y X
  simpa only [specNorm_transpose] using hD

end NLAlib
