import NLAlib.Matrix.Inequalities.KyFan
import NLAlib.Matrix.Inequalities.MajorizationProperties
/-!
# Leading singular-vector frames and matched truncations

First-column selection in an actual SVD gives orthonormal paired singular
frames. Their projectors produce the truncation from that same SVD, including
singular-value ties. Source: Wedin (1972), Section 3; supports `wedin-sin-theta`.
-/
noncomputable section
open scoped Matrix
namespace NLAlib

/-- Select the first `k` columns of a matrix with `n` ordered columns.
Wedin (1972), leading singular-frame convention; zero columns are allowed. -/
def headColumns {m : Type*} {n k : ℕ} (Q : Matrix m (Fin n) ℝ) (hk : k ≤ n) :
    Matrix m (Fin k) ℝ := Q.submatrix id (Fin.castLE hk)

/-- First-column selection preserves orthonormality. Wedin (1972), Section 3. -/
theorem hasOrthonormalCols_headColumns {m : Type*} [Fintype m] {n k : ℕ}
    {Q : Matrix m (Fin n) ℝ} (hQ : HasOrthonormalCols Q) (hk : k ≤ n) :
    HasOrthonormalCols (headColumns Q hk) :=
  hQ.submatrix_cols (Fin.castLEEmb hk)

/-- The head-column projector is the full frame with a diagonal prefix selector.
Wedin (1972), Section 3; this identity does not require an orthonormal frame. -/
theorem headColumns_mul_transpose {m : Type*} {n k : ℕ} (Q : Matrix m (Fin n) ℝ)
    (hk : k ≤ n) :
    headColumns Q hk * (headColumns Q hk)ᵀ =
      Q * Matrix.diagonal (fun i : Fin n => if (i : ℕ) < k then (1 : ℝ) else 0) * Qᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, headColumns, Matrix.submatrix_apply,
    id_eq]
  have hdiag (l : Fin n) :
      (∑ a : Fin n, Q i a * (Matrix.diagonal (fun b : Fin n => if (b : ℕ) < k then (1 : ℝ) else 0)) a l) =
        Q i l * (if (l : ℕ) < k then (1 : ℝ) else 0) := by
    exact Matrix.mul_diagonal _ Q i l
  simp_rw [hdiag]
  rw [← sum_fin_ite_lt_eq_sum_castLE hk (fun l : Fin n => Q i l * Q j l)]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> ring

private theorem diagonal_prefix_mul_rectDiag {m n k : ℕ} (s : ℕ → ℝ) :
    (Matrix.diagonal (fun i : Fin m => if (i : ℕ) < k then (1 : ℝ) else 0)) *
      (rectDiag s : Matrix (Fin m) (Fin n) ℝ) =
        rectDiag (fun i => if i < k then s i else 0) := by
  ext i j
  simp only [Matrix.diagonal_mul, rectDiag_apply]
  split_ifs <;> ring

private theorem rectDiag_mul_diagonal_prefix {m n k : ℕ} (s : ℕ → ℝ) :
    (rectDiag s : Matrix (Fin m) (Fin n) ℝ) *
      (Matrix.diagonal (fun j : Fin n => if (j : ℕ) < k then (1 : ℝ) else 0)) =
        rectDiag (fun i => if i < k then s i else 0) := by
  ext i j
  simp only [Matrix.mul_diagonal, rectDiag_apply]
  by_cases hij : (i : ℕ) = j
  · simp only [if_pos hij]
    rw [hij]
    split_ifs <;> ring
  · simp [hij]

namespace IsSVD
variable {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
  {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}

/-- Transposing an actual real SVD exchanges its paired orthogonal frames.
Horn–Johnson 2013, Section 2.6; Wedin frame helper. -/
theorem transpose (h : IsSVD A U V) : IsSVD Aᵀ V U := by
  refine ⟨h.transpose_mul_right, h.transpose_mul_left, ?_⟩
  rw [singularValues_transpose]
  exact h.transpose_eq

/-- The actual leading right singular frame maps to the leading left frame
through its ordered diagonal singular coefficient. Wedin (1972), Section 3. -/
theorem mul_headColumns (h : IsSVD A U V) (hkm : k ≤ m) (hkn : k ≤ n) :
    A * headColumns V hkn = headColumns U hkm *
      Matrix.diagonal (fun i : Fin k => singularValues A i) := by
  have hv := congrArg (fun M : Matrix (Fin m) (Fin n) ℝ =>
    M.submatrix id (Fin.castLE hkn)) h.mul_right
  have hmul : A * headColumns V hkn = (A * V).submatrix id (Fin.castLE hkn) := by
    simpa only [headColumns, Equiv.coe_refl, Matrix.submatrix_id_id] using
      Matrix.submatrix_mul_equiv A V (id : Fin m → Fin m) (Equiv.refl (Fin n)) (Fin.castLE hkn)
  have heq : A * headColumns V hkn = (U * (rectDiag (singularValues A) : Matrix (Fin m) (Fin n) ℝ)).submatrix id
      (Fin.castLE hkn) := hmul.trans hv
  rw [heq]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, rectDiag_apply, headColumns, Matrix.submatrix_apply, id_eq, Fin.val_castLE]
  rw [Finset.sum_eq_single (Fin.castLE hkm j)]
  · simp only [Fin.val_castLE, ite_true]
  · intro l _ hl
    have hlv : (l : ℕ) ≠ j := fun he => hl (Fin.ext (by simpa only [Fin.val_castLE] using he))
    rw [if_neg hlv, mul_zero]
  · simp

/-- The actual leading left singular frame satisfies the paired transpose
singular equation. Wedin (1972), Section 3. -/
theorem transpose_mul_headColumns (h : IsSVD A U V) (hkm : k ≤ m) (hkn : k ≤ n) :
    Aᵀ * headColumns U hkm = headColumns V hkn *
      Matrix.diagonal (fun i : Fin k => singularValues A i) := by
  simpa only [singularValues_transpose] using h.transpose.mul_headColumns hkn hkm

/-- The left leading-frame projector produces the truncation from the same SVD.
Wedin (1972), Section 3; the witness matching matters at singular-value ties. -/
theorem headColumns_projector_mul (h : IsSVD A U V) (hkm : k ≤ m) :
    (headColumns U hkm * (headColumns U hkm)ᵀ) * A = h.truncatedMatrix k := by
  rw [headColumns_mul_transpose]
  conv_lhs => rw [h.eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᵀ U, h.transpose_mul_left, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _) (rectDiag _), diagonal_prefix_mul_rectDiag]
  simp only [truncatedMatrix, Matrix.mul_assoc]

/-- The right leading-frame projector gives the same matched truncation.
Wedin (1972), Section 3; all rectangular null directions remain in the tail. -/
theorem mul_headColumns_projector (h : IsSVD A U V) (hkn : k ≤ n) :
    A * (headColumns V hkn * (headColumns V hkn)ᵀ) = h.truncatedMatrix k := by
  rw [headColumns_mul_transpose]
  conv_lhs => rw [h.eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᵀ V, h.transpose_mul_right, Matrix.one_mul,
    ← Matrix.mul_assoc (rectDiag _) (Matrix.diagonal _), rectDiag_mul_diagonal_prefix]
  simp only [truncatedMatrix, Matrix.mul_assoc]

/-- The left leading-frame residual is exactly the matched SVD tail.
Wedin (1972), Section 3. -/
theorem residual_headColumns_eq_sub_truncatedMatrix (h : IsSVD A U V) (hkm : k ≤ m) :
    residual (headColumns U hkm) A = A - h.truncatedMatrix k := by
  rw [residual, ← Matrix.mul_assoc, h.headColumns_projector_mul hkm]

/-- The right leading-frame residual of the transpose is the transposed tail.
Wedin (1972), Section 3. -/
theorem residual_headColumns_transpose_eq_sub_truncatedMatrix_transpose
    (h : IsSVD A U V) (hkn : k ≤ n) :
    residual (headColumns V hkn) Aᵀ = (A - h.truncatedMatrix k)ᵀ := by
  have hp := congrArg Matrix.transpose (h.mul_headColumns_projector hkn)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at hp
  rw [residual, ← Matrix.mul_assoc, hp, Matrix.transpose_sub]

end IsSVD
end NLAlib
