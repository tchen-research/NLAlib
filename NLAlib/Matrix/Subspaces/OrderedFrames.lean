import NLAlib.Matrix.Perturbation.SingularFrames

/-!
# Leading and trailing columns of an ordered orthogonal frame

The complementary frames retain the original ordering. These identities support
simultaneous iteration and QR convergence without imposing invertibility on the
smallest eigenvalue.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The columns after a leading prefix, in their original order. -/
def tailColumns {m : Type*} {n k : ℕ} (Q : Matrix m (Fin n) ℝ) (hk : k ≤ n) :
    Matrix m (Fin (n - k)) ℝ :=
  Q.submatrix id (fun i => ⟨k + i.val, by omega⟩)

/-- Trailing-column selection preserves orthonormality, including empty tails. -/
theorem hasOrthonormalCols_tailColumns {m : Type*} [Fintype m] {n k : ℕ}
    {Q : Matrix m (Fin n) ℝ} (hQ : HasOrthonormalCols Q) (hk : k ≤ n) :
    HasOrthonormalCols (tailColumns Q hk) := by
  apply hQ.submatrix_cols
    (⟨fun i : Fin (n-k) => ⟨k+i.val, by omega⟩, fun i j hij => Fin.ext (by
      have hv := congrArg Fin.val hij
      simp only at hv
      omega)⟩ : Fin (n-k) ↪ Fin n)

/-- The head and tail projectors partition the full frame projector. -/
theorem headColumns_projector_add_tailColumns_projector {m : Type*} {n k : ℕ}
    (Q : Matrix m (Fin n) ℝ) (hk : k ≤ n) :
    headColumns Q hk * (headColumns Q hk)ᵀ + tailColumns Q hk * (tailColumns Q hk)ᵀ =
      Q * Qᵀ := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n-k, by omega⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    headColumns, tailColumns, Matrix.submatrix_apply, id_eq]
  rw [Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · rfl
  · exact Fintype.sum_equiv (finCongr (by omega)) _ _ (fun i => rfl)

/-- Selecting leading columns commutes with left multiplication. -/
theorem mul_headColumns {m r : Type*} [Fintype r] {n k : ℕ}
    (A : Matrix m r ℝ) (Q : Matrix r (Fin n) ℝ) (hk : k ≤ n) :
    A * headColumns Q hk = headColumns (A * Q) hk := by
  ext i j
  rfl

/-- Selecting trailing columns commutes with left multiplication. -/
theorem mul_tailColumns {m r : Type*} [Fintype r] {n k : ℕ}
    (A : Matrix m r ℝ) (Q : Matrix r (Fin n) ℝ) (hk : k ≤ n) :
    A * tailColumns Q hk = tailColumns (A * Q) hk := by
  ext i j
  rfl

/-- Selecting the head of a diagonal right action selects the corresponding entries. -/
theorem headColumns_mul_diagonal {m : Type*} {n k : ℕ}
    (Q : Matrix m (Fin n) ℝ) (d : Fin n → ℝ) (hk : k ≤ n) :
    headColumns (Q * Matrix.diagonal d) hk =
      headColumns Q hk * Matrix.diagonal (fun i => d (Fin.castLE hk i)) := by
  ext i j
  simp only [headColumns, Matrix.submatrix_apply, Matrix.mul_diagonal, id_eq]

/-- Selecting the tail of a diagonal right action selects the corresponding entries. -/
theorem tailColumns_mul_diagonal {m : Type*} {n k : ℕ}
    (Q : Matrix m (Fin n) ℝ) (d : Fin n → ℝ) (hk : k ≤ n) :
    tailColumns (Q * Matrix.diagonal d) hk =
      tailColumns Q hk * Matrix.diagonal (fun i => d ⟨k+i.val, by omega⟩) := by
  ext i j
  simp only [tailColumns, Matrix.submatrix_apply, Matrix.mul_diagonal, id_eq]

end NLAlib
