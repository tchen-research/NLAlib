import NLAlib.Matrix.Spectral.SingularValueSpectrum
import NLAlib.Matrix.Basic.Dilation

/-!
# Real symmetric dilation and its orthogonal diagonalization

The real dilation `dilation A = [0 A; Aᵀ 0]` (`Matrix/Basic/Dilation`) has the paired singular
spectrum,
including every rectangular padded zero. Source: Bhatia 1997, Section III.4;
the matrix-toolkit operator manuscript, dilation argument for `lidskii`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Mixed rectangular diagonal multiplication gives the coordinate products,
with zeros beyond the intermediate dimension. Horn–Johnson 2013, Section 2.6. -/
theorem rectDiag_mul_rectDiag {m n p : ℕ} (s t : ℕ → ℝ) :
    (rectDiag s : Matrix (Fin m) (Fin n) ℝ) *
      (rectDiag t : Matrix (Fin n) (Fin p) ℝ) =
      rectDiag (fun k => if k < n then s k * t k else 0) := by
  ext i j
  simp only [Matrix.mul_apply, rectDiag_apply]
  by_cases hi : (i : ℕ) < n
  · rw [Finset.sum_eq_single ⟨i, hi⟩]
    · split_ifs <;> simp_all
    · intro l _ hl
      rw [if_neg (fun h => hl (Fin.ext h.symm)), zero_mul]
    · simp
  · rw [Finset.sum_eq_zero]
    · split_ifs <;> simp_all
    · intro l _
      rw [if_neg (fun (h : (i : ℕ) = l) => hi (h.symm ▸ l.isLt)), zero_mul]

private def pairRotation (m n : ℕ) (r : ℝ) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then r else 1)
    (rectDiag fun _ => r) (rectDiag fun _ => r)
    (Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then -r else 1)

private theorem pairRotation_transpose (m n : ℕ) (r : ℝ) :
    (pairRotation m n r)ᵀ = pairRotation m n r := by
  simp [pairRotation, Matrix.fromBlocks_transpose, transpose_rectDiag]

private theorem pairRotation_orthogonal (m n : ℕ) (r : ℝ) (hr : r ^ 2 + r ^ 2 = 1) :
    (pairRotation m n r)ᵀ * pairRotation m n r = 1 := by
  rw [pairRotation_transpose, pairRotation, Matrix.fromBlocks_multiply]
  have htop :
      (Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then r else 1) *
        (Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then r else 1) +
      (rectDiag (fun _ => r) : Matrix (Fin m) (Fin n) ℝ) * rectDiag (fun _ => r) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, rectDiag_mul_rectDiag]
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_apply, rectDiag_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      split_ifs <;> nlinarith
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, hij']
  have hbottom :
      (rectDiag (fun _ => r) : Matrix (Fin n) (Fin m) ℝ) * rectDiag (fun _ => r) +
      (Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then -r else 1) *
        (Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then -r else 1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, rectDiag_mul_rectDiag]
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_apply, rectDiag_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      split_ifs <;> nlinarith
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, hij']
  have hoff :
      (Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then r else 1) *
        (rectDiag (fun _ => r) : Matrix (Fin m) (Fin n) ℝ) +
      (rectDiag (fun _ => r) : Matrix (Fin m) (Fin n) ℝ) *
        (Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then -r else 1) = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, rectDiag_apply,
      Matrix.zero_apply]
    by_cases hij : (i : ℕ) = j
    · have hin : (i : ℕ) < n := hij.symm ▸ j.isLt
      have hjm : (j : ℕ) < m := hij ▸ i.isLt
      simp only [if_pos hij, if_pos hin, if_pos hjm]
      ring
    · simp [hij]
  have hoff' := congrArg Matrix.transpose hoff
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.diagonal_transpose,
    transpose_rectDiag, Matrix.transpose_zero] at hoff'
  rw [htop, hbottom, hoff]
  have hoff'' :
      (rectDiag (fun _ => r) : Matrix (Fin n) (Fin m) ℝ) *
        (Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then r else 1) +
      (Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then -r else 1) *
        (rectDiag (fun _ => r) : Matrix (Fin n) (Fin m) ℝ) = 0 := by
    simpa only [add_comm] using hoff'
  rw [hoff'', Matrix.fromBlocks_one]

private theorem rectDiag_dilation_mul_pairRotation {m n : ℕ} (s : ℕ → ℝ)
    (hs : ∀ k, min m n ≤ k → s k = 0) (r : ℝ) :
    dilation (rectDiag s : Matrix (Fin m) (Fin n) ℝ) * pairRotation m n r =
      pairRotation m n r * Matrix.diagonal (Sum.elim (fun i : Fin m => s i)
        (fun j : Fin n => -s j)) := by
  rw [dilation, Matrix.conjTranspose_eq_transpose_of_trivial, pairRotation, transpose_rectDiag,
    ← Matrix.fromBlocks_diagonal,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  congr 1
  · rw [rectDiag_mul_rectDiag]
    ext i j
    simp only [rectDiag_apply, Matrix.diagonal_mul, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      by_cases hi : (i : ℕ) < n
      · simp [hi, mul_comm]
      · simp [hi, hs i (by omega)]
    · simp [hij, show (i : ℕ) ≠ j from fun h => hij (Fin.ext h)]
  · ext i j
    simp only [Matrix.mul_diagonal, rectDiag_apply]
    by_cases hij : (i : ℕ) = j
    · have hjm : (j : ℕ) < m := hij ▸ i.isLt
      simp only [if_pos hij, if_pos hjm]
      rw [hij]
      ring
    · simp [hij]
  · ext i j
    simp only [Matrix.mul_diagonal, rectDiag_apply]
    by_cases hij : (i : ℕ) = j
    · have hjn : (j : ℕ) < n := hij ▸ i.isLt
      simp only [if_pos hij, if_pos hjn]
      rw [hij]
      ring
    · simp [hij]
  · rw [rectDiag_mul_rectDiag]
    ext i j
    simp only [rectDiag_apply, Matrix.diagonal_mul, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      by_cases hi : (i : ℕ) < m
      · simp [hi, mul_comm]
      · simp [hi, hs i (by omega)]
    · simp [hij, show (i : ℕ) ≠ j from fun h => hij (Fin.ext h)]

/-- Every real rectangular dilation admits an orthogonal diagonalization with
positive row-side and negative column-side padded singular values.
Bhatia 1997, Section III.4; empty dimensions and repeated zeros are included. -/
theorem exists_dilation_orthogonal_diagonalization {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ P : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ, Pᵀ * P = 1 ∧
      dilation A = P * Matrix.diagonal (Sum.elim
        (fun i : Fin m => singularValues A i) (fun j : Fin n => -singularValues A j)) * Pᵀ := by
  obtain ⟨U, V, h⟩ := exists_isSVD A
  let W := Matrix.fromBlocks U 0 0 V
  let r := Real.sqrt (1 / 2 : ℝ)
  let R := pairRotation m n r
  have hr : r ^ 2 + r ^ 2 = 1 := by
    have hsq : r ^ 2 = (1 / 2 : ℝ) := Real.sq_sqrt (by positivity)
    rw [hsq]
    norm_num
  have hR : Rᵀ * R = 1 := pairRotation_orthogonal m n r hr
  have hRR : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have hW : Wᵀ * W = 1 := by
    simp only [W, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      h.transpose_mul_left, h.transpose_mul_right, Matrix.fromBlocks_one]
  have hA : dilation A = W * dilation (rectDiag (singularValues A)) * Wᵀ := by
    simp only [W, dilation, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.fromBlocks_transpose, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [← h.eq, h.transpose_eq, transpose_rectDiag]
  refine ⟨W * R, ?_, ?_⟩
  · rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᵀ, hW, Matrix.one_mul, hR]
  · have hrot := rectDiag_dilation_mul_pairRotation (singularValues A)
      (fun k hk => singularValues_eq_zero_of_min_le A hk) r
    have hdiag : dilation (rectDiag (singularValues A) : Matrix (Fin m) (Fin n) ℝ) =
        R * Matrix.diagonal (Sum.elim (fun i : Fin m => singularValues A i)
          (fun j : Fin n => -singularValues A j)) * Rᵀ := by
      rw [← hrot, Matrix.mul_assoc, hRR, Matrix.mul_one]
    rw [hA, hdiag, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

end NLAlib
