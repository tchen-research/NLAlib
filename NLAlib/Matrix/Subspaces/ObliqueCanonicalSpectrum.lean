import NLAlib.Matrix.Spectral.SingularValueInvariance
import NLAlib.Matrix.Inequalities.KyFanNorms
/-!
# Singular values of the oblique canonical blocks

The range singular values of `[I diag(t); 0 0]` are exactly
`sqrt(1+t_i²)` in their actual order; the other values are zero.
Horn–Johnson 2013, Corollary 3.4.3.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- The actual singular values of the oblique block matrix are
`sqrt(1+t_i²)` on its range block and zero afterwards. All multiplicities,
zero coefficients and empty blocks are included. Horn–Johnson 2013,
Corollary 3.4.3.3; supports `cs-decomposition`. -/
theorem singularValues_oblique_canonical {r s : ℕ} (t : ℕ → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht : Antitone t)
    (hz : ∀ i, min r s ≤ i → t i = 0) (k : ℕ) :
    singularValues (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ)
      (rectDiag t : Matrix (Fin r) (Fin s) ℝ) 0
      (0 : Matrix (Fin s) (Fin s) ℝ)) k =
      if k < r then Real.sqrt (1 + t k ^ 2) else 0 := by
  let N := Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ)
    (rectDiag t : Matrix (Fin r) (Fin s) ℝ) 0 (0 : Matrix (Fin s) (Fin s) ℝ)
  let D := Matrix.fromBlocks (Matrix.diagonal (fun i : Fin r => Real.sqrt (1 + t i ^ 2)))
    (0 : Matrix (Fin r) (Fin s) ℝ) 0 (0 : Matrix (Fin s) (Fin s) ℝ)
  let d := fun i : ℕ => if i < r then Real.sqrt (1 + t i ^ 2) else 0
  have hd0 : ∀ i, 0 ≤ d i := by intro i; dsimp [d]; split_ifs <;> positivity
  have hd : Antitone d := by
    intro i j hij
    dsimp [d]
    split_ifs with hj hi hi
    · exact Real.sqrt_le_sqrt (by nlinarith [ht hij, ht0 i, ht0 j])
    · omega
    · positivity
    · rfl
  have hGram : N * Nᵀ = D * Dᵀ := by
    dsimp [N, D]
    simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.diagonal_transpose, Matrix.fromBlocks_multiply,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, Matrix.diagonal_mul_diagonal,
      show (rectDiag t : Matrix (Fin r) (Fin s) ℝ) * (rectDiag t)ᵀ =
        Matrix.diagonal (fun i : Fin r => if (i : ℕ) < s then t i ^ 2 else 0) from
        rectDiag_mul_conjTranspose_rectDiag t]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
      rw [Real.mul_self_sqrt (by positivity)]
      by_cases hi : (i : ℕ) < s
      · simp [hi]
      · rw [if_neg hi, hz i (min_le_right r s |>.trans (Nat.le_of_not_gt hi))]
        norm_num
    · simp [Matrix.add_apply, hij]
  have hND : singularValues N k = singularValues D k := by
    rw [← singularValues_transpose N, ← singularValues_transpose D]
    apply singularValues_eq_of_gram_eq
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hGram
  have hD : D = (rectDiag d : Matrix (Fin (r + s)) (Fin (r + s)) ℝ).reindex
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [D, Matrix.reindex_apply, rectDiag_apply, d,
          Matrix.diagonal_apply, Fin.ext_iff]
      | inr j =>
        have hij : (i : ℕ) ≠ r + j := by omega
        simp [D, Matrix.reindex_apply, rectDiag_apply, hij]
    | inr i =>
      cases j with
      | inl j =>
        have hij : r + (i : ℕ) ≠ j := by omega
        simp [D, Matrix.reindex_apply, rectDiag_apply, hij]
      | inr j =>
        simp [D, Matrix.reindex_apply, rectDiag_apply, d]
  rw [hND, hD, singularValues_reindex]
  change singularValues (rectDiag d : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) k = d k
  by_cases hk : k < r + s
  · exact singularValues_eq_of_eq_mul_rectDiag_mul
      (U := (1 : Matrix (Fin (r + s)) (Fin (r + s)) ℝ))
      (V := (1 : Matrix (Fin (r + s)) (Fin (r + s)) ℝ))
      (by simp) (by simp) hd0 hd (by simp) (by simpa using hk)
  · rw [singularValues_eq_zero_of_width_le _
      (by simpa only [Fintype.card_fin] using Nat.le_of_not_gt hk)]
    simp only [d, if_neg (show ¬k < r by omega)]

end NLAlib
