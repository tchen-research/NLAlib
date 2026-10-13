import NLAlib.Matrix.Inequalities.HadamardDeterminant
/-!
# Column Hadamard determinant inequality

The PSD Gram inequality gives the product of Euclidean column lengths.
Equality means orthogonal columns or a zero column, including singular
and empty matrices. Source: Horn--Johnson (2013), Corollary 7.8.3;
atlas `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Absolute determinant is bounded by the product of Euclidean column
lengths, with equality exactly for mutually orthogonal columns or a zero
column. Horn--Johnson (2013), Corollary 7.8.3. -/
private theorem abs_det_le_prod_column_norm_and_eq_iff_aux (B : Matrix n n ℝ) :
    |B.det| ≤ ∏ i, ‖(WithLp.toLp 2 (B.col i) : EuclideanSpace ℝ n)‖ ∧
    (|B.det| = (∏ i, ‖(WithLp.toLp 2 (B.col i) : EuclideanSpace ℝ n)‖) ↔
      B.HasOrthogonalCols ∨ ∃ i, B.col i = 0) := by
  let G := Bᵀ * B
  let p := ∏ i, ‖(WithLp.toLp 2 (B.col i) : EuclideanSpace ℝ n)‖
  have hG : G.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self B
  have hp : 0 ≤ p := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hdiag (i : n) : G i i = ‖(WithLp.toLp 2 (B.col i) : EuclideanSpace ℝ n)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [G, Matrix.mul_apply, Matrix.transpose_apply, Matrix.col_apply, sq]
  have hdet : G.det = |B.det| ^ 2 := by
    dsimp only [G]
    rw [Matrix.det_mul, Matrix.det_transpose, sq_abs, sq]
  have hprod : (∏ i, G i i) = p ^ 2 := by
    simp only [hdiag]
    exact Finset.prod_pow Finset.univ 2 (fun i => ‖(WithLp.toLp 2 (B.col i) : EuclideanSpace ℝ n)‖)
  have hle := det_le_prod_diag_of_posSemidef hG
  rw [hdet, hprod] at hle
  refine ⟨?_, ?_⟩
  · change |B.det| ≤ p
    nlinarith [abs_nonneg B.det]
  · have heq : |B.det| = p ↔ G.det = ∏ i, G i i := by
      rw [hdet, hprod]
      constructor
      · intro h; rw [h]
      · intro h; nlinarith [abs_nonneg B.det]
    rw [heq, det_eq_prod_diag_iff_of_posSemidef hG]
    apply or_congr
    · exact Matrix.transpose_mul_self_isDiag_iff_hasOrthogonalCols
    · apply exists_congr
      intro i
      rw [hdiag]
      simp

/-- **Hadamard's inequality.** `|det B| ≤ ∏ᵢ ‖bᵢ‖` (Euclidean column lengths). Horn–Johnson 2013, Corollary 7.8.3.
atlas: hadamard-fischer-inequalities (partial) -/
theorem abs_det_le_prod_column_norm (B : Matrix n n ℝ) :
    |B.det| ≤ ∏ i, ‖(WithLp.toLp 2 (B.col i) : EuclideanSpace ℝ n)‖ :=
  (abs_det_le_prod_column_norm_and_eq_iff_aux B).1

/-- Equality in Hadamard's inequality holds exactly for mutually orthogonal columns or a zero column. Horn–Johnson 2013, Corollary 7.8.3.
atlas: hadamard-fischer-inequalities (partial) -/
theorem abs_det_eq_prod_column_norm_iff (B : Matrix n n ℝ) :
    |B.det| = (∏ i, ‖(WithLp.toLp 2 (B.col i) : EuclideanSpace ℝ n)‖) ↔
      B.HasOrthogonalCols ∨ ∃ i, B.col i = 0 :=
  (abs_det_le_prod_column_norm_and_eq_iff_aux B).2

end NLAlib
