import NLAlib.ForMathlib.Logic.Equiv
import NLAlib.Matrix.MaximumVolumeColumns
import NLAlib.Matrix.MaximumVolumeBudget
import NLAlib.Matrix.OrthogonalSumCompletion

/-!
# Maximum-volume QR blocks and their shared budget

A maximizing independent column selection yields a genuine full orthogonal
factorization with an invertible triangular leading block, entrywise bounded
interpolation, and the exact shared Frobenius budget. Arbitrary finite input
labels and rank endpoints are supported. Gu–Eisenstat 1996, Theorem 3.2.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Maximum volume gives a full orthogonal QR block factorization with an
invertible upper-triangular leading block, interpolation entries bounded by
one, and the joint budget `‖T‖F² + ‖R⁻¹‖F² ‖D‖F² ≤ k(n-k)`.
The requested leading size may be any `k ≤ rank A`, including zero and full
rank. The column equivalence is an actual permutation into the selected and
remaining coordinate blocks. Gu–Eisenstat 1996, Theorem 3.2; derivations
equations alg:rrqr-block through alg:rrqr-budget.
Supports `rank-revealing-qr`. -/
theorem exists_maximum_volume_qr_blocks {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) (hk : k ≤ A.rank) :
    ∃ π : (Fin k ⊕ Fin (Fintype.card n - k)) ≃ n,
    ∃ Q : Matrix m (Fin k ⊕ Fin (Fintype.card m - k)) ℝ,
    ∃ R : Matrix (Fin k) (Fin k) ℝ,
    ∃ T : Matrix (Fin k) (Fin (Fintype.card n - k)) ℝ,
    ∃ D : Matrix (Fin (Fintype.card m - k)) (Fin (Fintype.card n - k)) ℝ,
      HasOrthonormalCols Q ∧ Q * Qᵀ = 1 ∧ IsUnit R ∧ R.IsUpperTriangular ∧
      A.submatrix id π = Q * Matrix.fromBlocks R (R * T) 0 D ∧
      (∀ i j, |T i j| ≤ 1) ∧
      frobSq T + frobSq R⁻¹ * frobSq D ≤ (k : ℝ) * (Fintype.card n - k) := by
  classical
  have hkm : k ≤ Fintype.card m := hk.trans A.rank_le_card_height
  have hkn : k ≤ Fintype.card n := hk.trans A.rank_le_card_width
  obtain ⟨e, hCpos, hMax⟩ := exists_maximum_volume_column_embedding A k hk
  obtain ⟨π, hπ⟩ := exists_equiv_sum_extending_embedding
    (q := Fin (Fintype.card n - k)) e (by simpa using Nat.add_sub_of_le hkn)
  let C := A.submatrix id e
  let B := A.submatrix id (fun j => π (Sum.inr j))
  have hA : A.submatrix id π = Matrix.fromCols C B := by
    ext i j
    cases j with
    | inl j => simp [C, Matrix.submatrix_apply, hπ]
    | inr j => rfl
  obtain ⟨L, R, hL, hUpper, _, hLR⟩ := exists_qr C (by simpa using hkm)
  have hGram : Cᵀ * C = Rᵀ * R := by
    rw [← hLR, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Lᵀ L R, show Lᵀ * L = 1 from hL, Matrix.one_mul]
  have hRdet : IsUnit R.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    change 0 < (Cᵀ * C).det at hCpos
    rw [hGram, Matrix.det_mul, Matrix.det_transpose, hz, zero_mul] at hCpos
    exact lt_irrefl 0 hCpos
  have hR : IsUnit R := (Matrix.isUnit_iff_isUnit_det R).mpr hRdet
  obtain ⟨Q, hQ, hQt, hFirst⟩ := exists_orthogonal_sum_completion
    (q := Fin (Fintype.card m - k)) L hL (by simpa using Nat.add_sub_of_le hkm)
  let K := Q.submatrix id Sum.inr
  have hQform : Q = Matrix.fromCols L K := by
    ext i j
    cases j with
    | inl j => exact congrArg (fun M : Matrix m (Fin k) ℝ => M i j) hFirst
    | inr j => rfl
  have hK : HasOrthonormalCols K := hQ.submatrix_cols ⟨Sum.inr, Sum.inr_injective⟩
  have hCross : Lᵀ * K = 0 := by
    have hh := congrArg Matrix.toBlocks₁₂ hQ
    rw [hQform, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols] at hh
    simpa only [Matrix.toBlocks_fromBlocks₁₂,
      show (1 : Matrix (Fin k ⊕ Fin (Fintype.card m - k))
        (Fin k ⊕ Fin (Fintype.card m - k)) ℝ).toBlocks₁₂ = 0 by
        ext i j; simp [Matrix.toBlocks₁₂]] using hh
  have hComplete : L * Lᵀ + K * Kᵀ = 1 := by
    simpa only [hQform, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using hQt
  let T := R⁻¹ * (Lᵀ * B)
  let D := Kᵀ * B
  have hRT : R * T = Lᵀ * B := by
    dsimp only [T]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv R hRdet, Matrix.one_mul]
  have hCT : C * T = L * (Lᵀ * B) := by rw [← hLR, Matrix.mul_assoc, hRT]
  have hReconstruct : C * T + K * D = B := by
    rw [hCT]
    change L * (Lᵀ * B) + K * (Kᵀ * B) = B
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul,
      hComplete, Matrix.one_mul]
  have hOrth : Cᵀ * (K * D) = 0 := by
    rw [← hLR, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Lᵀ K D, hCross, Matrix.zero_mul, Matrix.mul_zero]
  have hExchange (i : Fin k) (j : Fin (Fintype.card n - k)) :
      ((C.updateCol i ((C * T + K * D).col j))ᵀ *
        C.updateCol i ((C * T + K * D).col j)).det ≤ (Cᵀ * C).det := by
    rw [hReconstruct]
    have heq : C.updateCol i (B.col j) =
        A.submatrix id (Function.update e i (π (Sum.inr j))) := by
      ext a b
      by_cases hb : b = i
      · subst b
        simp [C, B, Matrix.col]
      · simp [C, B, Matrix.updateCol_ne hb, Function.update_of_ne hb]
    rw [heq]
    exact hMax _
  obtain ⟨hEntry, hBudget⟩ := frobSq_add_trace_inv_gram_mul_frobSq_le_of_maximum_volume
    C T (K * D) hCpos hOrth hExchange
  have hInvTrace : (Cᵀ * C)⁻¹.trace = frobSq R⁻¹ := by
    rw [hGram, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
      frobSq, frobInner_eq_trace, Matrix.trace_mul_comm]
  rw [hInvTrace, frobSq_mul_left_of_orthonormal hK] at hBudget
  refine ⟨π, Q, R, T, D, hQ, hQt, hR, hUpper, ?_, hEntry, ?_⟩
  · rw [hA, hQform, Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero,
      hLR, ← Matrix.mul_assoc L R T, hLR, hReconstruct]
  · simpa only [Fintype.card_fin, Nat.cast_sub hkn] using hBudget

end NLAlib
