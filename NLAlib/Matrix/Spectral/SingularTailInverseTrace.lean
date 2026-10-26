import NLAlib.Matrix.Factorizations.MaximumVolumeQR
import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.Matrix.Norms.BlockDiagonalBounds

/-!
# Maximum-volume columns and singular-tail inverse traces

The shared maximum-volume QR budget bounds the inverse Gram trace using
the Frobenius error of its rank-truncated approximant. Eckart--Young turns
that error into the actual singular-value tail, including rank endpoints.
This supplies the input to principal-coordinate thinning for the
Naor--Youssef restricted-invertibility theorem.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib.RestrictedInvertibility

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
private theorem sum_singularTail_eq_sum_rank (A : Matrix m n ℝ) (l N : ℕ)
    (hN : A.rank ≤ N) :
    (∑ i ∈ Finset.range N, if l ≤ i then singularValues A i ^ 2 else 0) =
      ∑ i ∈ Finset.range A.rank, if l ≤ i then singularValues A i ^ 2 else 0 := by
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro i _ hi
  have hσ := singularValues_eq_zero_of_rank_le A
    (show A.rank ≤ i by simpa only [Finset.mem_range, not_lt] using hi)
  simp only [hσ, zero_pow (by decide : (2 : ℕ) ≠ 0), ite_self]

omit [DecidableEq m] in
/-- The library tail may be summed through the number of input columns.
Thus `bestRankFrobSq A (r-1)` is exactly the zero-padded one-based singular
tail in the Naor--Youssef statement, including rectangular matrices. -/
theorem bestRankFrobSq_eq_sum_width (A : Matrix m n ℝ) (l : ℕ) :
    bestRankFrobSq A l =
      ∑ i ∈ Finset.range (Fintype.card n), if l ≤ i then singularValues A i ^ 2 else 0 := by
  unfold bestRankFrobSq
  rw [sum_singularTail_eq_sum_rank A l _ A.rank_le_card_height,
    sum_singularTail_eq_sum_rank A l _ A.rank_le_card_width]

omit [DecidableEq m] in
/-- A singular-value tail is positive strictly below the matrix rank. -/
theorem bestRankFrobSq_pos_of_lt_rank (A : Matrix m n ℝ) {l : ℕ} (hl : l < A.rank) :
    0 < bestRankFrobSq A l := by
  have hσ : 0 < singularValues A l := (singularValues_pos_iff A l).mpr hl
  have hi : l ∈ Finset.range (Fintype.card m) :=
    Finset.mem_range.mpr (hl.trans_le A.rank_le_card_height)
  have hs := Finset.single_le_sum
    (s := Finset.range (Fintype.card m))
    (f := fun i => if l ≤ i then singularValues A i ^ 2 else 0)
    (fun i _ => by split_ifs <;> positivity) hi
  have ht : 0 < (if l ≤ l then singularValues A l ^ 2 else 0) := by simpa using sq_pos_of_pos hσ
  exact ht.trans_le hs

/-- Maximum-volume selection gives a positive definite selected Gram matrix
whose inverse trace is controlled by the singular-value tail. The selected
size is `l`, and the tail starts at zero-based index `l`. -/
theorem exists_column_embedding_posDef_gram_trace_inv_le_tail
    (A : Matrix m n ℝ) (l : ℕ) (hl : l < A.rank) :
    ∃ e : Fin l ↪ n,
      ((A.submatrix id e)ᵀ * A.submatrix id e).PosDef ∧
      ((A.submatrix id e)ᵀ * A.submatrix id e)⁻¹.trace ≤
        (l : ℝ) * (Fintype.card n - l) / bestRankFrobSq A l := by
  classical
  have hlw : l ≤ Fintype.card n := hl.le.trans A.rank_le_card_width
  obtain ⟨π, Q, R, T, D, hQ, _hQt, hR, _hUpper, hFact, _hEntry, hBudget⟩ :=
    exists_maximum_volume_qr_blocks A l hl.le
  let e : Fin l ↪ n :=
    ⟨fun i => π (Sum.inl i), π.injective.comp Sum.inl_injective⟩
  let C := A.submatrix id e
  let W := Matrix.fromBlocks R (R * T)
    (0 : Matrix (Fin (Fintype.card m - l)) (Fin l) ℝ) D
  let V := Matrix.fromBlocks R (R * T)
    (0 : Matrix (Fin (Fintype.card m - l)) (Fin l) ℝ)
    (0 : Matrix (Fin (Fintype.card m - l)) (Fin (Fintype.card n - l)) ℝ)
  have hC : C = Q * Matrix.fromRows R (0 : Matrix (Fin (Fintype.card m - l)) (Fin l) ℝ) := by
    change (A.submatrix id π).submatrix id Sum.inl = _
    rw [hFact]
    have hprod : (Q * W).submatrix id Sum.inl = Q * (W.submatrix id Sum.inl) := rfl
    change (Q * W).submatrix id Sum.inl = _
    rw [hprod]
    congr 1
    ext i j
    cases i <;> rfl
  have hGram : Cᵀ * C = Rᵀ * R := by
    rw [hC, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Qᵀ Q, show Qᵀ * Q = 1 from hQ,
      Matrix.one_mul, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows,
      Matrix.transpose_zero, Matrix.zero_mul, add_zero]
  have hGramUnit : IsUnit (Cᵀ * C) := by
    rw [hGram, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det R).mp hR).mul ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hGramPos : (Cᵀ * C).PosDef := by
    have hp : (Cᵀ * C).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_conjTranspose_mul_self C
    exact hp.posDef_iff_isUnit.mpr hGramUnit
  have hInvTrace : (Cᵀ * C)⁻¹.trace = frobSq R⁻¹ := by
    rw [hGram, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
      frobSq, frobInner_eq_trace, RCLike.re_to_real,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.trace_mul_comm]
  have hVRank : V.rank ≤ l := by
    have hV : V =
        Matrix.fromRows (1 : Matrix (Fin l) (Fin l) ℝ)
          (0 : Matrix (Fin (Fintype.card m - l)) (Fin l) ℝ) *
        Matrix.fromCols R (R * T) := by
      rw [Matrix.fromRows_mul_fromCols]
      simp only [Matrix.one_mul, Matrix.zero_mul]
      rfl
    rw [hV]
    exact (Matrix.rank_mul_le_right _ _).trans (by simpa using
      (Matrix.fromCols R (R * T)).rank_le_card_height)
  have hTailEq : bestRankFrobSq (A.submatrix id π) l = bestRankFrobSq A l := by
    have hh := singularValues_reindex A (Equiv.refl m) π.symm
    change singularValues (A.submatrix id π) = singularValues A at hh
    simp only [bestRankFrobSq, hh]
  have hResidual : frobSq (A.submatrix id π - Q * V) = frobSq D := by
    rw [hFact]
    change frobSq (Q * W - Q * V) = _
    rw [← Matrix.mul_sub, frobSq_mul_left_of_orthonormal hQ.conjTranspose_mul_self]
    have hdiff : W - V = Matrix.fromBlocks
        (0 : Matrix (Fin l) (Fin l) ℝ)
        (0 : Matrix (Fin l) (Fin (Fintype.card n - l)) ℝ)
        (0 : Matrix (Fin (Fintype.card m - l)) (Fin l) ℝ) D := by
      ext i j
      cases i <;> cases j <;> simp [W, V]
    rw [hdiff, frobSq_fromBlocks]
    simp only [frobSq_zero, zero_add]
  have hTail : bestRankFrobSq A l ≤ frobSq D := by
    rw [← hResidual, ← hTailEq]
    exact bestRankFrobSq_le_frobSq_sub_of_rank_le _ _ l
      ((Matrix.rank_mul_le_right Q V).trans hVRank)
  have hE : 0 < bestRankFrobSq A l := bestRankFrobSq_pos_of_lt_rank A hl
  refine ⟨e, hGramPos, ?_⟩
  change (Cᵀ * C)⁻¹.trace ≤ _
  rw [hInvTrace]
  apply (le_div_iff₀ hE).mpr
  have hh := mul_le_mul_of_nonneg_left hTail (frobSq_nonneg R⁻¹)
  have hTnon : 0 ≤ frobSq T := frobSq_nonneg T
  simpa only [Nat.cast_sub hlw] using (hh.trans (by linarith :
    frobSq R⁻¹ * frobSq D ≤ (l : ℝ) * (Fintype.card n - l)))

end NLAlib.RestrictedInvertibility
