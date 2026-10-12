import NLAlib.Matrix.OrthogonalSumCompletion
import NLAlib.Matrix.RankInequalities

/-!
# Range-adapted orthogonal blocks of an idempotent

Every real idempotent is orthogonally similar to `[I T; 0 0]`, with the
identity size equal to its actual rank. Horn–Johnson 2013, Corollary 3.4.3.3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- An idempotent fixes every matrix whose range lies in its range.
Horn–Johnson 2013, Section 1.3; oblique projection helper. -/
theorem mul_eq_of_range_le_of_isIdempotentElem {n r : Type*}
    [Fintype n] [Fintype r] {P : Matrix n n ℝ} {Q : Matrix n r ℝ}
    (hP : IsIdempotentElem P)
    (hRange : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin) : P * Q = Q := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  obtain ⟨y, hy⟩ := hRange (show Q *ᵥ x ∈ LinearMap.range Q.mulVecLin from ⟨x, rfl⟩)
  rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    show P * P = P from hP]

/-- Orthogonal coordinates adapted to the actual range of an idempotent
give the exact block form `[I T; 0 0]`. Both coordinate Gram identities are
supplied; the first block has `rank P` coordinates, so zero and full rank
are included. Horn–Johnson 2013, Corollary 3.4.3.3.
atlas: cs-decomposition (partial) -/
theorem exists_orthogonal_idempotent_range_blocks {n : Type*}
    [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (hP : IsIdempotentElem P) :
    ∃ H : Matrix n (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℝ,
    ∃ T : Matrix (Fin P.rank) (Fin (Fintype.card n - P.rank)) ℝ,
      HasOrthonormalCols H ∧ H * Hᵀ = 1 ∧
      Hᵀ * P * H = Matrix.fromBlocks 1 T 0 0 := by
  let Q : Matrix n (Fin P.rank) ℝ := orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  have hQ : HasOrthonormalCols Q :=
    hasOrthonormalCols_orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  have hRange : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin :=
    range_orthonormalBasisMatrix (LinearMap.range P.mulVecLin)
  obtain ⟨H, hH, hHt, hHQ⟩ := exists_orthogonal_sum_completion
    (q := Fin (Fintype.card n - P.rank)) Q hQ
    (by simpa using Nat.add_sub_of_le P.rank_le_card_height)
  let R := H.submatrix id Sum.inr
  have hHform : H = Matrix.fromCols Q R := by
    ext i j
    cases j with
    | inl j => exact congrArg (fun A : Matrix n (Fin P.rank) ℝ => A i j) hHQ
    | inr j => rfl
  have hCross : Rᵀ * Q = 0 := by
    have h := congrArg Matrix.toBlocks₂₁ hH
    rw [hHform, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols] at h
    simpa only [Matrix.toBlocks_fromBlocks₂₁,
      show (1 : Matrix (Fin P.rank ⊕ Fin (Fintype.card n - P.rank))
        (Fin P.rank ⊕ Fin (Fintype.card n - P.rank)) ℝ).toBlocks₂₁ = 0 by
        ext i j; simp [Matrix.toBlocks₂₁]] using h
  have hPQ : P * Q = Q := mul_eq_of_range_le_of_isIdempotentElem hP hRange.le
  have hQP : Q * (Qᵀ * P) = P := mul_transpose_mul_eq_of_range_le hQ hRange.ge
  have hRP : Rᵀ * P = 0 := by
    calc
      Rᵀ * P = Rᵀ * (Q * (Qᵀ * P)) := congrArg (fun A : Matrix n n ℝ => Rᵀ * A) hQP.symm
      _ = 0 := by rw [← Matrix.mul_assoc, hCross, Matrix.zero_mul]
  refine ⟨H, Qᵀ * P * R, hH, hHt, ?_⟩
  rw [hHform, Matrix.transpose_fromCols, Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols]
  rw [Matrix.mul_assoc, hPQ, show Qᵀ * Q = 1 from hQ,
    hRP, Matrix.zero_mul, Matrix.zero_mul]

end NLAlib
