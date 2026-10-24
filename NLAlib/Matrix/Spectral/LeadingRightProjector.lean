import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.Matrix.Subspaces.SingularDirectionProjector
import NLAlib.Matrix.Subspaces.ProjectorCapture

/-! # Leading right singular projectors, including padded singular directions

A full right singular basis defines a projector at every cutoff. Its rank is the
cutoff capped by the width, regardless of the height or rank of the input matrix.
It realizes the native truncated SVD and therefore maximizes captured Frobenius energy.
Source: Horn–Johnson (2013), Theorem 7.4.9; Ghashami et al. (2016), §2.
-/

noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The leading right singular projector in a specified full SVD. At a tied cutoff,
the frame determines one permitted maximizing subspace. The definition is total in `k`. -/
def IsSVD.leadingRightProjector {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (_h : IsSVD A U V) (k : ℕ) : Matrix n n 𝕜 :=
  singularDirectionProjector V (fun i => decide ((i : ℕ) < k))

/-- Every SVD leading-right projector is Hermitian. -/
theorem IsSVD.leadingRightProjector_isHermitian {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (k : ℕ) :
    (h.leadingRightProjector k).IsHermitian := singularDirectionProjector_isHermitian _ _

/-- Every SVD leading-right projector is idempotent. -/
theorem IsSVD.leadingRightProjector_isIdempotentElem {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (k : ℕ) :
    IsIdempotentElem (h.leadingRightProjector k) :=
  HasOrthonormalCols.isIdempotentElem_singularDirectionProjector h.conjTranspose_mul_right _

private theorem sum_fin_prefix_indicator (q k : ℕ) :
    (∑ i : Fin q, if (i : ℕ) < k then (1 : ℝ) else 0) = (min k q : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then (1 : ℝ) else 0) q, ← Finset.sum_filter]
  have hf : (Finset.range q).filter (fun i => i < k) = Finset.range (min k q) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  rw [hf]
  simp

/-- The leading right projector has rank `min k width`, even when the height is zero.
No bound on `k` by the height or matrix rank is assumed. -/
theorem IsSVD.rank_leadingRightProjector {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (k : ℕ) :
    (h.leadingRightProjector k).rank = min k (Fintype.card n) := by
  have ht : RCLike.re (h.leadingRightProjector k).trace = (min k q : ℕ) := by
    rw [IsSVD.leadingRightProjector, singularDirectionProjector, Matrix.trace_mul_cycle,
      h.conjTranspose_mul_right, Matrix.one_mul, Matrix.trace_diagonal, map_sum]
    simpa only [decide_eq_true_eq, apply_ite, RCLike.one_re, RCLike.zero_re] using
      sum_fin_prefix_indicator q k
  rw [trace_eq_rank_of_isIdempotentElem _ (h.leadingRightProjector_isIdempotentElem k),
    RCLike.natCast_re] at ht
  rw [h.card_right]
  exact_mod_cast ht

/-- A width-admissible cutoff gives a rank-`k` right projector without a height restriction. -/
theorem IsSVD.rank_leadingRightProjector_of_le {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V)
    {k : ℕ} (hk : k ≤ Fintype.card n) : (h.leadingRightProjector k).rank = k := by
  rw [h.rank_leadingRightProjector, min_eq_left hk]

/-- Multiplication by the selected right projector is exactly the native truncated SVD. -/
theorem IsSVD.mul_leadingRightProjector_eq_truncatedMatrix {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (k : ℕ) :
    A * h.leadingRightProjector k = h.truncatedMatrix k := by
  rw [IsSVD.leadingRightProjector, singularDirectionProjector]
  conv_lhs => lhs; rw [h.eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᴴ V, h.conjTranspose_mul_right, Matrix.one_mul]
  have hd : (rectDiag (singularValues A) : Matrix (Fin p) (Fin q) 𝕜) *
      Matrix.diagonal (fun j : Fin q => if decide ((j : ℕ) < k) then (1 : 𝕜) else 0) =
      rectDiag (fun i => if i < k then singularValues A i else 0) := by
    ext i j
    rw [Matrix.mul_diagonal]
    simp only [rectDiag_apply_ofReal, decide_eq_true_eq]
    by_cases hij : (i : ℕ) = j
    · rw [if_pos hij, if_pos hij, ← hij]
      by_cases hi : (i : ℕ) < k
      · simp only [if_pos hi, mul_one]
      · simp only [if_neg hi, mul_zero, RCLike.ofReal_zero]
    · simp only [if_neg hij, zero_mul]
  change U * ((rectDiag (singularValues A) : Matrix (Fin p) (Fin q) 𝕜) *
    ((Matrix.diagonal fun j : Fin q => if decide ((j : ℕ) < k) then (1 : 𝕜) else 0) * Vᴴ)) = _
  simpa only [IsSVD.truncatedMatrix, Matrix.mul_assoc] using congrArg (fun M => U * M * Vᴴ) hd

/-- Leading right projection attains the optimal Frobenius rank tail for every cutoff,
including cutoffs larger than the height and zero-padded singular directions. -/
theorem IsSVD.frobSq_sub_mul_leadingRightProjector {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (k : ℕ) :
    frobSq (A - A * h.leadingRightProjector k) = bestRankFrobSq A k := by
  rw [h.mul_leadingRightProjector_eq_truncatedMatrix]
  exact h.frobSq_sub_truncatedMatrix k

/-- The leading right projector captures at least as much Frobenius energy as any
orthogonal projector of rank at most `k`. This is the maximizing-projector realization. -/
theorem IsSVD.frobSq_mul_le_leadingRightProjector {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (k : ℕ)
    {P : Matrix n n 𝕜} (hs : P.IsHermitian) (hp : IsIdempotentElem P) (hr : P.rank ≤ k) :
    frobSq (A * P) ≤ frobSq (A * h.leadingRightProjector k) := by
  have hPyth := frobSq_mul_projector_add_complement hs hp A
  have hLead := frobSq_mul_projector_add_complement (h.leadingRightProjector_isHermitian k)
    (h.leadingRightProjector_isIdempotentElem k) A
  rw [Matrix.mul_sub, Matrix.mul_one] at hPyth hLead
  rw [h.frobSq_sub_mul_leadingRightProjector] at hLead
  have hBest := bestRankFrobSq_le_frobSq_sub_of_rank_le A (A * P) k
    ((Matrix.rank_mul_le_right A P).trans hr)
  linarith

/-- The same realized projector maximizes the real Gram trace among all rank-at-most-k
orthogonal projectors. The width cutoff may exceed the input height or rank. -/
theorem IsSVD.re_trace_mul_gram_le_leadingRightProjector {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) (k : ℕ)
    {P : Matrix n n 𝕜} (hs : P.IsHermitian) (hp : IsIdempotentElem P) (hr : P.rank ≤ k) :
    RCLike.re (P * (Aᴴ * A)).trace ≤
      RCLike.re (h.leadingRightProjector k * (Aᴴ * A)).trace := by
  rw [← frobSq_mul_projector_eq_re_trace_mul hs hp A,
    ← frobSq_mul_projector_eq_re_trace_mul (h.leadingRightProjector_isHermitian k)
      (h.leadingRightProjector_isIdempotentElem k) A]
  exact h.frobSq_mul_le_leadingRightProjector k hs hp hr

/-- A rank-k Gram-trace maximizing right projector is realized by a full SVD for every
k at most the width, including a zero-dimensional or deficient left space. -/
theorem exists_rank_projector_maximizing_gram_trace (A : Matrix m n 𝕜)
    {k : ℕ} (hk : k ≤ Fintype.card n) :
    ∃ P : Matrix n n 𝕜, P.IsHermitian ∧ IsIdempotentElem P ∧ P.rank = k ∧
      ∀ Q : Matrix n n 𝕜, Q.IsHermitian → IsIdempotentElem Q → Q.rank = k →
        RCLike.re (Q * (Aᴴ * A)).trace ≤ RCLike.re (P * (Aᴴ * A)).trace := by
  obtain ⟨U, V, h⟩ := exists_isSVD A
  refine ⟨h.leadingRightProjector k, h.leadingRightProjector_isHermitian k,
    h.leadingRightProjector_isIdempotentElem k, h.rank_leadingRightProjector_of_le hk, ?_⟩
  intro Q hQ hQQ hRank
  exact h.re_trace_mul_gram_le_leadingRightProjector k hQ hQQ hRank.le

end NLAlib
