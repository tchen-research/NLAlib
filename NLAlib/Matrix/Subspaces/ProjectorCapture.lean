/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Subspaces.RangeProjector
import NLAlib.Matrix.Basic.GramVanishing
import NLAlib.Matrix.Spectral.EckartYoung

/-! # Captured Frobenius energy in singular coordinates

Orthogonal projector errors split exactly. In a full left singular basis, captured
energy is a weighted sum of squared singular values and projector diagonal entries.
Source: Horn–Johnson (2013), Theorem 7.4.9; Fessler–Nadakuditi (2024), §7.5.3.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- Exact least-squares decomposition for an orthogonal projector fixing the competitor. -/
theorem frobSq_sub_eq_projector_error_add {P : Matrix m m 𝕜}
    (hP : P.IsHermitian) (hPP : IsIdempotentElem P) (Y X : Matrix m n 𝕜)
    (hPX : P * X = X) :
    frobSq (Y - X) = frobSq Y - frobSq (P * Y) + frobSq (P * Y - X) := by
  have hY := frobSq_projector_mul_add_complement hP hPP Y
  have hE := frobSq_projector_mul_add_complement hP hPP (Y - X)
  have hCX : (1 - P) * X = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPX, sub_self]
  rw [Matrix.mul_sub, hPX, Matrix.mul_sub, hCX, sub_zero] at hE
  linarith

/-- Captured Frobenius energy is the singular-value square sum weighted by the
projection diagonal in a full left singular basis. -/
theorem IsSVD.frobSq_projector_mul_eq_sum {p q : ℕ} {Y : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD Y U V)
    {P : Matrix m m 𝕜} (hs : P.IsHermitian) (hp : IsIdempotentElem P) :
    frobSq (P * Y) =
      ∑ i : Fin p, singularValues Y i ^ 2 * RCLike.re ((Uᴴ * P * U) i i) := by
  have hgram : (P * Y) * (P * Y)ᴴ = P * (Y * Yᴴ) * P := by
    simp only [Matrix.conjTranspose_mul, hs.eq, Matrix.mul_assoc]
  set D : Matrix (Fin p) (Fin p) 𝕜 :=
    Matrix.diagonal (fun i => ((singularValues Y i ^ 2 : ℝ) : 𝕜))
  rw [← frobSq_conjTranspose, frobSq, frobInner_eq_trace, Matrix.conjTranspose_conjTranspose,
    hgram, h.mul_conjTranspose_self]
  calc
    _ = RCLike.re (P * U * (D * (Uᴴ * P))).trace := by
      congr 2
      simp only [Matrix.mul_assoc, D]
    _ = RCLike.re ((D * (Uᴴ * P)) * (P * U)).trace := by rw [Matrix.trace_mul_comm]
    _ = RCLike.re (D * (Uᴴ * P * U)).trace := by
      congr 2
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P U, show P * P = P from hp]
    _ = _ := by
      simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, map_sum, D,
        RCLike.re_ofReal_mul]

/-- The full left singular basis gives the Frobenius square as its padded square sum. -/
theorem IsSVD.frobSq_eq_sum_left_singularValues_sq {p q : ℕ} {Y : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD Y U V) :
    frobSq Y = ∑ i : Fin p, singularValues Y i ^ 2 := by
  have hp : IsIdempotentElem (1 : Matrix m m 𝕜) := by change (1 : Matrix m m 𝕜) * 1 = 1; simp
  have hc := h.frobSq_projector_mul_eq_sum (P := 1) Matrix.isHermitian_one hp
  simpa only [Matrix.one_mul, Matrix.mul_one, h.conjTranspose_mul_left,
    Matrix.one_apply_eq, RCLike.one_re, mul_one] using hc

/-- The first singular-value square sum and the native best-rank tail split the full
Frobenius square, with zero padding beyond either dimension. -/
theorem frobSq_eq_sum_prefix_sq_add_bestRankFrobSq (A : Matrix m n 𝕜) (k : ℕ) :
    frobSq A = (∑ i ∈ Finset.range k, singularValues A i ^ 2) + bestRankFrobSq A k := by
  obtain ⟨U, V, h⟩ := exists_isSVD A
  rw [h.frobSq_eq_sum_left_singularValues_sq, bestRankFrobSq,
    Fin.sum_univ_eq_sum_range (fun i => singularValues A i ^ 2) (Fintype.card m)]
  by_cases hk : k ≤ Fintype.card m
  · have ht : (∑ i ∈ Finset.range (Fintype.card m), if k ≤ i then singularValues A i ^ 2 else 0) =
        ∑ i ∈ Finset.Ico k (Fintype.card m), singularValues A i ^ 2 := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [ht]
    exact (Finset.sum_range_add_sum_Ico _ hk).symm
  · have hmk : Fintype.card m ≤ k := by omega
    have ht : (∑ i ∈ Finset.range (Fintype.card m), if k ≤ i then singularValues A i ^ 2 else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
    rw [ht, add_zero]
    apply Finset.sum_subset (Finset.range_subset_range.mpr hmk)
    intro i _ hi
    have hz := singularValues_eq_zero_of_height_le A
      (show Fintype.card m ≤ i by simpa only [Finset.mem_range, not_lt] using hi)
    rw [hz, zero_pow (by decide : 2 ≠ 0)]

/-- An orthogonal projector of rank at most `k` captures at most the first `k`
singular-value squares. This is generic over both scalar fields and every finite shape.
It follows directly from Eckart–Young and projector Pythagoras. -/
theorem frobSq_projector_mul_le_sum_prefix_singularValues_sq {P : Matrix m m 𝕜}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (A : Matrix m n 𝕜)
    (k : ℕ) (hr : P.rank ≤ k) :
    frobSq (P * A) ≤ ∑ i ∈ Finset.range k, singularValues A i ^ 2 := by
  have hPyth := frobSq_projector_mul_add_complement hs hp A
  rw [Matrix.sub_mul, Matrix.one_mul] at hPyth
  have hBest := bestRankFrobSq_le_frobSq_sub_of_rank_le A (P * A) k
    ((Matrix.rank_mul_le_left P A).trans hr)
  have hSplit := frobSq_eq_sum_prefix_sq_add_bestRankFrobSq A k
  linarith

/-- Unitary singular coordinates preserve the real trace of every matrix. -/
theorem IsSVD.re_trace_conjTranspose_mul_mul {p q : ℕ} {Y : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD Y U V)
    (P : Matrix m m 𝕜) :
    (∑ i : Fin p, RCLike.re ((Uᴴ * P * U) i i)) = RCLike.re P.trace := by
  rw [← map_sum]
  change RCLike.re (Uᴴ * P * U).trace = _
  rw [Matrix.trace_mul_cycle, h.mul_conjTranspose_left, Matrix.one_mul]

/-- A Hermitian idempotent is determined by a diagonal of zeros and ones.
PSD zero-diagonal row vanishing is applied to the projector and its complement. -/
theorem _root_.Matrix.IsHermitian.eq_diagonal_of_isIdempotentElem_of_re_diag
    {P : Matrix m m 𝕜} (hs : P.IsHermitian) (hp : IsIdempotentElem P)
    (keep : m → Bool) (hd : ∀ i, RCLike.re (P i i) = if keep i then 1 else 0) :
    P = Matrix.diagonal (fun i => if keep i then 1 else 0) := by
  have hPSD := hs.posSemidef_of_isIdempotentElem hp
  have hQ := one_sub_projector_isHermitian_isIdempotentElem hs hp
  have hQPSD := hQ.1.posSemidef_of_isIdempotentElem hQ.2
  ext i j
  cases hj : keep j with
  | false =>
    have hz : P j j = 0 := by
      rw [← hs.coe_re_apply_self, hd j]
      simp [hj]
    rw [Matrix.diagonal_apply]
    have hij := apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hPSD hz i
    by_cases heq : i = j
    · subst j
      simpa [hj] using hij
    · simpa [heq] using hij
  | true =>
    have hz : (1 - P) j j = 0 := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, ← hs.coe_re_apply_self, hd j]
      simp [hj]
    have hij := apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hQPSD hz i
    rw [Matrix.sub_apply, sub_eq_zero] at hij
    rw [Matrix.diagonal_apply]
    by_cases heq : i = j
    · subst j
      simpa [hj] using hij.symm
    · simpa [heq] using hij.symm

end NLAlib
