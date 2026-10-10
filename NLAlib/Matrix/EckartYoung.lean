import NLAlib.Matrix.MoorePenrose
import NLAlib.Matrix.Projections
import NLAlib.Matrix.SpectralBounds
import Mathlib.LinearAlgebra.Trace
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# Eckart–Young theorem

Frobenius form (`bestRankFrobSq_eq_singularValueTailSq`, `isBestRankApprox_truncatedSVD`) and
the spectral attainment `specNorm_sub_truncatedSVD_eq` (`‖A − A_k‖₂ = σ_k`).

The Frobenius proof compares an arbitrary rank-bounded competitor with its actual
Moore–Penrose column-space projector. In singular-vector coordinates the
projector has diagonal weights in `[0,1]` with total mass equal to its rank.
The finite weighted top-k inequality then gives the optimal singular-value tail.

Source: Horn–Johnson, Matrix Analysis, Theorem 7.4.9; HMT 2011, §2.1.
Atlas: `eckart-young`. No probabilistic or inverse-Wishart bounds enter this proof.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- The trace of an idempotent real matrix is its rank. Empty index types
are included. This is Mathlib's projection trace theorem in matrix coordinates.
Atlas `eckart-young` (foundation). -/
theorem trace_eq_rank_of_isIdempotentElem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : IsIdempotentElem P) : P.trace = (P.rank : ℝ) := by
  have hf : IsIdempotentElem P.mulVecLin := by
    change P.mulVecLin.comp P.mulVecLin = P.mulVecLin
    rw [← Matrix.mulVecLin_mul, show P * P = P from hP]
  calc
    P.trace = LinearMap.trace ℝ (ι → ℝ) P.toLin' := (Matrix.trace_toLin'_eq P).symm
    _ = LinearMap.trace ℝ (ι → ℝ) P.mulVecLin := by rw [Matrix.toLin'_apply']
    _ = (P.rank : ℝ) := LinearMap.IsProj.trace
      ((LinearMap.isProj_range_iff_isIdempotentElem P.mulVecLin).mpr hf)

/-- Every diagonal weight of a real orthogonal projector lies in `[0,1]`.
The proof uses the squared column length, including all degenerate cases.
Atlas `eckart-young` (foundation). -/
theorem diag_mem_Icc_of_isSymm_of_isIdempotentElem {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hs : Pᵀ = P) (hp : IsIdempotentElem P) (j : ι) :
    P j j ∈ Set.Icc (0 : ℝ) 1 := by
  have hgram : Pᵀ * P = P := by rw [hs]; exact hp
  have hsum : (∑ i, P i j ^ 2) = P j j := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M j j) hgram
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have h0 : 0 ≤ P j j := by
    rw [← hsum]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsq : P j j ^ 2 ≤ P j j := by
    calc
      _ ≤ ∑ i, P i j ^ 2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (P i j)) (Finset.mem_univ j)
      _ = P j j := hsum
  exact ⟨h0, by nlinarith⟩

private theorem card_fin_head {m k : ℕ} (hk : k < m) :
    ((Finset.univ : Finset (Fin m)).filter fun i : Fin m => (i : ℕ) < k).card = k := by
  have he : ((Finset.univ : Finset (Fin m)).filter fun i : Fin m => (i : ℕ) < k) =
      Finset.Iio (⟨k, hk⟩ : Fin m) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    rfl
  rw [he, Fin.card_Iio]

/-- **Weighted top-`k` inequality.** For nonnegative non-increasing `a` and weights
`0 ≤ wᵢ ≤ 1` with total mass at most `k`, `∑ᵢ aᵢ wᵢ ≤ ∑_{i<k} aᵢ`. The finite core of
Eckart–Young and of Ky Fan's maximum principle (Horn–Johnson 2013, proof of Thm 7.4.9;
Bhatia 1997, Lemma III.1.1 / Ky Fan). Audit G0 A2 (made public for the von Neumann trace
inequality); atlas `eckart-young`, `von-neumann-trace`. -/
theorem sum_mul_le_sum_ite_lt_of_antitone {m k : ℕ} (a w : Fin m → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha : Antitone a)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hbudget : ∑ i, w i ≤ (k : ℝ)) :
    (∑ i, a i * w i) ≤ ∑ i : Fin m, if (i : ℕ) < k then a i else 0 := by
  classical
  by_cases hk : k < m
  · let c : Fin m := ⟨k, hk⟩
    have hpoint (i : Fin m) : (a i - a c) * w i ≤
        if (i : ℕ) < k then a i - a c else 0 := by
      by_cases hi : (i : ℕ) < k
      · rw [if_pos hi]
        have hac : a c ≤ a i := ha (show i ≤ c from Nat.le_of_lt hi)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw1 i) (sub_nonneg.mpr hac)
      · rw [if_neg hi]
        have hac : a i ≤ a c := ha (show c ≤ i from not_lt.mp hi)
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hac) (hw0 i)
    have hcard := card_fin_head hk
    have hsum : (∑ i : Fin m, if (i : ℕ) < k then a i - a c else 0) =
        (∑ i : Fin m, if (i : ℕ) < k then a i else 0) - (k : ℝ) * a c := by
      rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const, hcard]
      rw [← Finset.sum_filter]
      simp only [nsmul_eq_mul]
    calc
      (∑ i, a i * w i) = a c * (∑ i, w i) + ∑ i, (a i - a c) * w i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ a c * k + ∑ i : Fin m, if (i : ℕ) < k then a i - a c else 0 :=
        add_le_add (mul_le_mul_of_nonneg_left hbudget (ha0 c))
          (Finset.sum_le_sum (fun i _ => hpoint i))
      _ = ∑ i : Fin m, if (i : ℕ) < k then a i else 0 := by rw [hsum]; ring
  · have hmk : m ≤ k := not_lt.mp hk
    have hall (i : Fin m) : (i : ℕ) < k := lt_of_lt_of_le i.isLt hmk
    simp only [if_pos (hall _)]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw1 i) (ha0 i)

private theorem frobSq_eq_projection_add_residual {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (P : Matrix m m ℝ) (hs : Pᵀ = P) (hp : IsIdempotentElem P)
    (A : Matrix m n ℝ) :
    frobSq A = frobSq (P * A) + frobSq ((1 - P) * A) := by
  have horth : Pᵀ * (1 - P) = 0 := by
    rw [hs, Matrix.mul_sub, Matrix.mul_one, show P * P = P from hp, sub_self]
  have hsplit : P * A + (1 - P) * A = A := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  calc
    frobSq A = frobSq (P * A + (1 - P) * A) := congrArg frobSq hsplit.symm
    _ = _ := frobSq_add_of_frobInner_eq_zero _ _
      (frobInner_mul_mul_eq_zero P A (1 - P) A horth)

private theorem frobSq_projection_residual_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (P : Matrix m m ℝ) (hs : Pᵀ = P) (hp : IsIdempotentElem P)
    (A B : Matrix m n ℝ) (hPB : P * B = B) :
    frobSq ((1 - P) * A) ≤ frobSq (A - B) := by
  have horth : (1 - P)ᵀ * P = 0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hs, Matrix.sub_mul,
      Matrix.one_mul, show P * P = P from hp, sub_self]
  have hsplit : (1 - P) * A + P * (A - B) = A - B := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hPB]
    abel
  rw [← hsplit, frobSq_add_of_frobInner_eq_zero _ _
    (frobInner_mul_mul_eq_zero (1 - P) A P (A - B) horth)]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

/-- The squared singular-value tail after deleting the first `k` singular
values. Padding includes rectangular null directions and zero dimensions.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: best-rank-approx-def -/
def singularValueTailSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin m, if k ≤ (i : ℕ) then singularValues A i ^ 2 else 0

/-- **Frobenius Eckart–Young lower bound.** Every rank-at-most-`k` real
competitor has squared error at least the singular-value tail.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem singularValueTailSq_le_frobSq_sub_of_rank_le {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) (hB : B.rank ≤ k) :
    singularValueTailSq A k ≤ frobSq (A - B) := by
  let P := B * moorePenroseInverse B
  have hs : Pᵀ = P := (mul_moorePenroseInverse_isSymm B).eq
  have hp : IsIdempotentElem P := mul_moorePenroseInverse_isIdempotentElem B
  have hPB : P * B = B := mul_moorePenroseInverse_mul B
  have hrankP : P.rank ≤ k := (Matrix.rank_mul_le_left B _).trans hB
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A
  let R := Uᵀ * P * U
  have hsR : Rᵀ = R := by
    dsimp [R]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]
  have hpR : IsIdempotentElem R := by
    change (Uᵀ * P * U) * (Uᵀ * P * U) = Uᵀ * P * U
    calc
      _ = Uᵀ * (P * (U * Uᵀ) * P) * U := by simp only [Matrix.mul_assoc]
      _ = Uᵀ * P * U := by rw [hSVD.mul_transpose_left, Matrix.mul_one, show P * P = P from hp]
  have hrankR : R.rank ≤ k :=
    ((Matrix.rank_mul_le_left (Uᵀ * P) U).trans (Matrix.rank_mul_le_right Uᵀ P)).trans hrankP
  have hbudget : ∑ i : Fin m, R i i ≤ (k : ℝ) := by
    change R.trace ≤ (k : ℝ)
    rw [trace_eq_rank_of_isIdempotentElem R hpR]
    exact_mod_cast hrankR
  have hweights (i : Fin m) := diag_mem_Icc_of_isSymm_of_isIdempotentElem R hsR hpR i
  have hcaptured : frobSq (P * A) = ∑ i : Fin m, singularValues A i ^ 2 * R i i := by
    have hgram : (P * A)ᵀ * (P * A) = Aᵀ * P * A := by
      calc
        _ = Aᵀ * (Pᵀ * P) * A := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hs, show P * P = P from hp]
    rw [frobSq, frobInner_eq_trace, hgram, Matrix.trace_mul_cycle, hSVD.mul_transpose_self]
    calc
      _ = (U * (Matrix.diagonal (fun i : Fin m => singularValues A i ^ 2) * (Uᵀ * P))).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = ((Matrix.diagonal (fun i : Fin m => singularValues A i ^ 2) * (Uᵀ * P)) * U).trace :=
        Matrix.trace_mul_comm _ _
      _ = (Matrix.diagonal (fun i : Fin m => singularValues A i ^ 2) * R).trace := by
        congr 1
        simp only [R, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  have hcaptured_le : frobSq (P * A) ≤
      ∑ i : Fin m, if (i : ℕ) < k then singularValues A i ^ 2 else 0 := by
    rw [hcaptured]
    apply sum_mul_le_sum_ite_lt_of_antitone
    · intro i; exact sq_nonneg _
    · intro i j hij
      exact pow_le_pow_left₀ (singularValues_nonneg A j) (singularValues_antitone A hij) 2
    · intro i; exact (hweights i).1
    · intro i; exact (hweights i).2
    · exact hbudget
  have htotal : frobSq A = ∑ i : Fin m, singularValues A i ^ 2 := by
    rw [← frobSq_transpose A, frobSq, frobInner_eq_trace, Matrix.transpose_transpose,
      hSVD.mul_transpose_self, Matrix.trace_mul_cycle, hSVD.transpose_mul_left,
      Matrix.one_mul, Matrix.trace_diagonal]
  have hsplit : frobSq A =
      (∑ i : Fin m, if (i : ℕ) < k then singularValues A i ^ 2 else 0) +
      singularValueTailSq A k := by
    rw [htotal, singularValueTailSq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) < k
    · simp [hi, not_le.mpr hi]
    · simp [hi, not_lt.mp hi]
  have hpyth := frobSq_eq_projection_add_residual P hs hp A
  have hres := frobSq_projection_residual_le P hs hp A B hPB
  linarith

private theorem card_fin_head_le (m k : ℕ) :
    ((Finset.univ : Finset (Fin m)).filter fun i : Fin m => (i : ℕ) < k).card ≤ k := by
  by_cases hk : k < m
  · rw [card_fin_head hk]
  · calc
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
      _ = m := by simp
      _ ≤ k := not_lt.mp hk

/-- Truncate a given real SVD after its first `k` singular values. The index
may exceed either matrix dimension; in that case padding handles the cutoff.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: best-rank-approx-def -/
def IsSVD.truncatedMatrix {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (_h : IsSVD A U V) (k : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  U * (rectDiag (fun i => if i < k then singularValues A i else 0) :
    Matrix (Fin m) (Fin n) ℝ) * Vᵀ

/-- The truncated SVD has rank at most its cutoff, including cutoff zero.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem IsSVD.rank_truncatedMatrix_le {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A U V) (k : ℕ) : (h.truncatedMatrix k).rank ≤ k := by
  classical
  let S : Matrix (Fin m) (Fin n) ℝ :=
    rectDiag (fun i => if i < k then singularValues A i else 0)
  let H := (Finset.univ : Finset (Fin m)).filter fun i : Fin m => (i : ℕ) < k
  have hsupport : Function.support S.row ⊆ H := by
    rw [Function.support_subset_iff']
    intro i hi
    have hik : ¬(i : ℕ) < k := by simpa [H] using hi
    ext j
    change S i j = 0
    simp [S, rectDiag_apply, hik]
  have hS : S.rank ≤ H.card := Matrix.rank_le_card_of_support_subset S H hsupport
  change (U * S * Vᵀ).rank ≤ k
  exact ((Matrix.rank_mul_le_left (U * S) Vᵀ).trans (Matrix.rank_mul_le_right U S)).trans
    (hS.trans (card_fin_head_le m k))

/-- The squared error of the truncated SVD is exactly the singular-value
tail, with no rank/dimension side conditions.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem IsSVD.frobSq_sub_truncatedMatrix {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A U V) (k : ℕ) :
    frobSq (A - h.truncatedMatrix k) = singularValueTailSq A k := by
  let T : Matrix (Fin m) (Fin n) ℝ :=
    rectDiag (fun i => if i < k then 0 else singularValues A i)
  have hsplit : A = h.truncatedMatrix k + U * T * Vᵀ := h.eq_head_add_tail k
  have he : A - h.truncatedMatrix k = U * T * Vᵀ := by
    calc
      _ = (h.truncatedMatrix k + U * T * Vᵀ) - h.truncatedMatrix k :=
        congrArg (fun M => M - h.truncatedMatrix k) hsplit
      _ = _ := by abel
  rw [he, frobSq_mul_right_of_orthonormal h.transpose_mul_right,
    frobSq_mul_left_of_orthonormal h.transpose_mul_left]
  rw [← frobSq_transpose T, frobSq, frobInner_eq_trace, Matrix.transpose_transpose]
  dsimp only [T]
  rw [rectDiag_mul_transpose_rectDiag, Matrix.trace_diagonal, singularValueTailSq]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hin : (i : ℕ) < n
  · rw [if_pos hin]
    by_cases hik : (i : ℕ) < k
    · simp [hik, not_le.mpr hik]
    · simp [hik, not_lt.mp hik]
  · rw [if_neg hin, singularValues_eq_zero_of_width_le A (not_lt.mp hin)]
    simp

/-- **Frobenius Eckart–Young minimizer.** Truncating any actual SVD gives a
best rank-at-most-`k` approximation, rather than assuming a best-approximation
predicate. Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem IsSVD.isBestRankApprox_truncatedMatrix {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A U V) (k : ℕ) : IsBestRankApprox k A (h.truncatedMatrix k) := by
  refine ⟨h.rank_truncatedMatrix_le k, ?_⟩
  intro B hB
  rw [h.frobSq_sub_truncatedMatrix k]
  exact singularValueTailSq_le_frobSq_sub_of_rank_le A B k hB

/-- A concrete rank-`k` truncated SVD, using an SVD chosen from the proved
existence theorem. No best-approximation assumption enters the definition.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: best-rank-approx-def -/
def truncatedSVD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin m) (Fin n) ℝ := (exists_isSVD A).choose_spec.choose_spec.truncatedMatrix k

/-- The constructed truncated SVD is a best rank-at-most-`k` approximation.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: eckart-young-frobenius -/
theorem isBestRankApprox_truncatedSVD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    IsBestRankApprox k A (truncatedSVD A k) := by
  unfold truncatedSVD
  exact (exists_isSVD A).choose_spec.choose_spec.isBestRankApprox_truncatedMatrix k

/-- The chosen truncated SVD attains the exact singular-value-tail error.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem frobSq_sub_truncatedSVD_eq_singularValueTailSq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    frobSq (A - truncatedSVD A k) = singularValueTailSq A k := by
  unfold truncatedSVD
  exact (exists_isSVD A).choose_spec.choose_spec.frobSq_sub_truncatedMatrix k

/-- The actual rank-constrained optimal squared Frobenius error, as an
infimum over all feasible matrices. Eckart–Young proves it is attained.
Atlas `eckart-young`; intended for relative RSVD/GN error statements.
atlas: best-rank-approx-def -/
def bestRankFrobSq {m n : Type*} [Fintype m] [Fintype n]
    (k : ℕ) (A : Matrix m n ℝ) : ℝ :=
  sInf {v : ℝ | ∃ B : Matrix m n ℝ, B.rank ≤ k ∧ v = frobSq (A - B)}

/-- The genuine optimal rank-`k` squared Frobenius error equals the spectral
tail. All ranks, rectangular shapes and zero dimensions are included.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: eckart-young-frobenius -/
theorem bestRankFrobSq_eq_singularValueTailSq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    bestRankFrobSq k A = singularValueTailSq A k := by
  let S := {v : ℝ | ∃ B : Matrix (Fin m) (Fin n) ℝ, B.rank ≤ k ∧ v = frobSq (A - B)}
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro v ⟨B, _, rfl⟩
    exact frobSq_nonneg _
  have hmem : frobSq (A - truncatedSVD A k) ∈ S :=
    ⟨truncatedSVD A k, (isBestRankApprox_truncatedSVD A k).1, rfl⟩
  change sInf S = singularValueTailSq A k
  apply le_antisymm
  · have hle := csInf_le hbdd hmem
    rwa [frobSq_sub_truncatedSVD_eq_singularValueTailSq] at hle
  · apply le_csInf ⟨_, hmem⟩
    rintro v ⟨B, hB, rfl⟩
    exact singularValueTailSq_le_frobSq_sub_of_rank_le A B k hB

/-- The explicit truncated SVD attains the actual rank-constrained optimum.
Atlas `eckart-young`; a direct bridge to relative best-rank error bounds.
atlas: eckart-young-frobenius -/
theorem frobSq_sub_truncatedSVD_eq_bestRankFrobSq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    frobSq (A - truncatedSVD A k) = bestRankFrobSq k A := by
  rw [frobSq_sub_truncatedSVD_eq_singularValueTailSq, bestRankFrobSq_eq_singularValueTailSq]

/-! ### Spectral-norm attainment -/

/-- **Spectral Eckart–Young, attainment for a given SVD.** The spectral error of truncating an
SVD after `k` terms is the `(k+1)`-st singular value (zero-indexed `σ_k`):
`‖A − U Σ_{<k} Vᵀ‖₂ = σ_k(A)`. All shapes and cutoffs are allowed (`σ_k = 0` for
`k ≥ min m n`). Horn–Johnson 2013, Thm 7.4.9.1 (spectral case); HMT 2011, eq. (2.3);
audit G0 C3; atlas `eckart-young`. -/
theorem IsSVD.specNorm_sub_truncatedMatrix {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A U V) (k : ℕ) :
    specNorm (A - h.truncatedMatrix k) = singularValues A k := by
  set τ : ℕ → ℝ := fun i => if i < k then 0 else singularValues A i with hτ
  let T : Matrix (Fin m) (Fin n) ℝ := rectDiag τ
  have hsplit : A = h.truncatedMatrix k + U * T * Vᵀ := h.eq_head_add_tail k
  have he : A - h.truncatedMatrix k = U * T * Vᵀ := by
    calc
      _ = (h.truncatedMatrix k + U * T * Vᵀ) - h.truncatedMatrix k :=
        congrArg (fun M => M - h.truncatedMatrix k) hsplit
      _ = _ := by abel
  rw [he, specNorm_mul_transpose_right_of_hasOrthonormalCols h.transpose_mul_right,
    specNorm_mul_left_of_hasOrthonormalCols h.transpose_mul_left]
  have hσk := singularValues_nonneg A k
  have hsq : specNorm T ^ 2 = singularValues A k ^ 2 := by
    rw [specNorm_sq_eq_specNorm_transpose_mul_self, transpose_rectDiag_mul_rectDiag,
      specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2 fun j => ?_
      rw [Real.norm_eq_abs]
      split_ifs with hj
      · rw [abs_of_nonneg (sq_nonneg _)]
        simp only [hτ]
        split_ifs with hjk
        · simpa using sq_nonneg (singularValues A k)
        · exact pow_le_pow_left₀ (singularValues_nonneg A j)
            (singularValues_antitone A (not_lt.1 hjk)) 2
      · simpa using sq_nonneg (singularValues A k)
    · by_cases hk : k < min m n
      · have hkm : k < m := lt_of_lt_of_le hk (min_le_left m n)
        have hkn : k < n := lt_of_lt_of_le hk (min_le_right m n)
        have h0 := norm_le_pi_norm (fun j : Fin n => if (j : ℕ) < m then τ j ^ 2 else 0)
          ⟨k, hkn⟩
        simp only [hkm, if_true, hτ, lt_irrefl, if_false, Real.norm_eq_abs] at h0
        rwa [abs_of_nonneg (sq_nonneg _)] at h0
      · rw [singularValues_eq_zero_of_min_le A (not_lt.1 hk)]
        simp
  exact (sq_eq_sq₀ (specNorm_nonneg T) hσk).1 hsq

/-- **Spectral Eckart–Young, attainment.** `‖A − truncatedSVD A k‖₂ = σ_k(A)` (zero-indexed;
`0` when `k ≥ min m n`). Horn–Johnson 2013, Thm 7.4.9.1 (spectral case); HMT 2011, eq. (2.3);
audit G0 C3; atlas `eckart-young`.
atlas: eckart-young -/
theorem specNorm_sub_truncatedSVD_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    specNorm (A - truncatedSVD A k) = singularValues A k := by
  unfold truncatedSVD
  exact (exists_isSVD A).choose_spec.choose_spec.specNorm_sub_truncatedMatrix k

end NLAlib
