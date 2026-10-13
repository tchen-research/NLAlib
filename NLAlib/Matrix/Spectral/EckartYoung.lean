import NLAlib.Matrix.Basic.MoorePenrose
import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Matrix.Subspaces.ProjectorTrace
import NLAlib.Matrix.Spectral.SpectralBounds
import Mathlib.Tactic

/-!
# Eckart–Young theorem

For `A : Matrix m n 𝕜` over `ℝ` or `ℂ` (`[RCLike 𝕜]`) on arbitrary finite index types:
Frobenius form (`bestRankFrobSq_eq_bestRankFrobSq`, `isBestFrobRankApprox_truncatedSVD`) and
the spectral attainment `specNorm_sub_truncatedSVD_eq` (`‖A − A_k‖₂ = σ_k`).

The Frobenius proof compares an arbitrary rank-bounded competitor with its Moore–Penrose column-space projector. In singular-vector coordinates the
projector has diagonal weights in `[0,1]` with total mass equal to its rank.
The finite weighted top-k inequality then gives the optimal singular-value tail.

Source: Horn–Johnson, Matrix Analysis, Theorem 7.4.9; HMT 2011, §2.1.
The SVD factors are `U : Matrix m (Fin p) 𝕜`, `V : Matrix n (Fin q) 𝕜` (`IsSVD`), and the
tail `bestRankFrobSq A k = ∑_{k ≤ i < card m} σ_i²` is a sum over `Finset.range (card m)`;
at `m = Fin a` the `Fin a` sum is recovered with `Fin.sum_univ_eq_sum_range`.
Atlas: `eckart-young`. No probabilistic or inverse-Wishart bounds enter this proof.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

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
Bhatia 1997, Lemma III.1.1 / Ky Fan) atlas `eckart-young`, `von-neumann-trace`. -/
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

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

private theorem frobSq_eq_projection_add_residual [DecidableEq m]
    (P : Matrix m m 𝕜) (hs : P.IsHermitian) (hp : IsIdempotentElem P)
    (A : Matrix m n 𝕜) :
    frobSq A = frobSq (P * A) + frobSq ((1 - P) * A) := by
  have horth : Pᴴ * (1 - P) = 0 := by
    rw [hs.eq, Matrix.mul_sub, Matrix.mul_one, show P * P = P from hp, sub_self]
  have hsplit : P * A + (1 - P) * A = A := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  calc
    frobSq A = frobSq (P * A + (1 - P) * A) := congrArg frobSq hsplit.symm
    _ = _ := frobSq_add_of_frobInner_eq_zero _ _
      (frobInner_mul_mul_eq_zero P A (1 - P) A horth)

private theorem frobSq_projection_residual_le [DecidableEq m]
    (P : Matrix m m 𝕜) (hs : P.IsHermitian) (hp : IsIdempotentElem P)
    (A B : Matrix m n 𝕜) (hPB : P * B = B) :
    frobSq ((1 - P) * A) ≤ frobSq (A - B) := by
  have horth : (1 - P)ᴴ * P = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hs.eq, Matrix.sub_mul,
      Matrix.one_mul, show P * P = P from hp, sub_self]
  have hsplit : (1 - P) * A + P * (A - B) = A - B := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hPB]
    abel
  rw [← hsplit, frobSq_add_of_frobInner_eq_zero _ _
    (frobInner_mul_mul_eq_zero (1 - P) A P (A - B) horth)]
  exact le_add_of_nonneg_right (frobSq_nonneg _)

variable [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The optimal squared Frobenius error of a rank-`≤ k` approximation of `A`: the squared
singular-value tail `∑_{k ≤ i < card m} σ_i²` (Eckart–Young; the infimum form is
`bestRankFrobSq_eq_sInf`, attained by `truncatedSVD A k`). Padding includes rectangular null
directions and zero dimensions. Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: best-rank-approx-def -/
def bestRankFrobSq (A : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card m), if k ≤ i then singularValues A i ^ 2 else 0

open scoped Matrix.Norms.L2Operator in
/-- `‖Σ‖_F² = ∑_{i < min p q} σ_i²` for a rectangular diagonal matrix, written as a sum over
the rows `Fin p`. -/
private theorem frobSq_rectDiag {p q : ℕ} (σ : ℕ → ℝ) :
    frobSq (rectDiag σ : Matrix (Fin p) (Fin q) 𝕜) =
      ∑ i : Fin p, if (i : ℕ) < q then σ i ^ 2 else 0 := by
  rw [← frobSq_conjTranspose, frobSq, frobInner_eq_trace, Matrix.conjTranspose_conjTranspose,
    rectDiag_mul_conjTranspose_rectDiag, Matrix.trace_diagonal, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- With an SVD whose left factor has `p` columns, `∑_{i : Fin p} σ_i² = ‖A‖_F²`. -/
private theorem IsSVD.frobSq_eq_sum {p q : ℕ} [DecidableEq m] {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) :
    frobSq A = ∑ i : Fin p, singularValues A i ^ 2 := by
  rw [← frobSq_conjTranspose, frobSq, frobInner_eq_trace, Matrix.conjTranspose_conjTranspose,
    h.mul_conjTranspose_self, Matrix.trace_mul_cycle, h.conjTranspose_mul_left, Matrix.one_mul,
    Matrix.trace_diagonal, map_sum]
  simp

/-- **Frobenius Eckart–Young lower bound.** Every rank-at-most-`k` competitor has squared
error at least the singular-value tail. Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem bestRankFrobSq_le_frobSq_sub_of_rank_le [DecidableEq m]
    (A B : Matrix m n 𝕜) (k : ℕ) (hB : B.rank ≤ k) :
    bestRankFrobSq A k ≤ frobSq (A - B) := by
  let P := B * moorePenroseInverse B
  have hs : P.IsHermitian := mul_moorePenroseInverse_isHermitian B
  have hp : IsIdempotentElem P := mul_moorePenroseInverse_isIdempotentElem B
  have hPB : P * B = B := mul_moorePenroseInverse_mul B
  have hrankP : P.rank ≤ k := (Matrix.rank_mul_le_left B _).trans hB
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A
  let R := Uᴴ * P * U
  have hsR : R.IsHermitian := by
    change (Uᴴ * P * U)ᴴ = Uᴴ * P * U
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hs.eq,
      Matrix.mul_assoc]
  have hpR : IsIdempotentElem R := by
    change (Uᴴ * P * U) * (Uᴴ * P * U) = Uᴴ * P * U
    calc
      _ = Uᴴ * (P * (U * Uᴴ) * P) * U := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * P * U := by
        rw [hSVD.mul_conjTranspose_left, Matrix.mul_one, show P * P = P from hp]
  have hrankR : R.rank ≤ k :=
    ((Matrix.rank_mul_le_left (Uᴴ * P) U).trans (Matrix.rank_mul_le_right Uᴴ P)).trans hrankP
  have hbudget : ∑ i, RCLike.re (R i i) ≤ (k : ℝ) := by
    rw [← map_sum]
    change RCLike.re R.trace ≤ (k : ℝ)
    rw [trace_eq_rank_of_isIdempotentElem R hpR, RCLike.natCast_re]
    exact_mod_cast hrankR
  have hweights (i : Fin (Fintype.card m)) : RCLike.re (R i i) ∈ Set.Icc (0 : ℝ) 1 :=
    re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem R hsR hpR i
  have hcaptured : frobSq (P * A) =
      ∑ i : Fin (Fintype.card m), singularValues A i ^ 2 * RCLike.re (R i i) := by
    have hgram : (P * A) * (P * A)ᴴ = P * (A * Aᴴ) * P := by
      simp only [Matrix.conjTranspose_mul, hs.eq, Matrix.mul_assoc]
    set D : Matrix (Fin (Fintype.card m)) (Fin (Fintype.card m)) 𝕜 :=
      Matrix.diagonal (fun i => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    rw [← frobSq_conjTranspose, frobSq, frobInner_eq_trace, Matrix.conjTranspose_conjTranspose,
      hgram, hSVD.mul_conjTranspose_self]
    calc
      _ = RCLike.re (P * U * (D * (Uᴴ * P))).trace := by
        congr 2
        simp only [Matrix.mul_assoc, D]
      _ = RCLike.re ((D * (Uᴴ * P)) * (P * U)).trace := by rw [Matrix.trace_mul_comm]
      _ = RCLike.re (D * R).trace := by
        congr 2
        simp only [R, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P P U, show P * P = P from hp]
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, map_sum, D,
          RCLike.re_ofReal_mul]
  have hcaptured_le : frobSq (P * A) ≤
      ∑ i : Fin (Fintype.card m), if (i : ℕ) < k then singularValues A i ^ 2 else 0 := by
    rw [hcaptured]
    apply sum_mul_le_sum_ite_lt_of_antitone
    · intro i; exact sq_nonneg _
    · intro i j hij
      exact pow_le_pow_left₀ (singularValues_nonneg A j) (singularValues_antitone A hij) 2
    · intro i; exact (hweights i).1
    · intro i; exact (hweights i).2
    · exact hbudget
  have hsplit : frobSq A =
      (∑ i : Fin (Fintype.card m), if (i : ℕ) < k then singularValues A i ^ 2 else 0) +
      bestRankFrobSq A k := by
    rw [hSVD.frobSq_eq_sum, bestRankFrobSq,
      ← Fin.sum_univ_eq_sum_range (fun i => if k ≤ i then singularValues A i ^ 2 else 0),
      ← Finset.sum_add_distrib]
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

variable [DecidableEq m]

/-- Truncate a given SVD after its first `k` singular values. The index
may exceed either matrix dimension; in that case padding handles the cutoff.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: best-rank-approx-def -/
def IsSVD.truncatedMatrix {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (_h : IsSVD A U V) (k : ℕ) : Matrix m n 𝕜 :=
  U * (rectDiag (fun i => if i < k then singularValues A i else 0) :
    Matrix (Fin p) (Fin q) 𝕜) * Vᴴ

/-- The truncated SVD has rank at most its cutoff, including cutoff zero.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem IsSVD.rank_truncatedMatrix_le {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD A U V) (k : ℕ) : (h.truncatedMatrix k).rank ≤ k := by
  classical
  let S : Matrix (Fin p) (Fin q) 𝕜 :=
    rectDiag (fun i => if i < k then singularValues A i else 0)
  let H := (Finset.univ : Finset (Fin p)).filter fun i : Fin p => (i : ℕ) < k
  have hsupport : Function.support S.row ⊆ H := by
    rw [Function.support_subset_iff']
    intro i hi
    have hik : ¬(i : ℕ) < k := by simpa [H] using hi
    ext j
    change S i j = 0
    simp [S, rectDiag_apply_ofReal, hik]
  have hS : S.rank ≤ H.card := Matrix.rank_le_card_of_support_subset S H hsupport
  change (U * S * Vᴴ).rank ≤ k
  exact ((Matrix.rank_mul_le_left (U * S) Vᴴ).trans (Matrix.rank_mul_le_right U S)).trans
    (hS.trans (card_fin_head_le p k))

/-- The squared error of the truncated SVD is exactly the singular-value
tail, with no rank/dimension side conditions.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem IsSVD.frobSq_sub_truncatedMatrix {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD A U V) (k : ℕ) :
    frobSq (A - h.truncatedMatrix k) = bestRankFrobSq A k := by
  have hp := h.card_left
  have hq := h.card_right
  let T : Matrix (Fin p) (Fin q) 𝕜 :=
    rectDiag (fun i => if i < k then 0 else singularValues A i)
  have hsplit : A = h.truncatedMatrix k + U * T * Vᴴ := h.eq_head_add_tail k
  have he : A - h.truncatedMatrix k = U * T * Vᴴ := by
    calc
      _ = (h.truncatedMatrix k + U * T * Vᴴ) - h.truncatedMatrix k :=
        congrArg (fun M => M - h.truncatedMatrix k) hsplit
      _ = _ := by abel
  rw [he, frobSq_mul_right_of_orthonormal h.conjTranspose_mul_right,
    frobSq_mul_left_of_orthonormal h.conjTranspose_mul_left, frobSq_rectDiag,
    bestRankFrobSq, hp,
    ← Fin.sum_univ_eq_sum_range (fun i => if k ≤ i then singularValues A i ^ 2 else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hin : (i : ℕ) < q
  · rw [if_pos hin]
    by_cases hik : (i : ℕ) < k
    · simp [hik, not_le.mpr hik]
    · simp [hik, not_lt.mp hik]
  · rw [if_neg hin, singularValues_eq_zero_of_width_le A (by rw [hq]; exact not_lt.mp hin)]
    simp

/-- **Frobenius Eckart–Young minimizer.** Truncating any SVD gives a
best rank-at-most-`k` approximation, rather than assuming a best-approximation
predicate. Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem IsSVD.isBestFrobRankApprox_truncatedMatrix {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD A U V) (k : ℕ) : IsBestFrobRankApprox A k (h.truncatedMatrix k) := by
  refine ⟨h.rank_truncatedMatrix_le k, ?_⟩
  intro B hB
  rw [h.frobSq_sub_truncatedMatrix k]
  exact bestRankFrobSq_le_frobSq_sub_of_rank_le A B k hB

/-- A concrete rank-`k` truncated SVD, using an SVD chosen from the proved
existence theorem. No best-approximation assumption enters the definition.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: best-rank-approx-def -/
def truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  (exists_isSVD A).choose_spec.choose_spec.truncatedMatrix k

/-- The constructed truncated SVD is a best rank-at-most-`k` approximation.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: eckart-young-frobenius -/
theorem isBestFrobRankApprox_truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    IsBestFrobRankApprox A k (truncatedSVD A k) := by
  unfold truncatedSVD
  exact (exists_isSVD A).choose_spec.choose_spec.isBestFrobRankApprox_truncatedMatrix k

omit [DecidableEq m] [DecidableEq n] in
/-- A Frobenius best rank-at-most-`k` approximation exists for every
finite rectangular matrix, including empty indices and every target rank.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: eckart-young-frobenius -/
theorem exists_isBestFrobRankApprox (A : Matrix m n 𝕜) (k : ℕ) :
    ∃ B : Matrix m n 𝕜, IsBestFrobRankApprox A k B := by
  classical
  exact ⟨_, isBestFrobRankApprox_truncatedSVD A k⟩

/-- The chosen truncated SVD attains the exact singular-value-tail error.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem frobSq_sub_truncatedSVD_eq_bestRankFrobSq (A : Matrix m n 𝕜) (k : ℕ) :
    frobSq (A - truncatedSVD A k) = bestRankFrobSq A k := by
  unfold truncatedSVD
  exact (exists_isSVD A).choose_spec.choose_spec.frobSq_sub_truncatedMatrix k

omit [DecidableEq m] in
/-- Every best Frobenius rank-`k` approximation attains the optimal error `bestRankFrobSq A k`.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: eckart-young-frobenius -/
theorem IsBestFrobRankApprox.frobSq_sub_eq_bestRankFrobSq {k : ℕ} {A B : Matrix m n 𝕜}
    (h : IsBestFrobRankApprox A k B) : frobSq (A - B) = bestRankFrobSq A k := by
  classical
  rw [← frobSq_sub_truncatedSVD_eq_bestRankFrobSq A k]
  exact le_antisymm (h.2 _ (isBestFrobRankApprox_truncatedSVD A k).1)
    ((isBestFrobRankApprox_truncatedSVD A k).2 _ h.1)

omit [DecidableEq m] in
/-- The optimal rank-`k` squared Frobenius error is the infimum over all matrices of rank at
most `k` (attained by `truncatedSVD A k`). Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: eckart-young-frobenius -/
theorem bestRankFrobSq_eq_sInf (A : Matrix m n 𝕜) (k : ℕ) :
    bestRankFrobSq A k = sInf {v : ℝ | ∃ B : Matrix m n 𝕜, B.rank ≤ k ∧ v = frobSq (A - B)} := by
  classical
  have hT := isBestFrobRankApprox_truncatedSVD A k
  rw [← hT.frobSq_sub_eq_bestRankFrobSq]
  apply le_antisymm
  · exact le_csInf ⟨_, truncatedSVD A k, hT.1, rfl⟩ (by rintro v ⟨Z, hZ, rfl⟩; exact hT.2 Z hZ)
  · exact csInf_le ⟨0, by rintro v ⟨Z, _, rfl⟩; exact frobSq_nonneg _⟩ ⟨truncatedSVD A k, hT.1, rfl⟩

/-! ### Spectral-norm attainment -/

open scoped Matrix.Norms.L2Operator in
/-- **Spectral Eckart–Young, attainment for a given SVD.** The spectral error of truncating an
SVD after `k` terms is the `(k+1)`-st singular value (zero-indexed `σ_k`):
`‖A − U Σ_{<k} Vᴴ‖₂ = σ_k(A)`. All shapes and cutoffs are allowed (`σ_k = 0` for
`k ≥ min m n`). Horn–Johnson 2013, Thm 7.4.9.1 (spectral case); HMT 2011, eq. (2.3) atlas `eckart-young`. -/
theorem IsSVD.specNorm_sub_truncatedMatrix {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}
    (h : IsSVD A U V) (k : ℕ) :
    specNorm (A - h.truncatedMatrix k) = singularValues A k := by
  have hp := h.card_left
  have hq := h.card_right
  set τ : ℕ → ℝ := fun i => if i < k then 0 else singularValues A i with hτ
  let T : Matrix (Fin p) (Fin q) 𝕜 := rectDiag τ
  have hsplit : A = h.truncatedMatrix k + U * T * Vᴴ := h.eq_head_add_tail k
  have he : A - h.truncatedMatrix k = U * T * Vᴴ := by
    calc
      _ = (h.truncatedMatrix k + U * T * Vᴴ) - h.truncatedMatrix k :=
        congrArg (fun M => M - h.truncatedMatrix k) hsplit
      _ = _ := by abel
  rw [he, specNorm_mul_conjTranspose_right_of_hasOrthonormalCols h.conjTranspose_mul_right,
    specNorm_mul_left_of_hasOrthonormalCols h.conjTranspose_mul_left]
  have hσk := singularValues_nonneg A k
  have hsq : specNorm T ^ 2 = singularValues A k ^ 2 := by
    rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self, conjTranspose_rectDiag_mul_rectDiag,
      specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2 fun j => ?_
      split_ifs with hj
      · rw [RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _)]
        simp only [hτ]
        split_ifs with hjk
        · simpa using sq_nonneg (singularValues A k)
        · exact pow_le_pow_left₀ (singularValues_nonneg A j)
            (singularValues_antitone A (not_lt.1 hjk)) 2
      · simpa using sq_nonneg (singularValues A k)
    · by_cases hk : k < min p q
      · have hkm : k < p := lt_of_lt_of_le hk (min_le_left p q)
        have hkn : k < q := lt_of_lt_of_le hk (min_le_right p q)
        have h0 := norm_le_pi_norm (fun j : Fin q =>
          if (j : ℕ) < p then ((τ j ^ 2 : ℝ) : 𝕜) else 0) ⟨k, hkn⟩
        simp only [hkm, if_true, hτ, lt_irrefl, if_false, RCLike.norm_ofReal] at h0
        rwa [abs_of_nonneg (sq_nonneg _)] at h0
      · rw [singularValues_eq_zero_of_min_le A (by rw [hp, hq]; exact not_lt.1 hk)]
        simp
  exact (sq_eq_sq₀ (specNorm_nonneg T) hσk).1 hsq

open scoped Matrix.Norms.L2Operator in
/-- **Spectral Eckart–Young, attainment.** `‖A − truncatedSVD A k‖₂ = σ_k(A)` (zero-indexed;
`0` when `k ≥ min m n`). Horn–Johnson 2013, Thm 7.4.9.1 (spectral case); HMT 2011, eq. (2.3) atlas `eckart-young`.
atlas: eckart-young -/
theorem specNorm_sub_truncatedSVD_eq (A : Matrix m n 𝕜) (k : ℕ) :
    specNorm (A - truncatedSVD A k) = singularValues A k := by
  unfold truncatedSVD
  exact (exists_isSVD A).choose_spec.choose_spec.specNorm_sub_truncatedMatrix k

end NLAlib
