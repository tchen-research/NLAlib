import NLAlib.Matrix.MoorePenrose
import NLAlib.Matrix.EckartYoung
import NLAlib.Matrix.Projections

/-!
# Leverage scores

The leverage score of row `i` of a real matrix `A` is the `i`-th diagonal entry of the
orthogonal projector onto `range A`, `ℓᵢ(A) = (A A⁺)ᵢᵢ` (`NLAlib.leverageScore`).

* `leverageScore_nonneg`, `leverageScore_le_one`: `0 ≤ ℓᵢ ≤ 1`;
* `sum_leverageScore_eq_rank`: `∑ᵢ ℓᵢ = rank A`;
* `leverageScore_eq_sum_sq_of_hasOrthonormalCols`: for any orthonormal basis `U` of
  `range A`, `ℓᵢ = ‖U_{i,:}‖²`; in particular the row norms do not depend on the basis.

The basis-independence step is the projector identity
`mul_transpose_eq_mul_moorePenroseInverse`: if `Q` has orthonormal columns, `range Y ⊆ range Q`
and `rank Y` is at least the number of columns of `Q`, then `QQᵀ = Y Y⁺`. It is also used for the
randomized Nyström bound (`NLAlib.LowRank.Nystrom`).

Source: Drineas–Mahoney–Muthukrishnan–Woodruff 2012, §1–2; Woodruff 2014, §2.4;
Martinsson–Tropp 2020, §9.6. Atlas: `leverage-scores`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-- The rank of the Moore–Penrose column-space projector `A A⁺` is the rank of `A`.
Horn–Johnson §7.3; atlas `pseudoinverse` (helper for `leverage-scores`). -/
theorem rank_mul_moorePenroseInverse (A : Matrix m n ℝ) :
    (A * moorePenroseInverse A).rank = A.rank := by
  refine le_antisymm (Matrix.rank_mul_le_left _ _) ?_
  calc A.rank = (A * moorePenroseInverse A * A).rank := by rw [mul_moorePenroseInverse_mul]
    _ ≤ (A * moorePenroseInverse A).rank := Matrix.rank_mul_le_left _ _

/-- The trace of the Moore–Penrose column-space projector is the rank: `tr(A A⁺) = rank A`.
Horn–Johnson §7.3; atlas `pseudoinverse` (helper for `leverage-scores`). -/
theorem trace_mul_moorePenroseInverse [DecidableEq m] (A : Matrix m n ℝ) :
    (A * moorePenroseInverse A).trace = (A.rank : ℝ) := by
  rw [trace_eq_rank_of_isIdempotentElem _ (mul_moorePenroseInverse_isIdempotentElem A),
    rank_mul_moorePenroseInverse]

/-- **Uniqueness of the orthogonal projector onto a range.** If `Q` has orthonormal columns,
`range Y ⊆ range Q` (written `Q (Qᵀ Y) = Y`) and `rank Y` is at least the number of columns of
`Q` (so the two ranges coincide), then `QQᵀ = Y Y⁺`.

Proof: `P₁ = QQᵀ` and `P₂ = YY⁺` are symmetric idempotents with `P₁P₂ = P₂ = P₂P₁`, so
`M = P₁ − P₂` is a symmetric idempotent and `‖M‖_F² = tr M = card q − rank Y ≤ 0`.
Standard (Golub–Van Loan, 4th ed., §2.5.1: the orthogonal projector onto a subspace is unique).
Atlas `leverage-scores` (basis independence), `projection-facts`. Belongs in
`Matrix/MoorePenrose.lean`. -/
theorem mul_transpose_eq_mul_moorePenroseInverse [DecidableEq m] [DecidableEq q]
    {Q : Matrix m q ℝ} (hQ : HasOrthonormalCols Q) {Y : Matrix m n ℝ}
    (hQY : Q * (Qᵀ * Y) = Y) (hr : Fintype.card q ≤ Y.rank) :
    Q * Qᵀ = Y * moorePenroseInverse Y := by
  set P₁ := Q * Qᵀ with hP₁
  set P₂ := Y * moorePenroseInverse Y with hP₂
  have hP₁s : P₁ᵀ = P₁ := mul_transpose_symm Q
  have hP₂s : P₂ᵀ = P₂ := (mul_moorePenroseInverse_isSymm Y).eq
  have hP₁i : P₁ * P₁ = P₁ := mul_transpose_mul_mul_transpose hQ
  have hP₂i : P₂ * P₂ = P₂ := mul_moorePenroseInverse_isIdempotentElem Y
  have h12 : P₁ * P₂ = P₂ := by
    rw [hP₁, hP₂, ← Matrix.mul_assoc, Matrix.mul_assoc Q, hQY]
  have h21 : P₂ * P₁ = P₂ := by
    have := congrArg Matrix.transpose h12
    rwa [Matrix.transpose_mul, hP₁s, hP₂s] at this
  set M := P₁ - P₂ with hM
  have hMs : Mᵀ = M := by rw [hM, Matrix.transpose_sub, hP₁s, hP₂s]
  have hMi : M * M = M := by
    rw [hM, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP₁i, h12, h21, hP₂i]
    abel
  have htr1 : P₁.trace = (Fintype.card q : ℝ) := by
    rw [hP₁, Matrix.trace_mul_comm, hQ, Matrix.trace_one]
  have htr2 : P₂.trace = (Y.rank : ℝ) := trace_mul_moorePenroseInverse Y
  have hfrob : frobSq M = (Fintype.card q : ℝ) - Y.rank := by
    rw [frobSq, frobInner_eq_trace, hMs, hMi, hM, Matrix.trace_sub, htr1, htr2]
  have hle : frobSq M ≤ 0 := by
    rw [hfrob]
    have : ((Fintype.card q : ℕ) : ℝ) ≤ Y.rank := by exact_mod_cast hr
    linarith
  have hM0 : M = 0 := (frobSq_eq_zero_iff M).1 (le_antisymm hle (frobSq_nonneg M))
  exact sub_eq_zero.1 hM0

/-- The **leverage score** of row `i` of `A`: `ℓᵢ(A) = (A A⁺)ᵢᵢ`, the `i`-th diagonal entry of
the orthogonal projector onto `range A`. Defined for every real matrix (any rank, empty
shapes). Drineas–Mahoney–Muthukrishnan–Woodruff 2012, Def. 1; Woodruff 2014, Def. 2.12.
Atlas `leverage-scores`.
atlas: leverage-scores -/
def leverageScore (A : Matrix m n ℝ) (i : m) : ℝ := (A * moorePenroseInverse A) i i

/-- `0 ≤ ℓᵢ(A)`. Woodruff 2014, §2.4; atlas `leverage-scores`.
atlas: leverage-scores -/
theorem leverageScore_nonneg (A : Matrix m n ℝ) (i : m) : 0 ≤ leverageScore A i :=
  (diag_mem_Icc_of_isSymm_of_isIdempotentElem _ (mul_moorePenroseInverse_isSymm A).eq
    (mul_moorePenroseInverse_isIdempotentElem A) i).1

/-- `ℓᵢ(A) ≤ 1`. Woodruff 2014, §2.4; atlas `leverage-scores`.
atlas: leverage-scores -/
theorem leverageScore_le_one (A : Matrix m n ℝ) (i : m) : leverageScore A i ≤ 1 :=
  (diag_mem_Icc_of_isSymm_of_isIdempotentElem _ (mul_moorePenroseInverse_isSymm A).eq
    (mul_moorePenroseInverse_isIdempotentElem A) i).2

/-- The leverage scores sum to the rank: `∑ᵢ ℓᵢ(A) = rank A`. Woodruff 2014, §2.4
(for full column rank, `∑ᵢ ℓᵢ = d`); atlas `leverage-scores`.
atlas: leverage-scores -/
theorem sum_leverageScore_eq_rank [DecidableEq m] (A : Matrix m n ℝ) :
    ∑ i, leverageScore A i = (A.rank : ℝ) := by
  rw [← trace_mul_moorePenroseInverse A]
  rfl

/-- **Leverage scores are squared row norms of any orthonormal basis.** If `U` has
orthonormal columns and is a basis of `range A` (`range A ⊆ range U`, written `U (Uᵀ A) = A`,
and `U` has at most `rank A` columns), then `ℓᵢ(A) = ∑ⱼ Uᵢⱼ² = ‖U_{i,:}‖²`. Since the left side
does not mention `U`, the row norms do not depend on the choice of basis.
Drineas–Mahoney–Muthukrishnan–Woodruff 2012, Def. 1 and the remark after it; Woodruff 2014,
Def. 2.12. Atlas `leverage-scores`. Deviation: "orthonormal basis of `range A`" is spelled as the
two hypotheses `hUA`, `hr` (together with orthonormality they force `range U = range A`).
atlas: leverage-scores -/
theorem leverageScore_eq_sum_sq_of_hasOrthonormalCols [DecidableEq m] [DecidableEq q]
    {A : Matrix m n ℝ} {U : Matrix m q ℝ} (hU : HasOrthonormalCols U)
    (hUA : U * (Uᵀ * A) = A) (hr : Fintype.card q ≤ A.rank) (i : m) :
    leverageScore A i = ∑ j, U i j ^ 2 := by
  unfold leverageScore
  rw [← mul_transpose_eq_mul_moorePenroseInverse hU hUA hr, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, sq]

/-- For a matrix `U` with orthonormal columns, `ℓᵢ(U) = ∑ⱼ Uᵢⱼ²`.
Woodruff 2014, §2.4; atlas `leverage-scores`. -/
theorem leverageScore_eq_sum_sq_of_self [DecidableEq m] [DecidableEq q] {U : Matrix m q ℝ}
    (hU : HasOrthonormalCols U) (i : m) : leverageScore U i = ∑ j, U i j ^ 2 := by
  have hUU : U * (Uᵀ * U) = U := by rw [hU, Matrix.mul_one]
  have hr : Fintype.card q ≤ U.rank := by
    have h1 : (Uᵀ * U).rank ≤ U.rank := Matrix.rank_mul_le_right _ _
    rw [hU, Matrix.rank_one] at h1
    exact h1
  exact leverageScore_eq_sum_sq_of_hasOrthonormalCols hU hUU hr i

end NLAlib
