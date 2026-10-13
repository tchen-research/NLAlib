import NLAlib.Matrix.Basic.MoorePenroseRank
import NLAlib.Matrix.Subspaces.Projections
import NLAlib.Matrix.Subspaces.ProjectorTrace
import NLAlib.Matrix.Norms.Core
/-!
# The Moore–Penrose column-space projector

Over `ℝ` or `ℂ` (`[RCLike 𝕜]`):

* `trace_mul_moorePenroseInverse`: `tr(A A⁺) = rank A`;
* `mul_conjTranspose_eq_mul_moorePenroseInverse`: uniqueness of the orthogonal projector onto a
  range: if `Q` has orthonormal columns, `range Y ⊆ range Q` and `rank Y ≥` the number of
  columns of `Q`, then `QQᴴ = Y Y⁺`.

Used by leverage scores (`NLAlib.Sketching.Sampling.Leverage`) and the randomized Nyström bound
(`NLAlib.LowRank.Nystrom.Structural`). Source: Horn–Johnson 2013, §7.3; Golub–Van Loan 2013,
§2.5.1. Atlas: helpers of `pseudoinverse`, `leverage-scores`, `projection-facts`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-- The trace of the Moore–Penrose column-space projector is the rank: `tr(A A⁺) = rank A`.
Horn–Johnson §7.3; atlas `pseudoinverse` (helper for `leverage-scores`). -/
theorem trace_mul_moorePenroseInverse [DecidableEq m] (A : Matrix m n 𝕜) :
    (A * moorePenroseInverse A).trace = (A.rank : 𝕜) := by
  rw [trace_eq_rank_of_isIdempotentElem _ (mul_moorePenroseInverse_isIdempotentElem A),
    rank_mul_moorePenroseInverse]

/-- **Uniqueness of the orthogonal projector onto a range.** If `Q` has orthonormal columns,
`range Y ⊆ range Q` (written `Q (Qᴴ Y) = Y`) and `rank Y` is at least the number of columns of
`Q` (so the two ranges coincide), then `QQᴴ = Y Y⁺`.

Proof: `P₁ = QQᴴ` and `P₂ = YY⁺` are Hermitian idempotents with `P₁P₂ = P₂ = P₂P₁`, so
`M = P₁ − P₂` is a Hermitian idempotent and `‖M‖_F² = re tr M = card q − rank Y ≤ 0`.
Standard (Golub–Van Loan, 4th ed., §2.5.1: the orthogonal projector onto a subspace is unique).
Atlas `leverage-scores` (basis independence), `projection-facts`. -/
theorem mul_conjTranspose_eq_mul_moorePenroseInverse [DecidableEq m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) {Y : Matrix m n 𝕜}
    (hQY : Q * (Qᴴ * Y) = Y) (hr : Fintype.card q ≤ Y.rank) :
    Q * Qᴴ = Y * moorePenroseInverse Y := by
  set P₁ := Q * Qᴴ with hP₁
  set P₂ := Y * moorePenroseInverse Y with hP₂
  have hP₁s : P₁ᴴ = P₁ := Matrix.isHermitian_mul_conjTranspose_self Q
  have hP₂s : P₂ᴴ = P₂ := mul_moorePenroseInverse_isHermitian Y
  have hP₁i : P₁ * P₁ = P₁ := mul_conjTranspose_mul_mul_conjTranspose hQ
  have hP₂i : P₂ * P₂ = P₂ := mul_moorePenroseInverse_isIdempotentElem Y
  have h12 : P₁ * P₂ = P₂ := by
    rw [hP₁, hP₂, ← Matrix.mul_assoc, Matrix.mul_assoc Q, hQY]
  have h21 : P₂ * P₁ = P₂ := by
    have := congrArg Matrix.conjTranspose h12
    rwa [Matrix.conjTranspose_mul, hP₁s, hP₂s] at this
  set M := P₁ - P₂ with hM
  have hMs : Mᴴ = M := by rw [hM, Matrix.conjTranspose_sub, hP₁s, hP₂s]
  have hMi : M * M = M := by
    rw [hM, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP₁i, h12, h21, hP₂i]
    abel
  have htr1 : P₁.trace = (Fintype.card q : 𝕜) := by
    rw [hP₁, Matrix.trace_mul_comm, hQ.conjTranspose_mul_self, Matrix.trace_one]
  have htr2 : P₂.trace = (Y.rank : 𝕜) := trace_mul_moorePenroseInverse Y
  have hfrob : frobSq M = (Fintype.card q : ℝ) - Y.rank := by
    rw [frobSq, frobInner_eq_trace, hMs, hMi, hM, Matrix.trace_sub, htr1, htr2, map_sub,
      RCLike.natCast_re, RCLike.natCast_re]
  have hle : frobSq M ≤ 0 := by
    rw [hfrob]
    have : ((Fintype.card q : ℕ) : ℝ) ≤ Y.rank := by exact_mod_cast hr
    linarith
  have hM0 : M = 0 := (frobSq_eq_zero_iff M).1 (le_antisymm hle (frobSq_nonneg M))
  exact sub_eq_zero.1 hM0

end NLAlib
