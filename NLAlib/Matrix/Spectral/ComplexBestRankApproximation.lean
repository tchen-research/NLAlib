import NLAlib.Matrix.Spectral.ComplexGramTruncation
/-!
# Actual complex optimal rank-constrained Frobenius error

The infimum is over all complex matrices of rank at most `k`, and the literal
Gram singular-vector truncation attains it. Source: Horn–Johnson Theorem
7.4.9; `sa:volume-theorem`; supports `volume-sampling`.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical Matrix Matrix.Norms.Frobenius
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The genuine best complex rank-at-most-`k` squared Frobenius error, as
an infimum over all feasible complex competitors. Source: `sa:volume-theorem`. -/
def complexBestRankFrobSq (k : ℕ) (A : Matrix m n ℂ) : ℝ :=
  sInf {r : ℝ | ∃ B : Matrix m n ℂ, B.rank ≤ k ∧ r = ‖A - B‖ ^ 2}

/-- The actual complex best rank-constrained Frobenius error equals the
sorted Gram eigenvalue tail, at every rank and rectangular shape.
Source: Horn–Johnson Theorem 7.4.9; `sa:volume-theorem`.
atlas: volume-sampling (partial) -/
theorem complexBestRankFrobSq_eq_complexGramTail (A : Matrix m n ℂ) (k : ℕ) :
    complexBestRankFrobSq k A = complexGramTail A k := by
  let S := {r : ℝ | ∃ B : Matrix m n ℂ, B.rank ≤ k ∧ r = ‖A - B‖ ^ 2}
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨B, _, rfl⟩
    exact sq_nonneg _
  have hmem : ‖A - complexTruncatedSVD A k‖ ^ 2 ∈ S :=
    ⟨complexTruncatedSVD A k, rank_complexTruncatedSVD_le A k, rfl⟩
  change sInf S = complexGramTail A k
  apply le_antisymm
  · have h := csInf_le hbdd hmem
    rwa [frobenius_norm_sq_sub_complexTruncatedSVD_eq_tail] at h
  · apply le_csInf ⟨_, hmem⟩
    rintro r ⟨B, hB, rfl⟩
    exact complexGramTail_le_frobenius_norm_sq_sub_of_rank_le A B k hB

/-- The literal complex singular-vector truncation attains the actual
best rank-constrained error. Source: `sa:volume-theorem`. -/
theorem frobenius_norm_sq_sub_complexTruncatedSVD_eq_bestRank
    (A : Matrix m n ℂ) (k : ℕ) :
    ‖A - complexTruncatedSVD A k‖ ^ 2 = complexBestRankFrobSq k A := by
  rw [frobenius_norm_sq_sub_complexTruncatedSVD_eq_tail, complexBestRankFrobSq_eq_complexGramTail]

/-- The actual optimal complex Frobenius error is the squared singular-value
tail, with the prescribed zero-indexed cutoff.
Source: Horn–Johnson Theorem 7.4.9; `sa:volume-theorem`. -/
theorem complexBestRankFrobSq_eq_sum_singularValues_sq (A : Matrix m n ℂ) (k : ℕ) :
    complexBestRankFrobSq k A =
      ∑ i : Fin (Fintype.card n), if k ≤ (i : ℕ) then singularValues A i ^ 2 else 0 := by
  rw [complexBestRankFrobSq_eq_complexGramTail, complexGramTail]
  simp only [sq_singularValues_eq_eigenvalues₀, complexGramEigenvalues]

end NLAlib
