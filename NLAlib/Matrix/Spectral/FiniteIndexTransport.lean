import NLAlib.Matrix.Spectral.EckartYoung
import NLAlib.Matrix.Norms.RankNorm
import NLAlib.Matrix.Norms.Reindex
import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!
# Matrix norm and best-rank results on arbitrary finite indices

Atlas: `norms-frob-spec`, `pseudoinverse`, `eckart-young`, `svd`.
Equivalent row and column labels preserve rank, the Moore–Penrose
inverse and the actual rank-constrained optimum, including empty index types
(the norm invariances are in `NLAlib.Matrix.Norms.Reindex`).
This exposes general finite-index results without another spelling of matrix
norms or optimal error. The parent singular-value API is presently `Fin`-indexed;
statements involving its list explicitly normalize to `Fin (Fintype.card _)`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- Equivalent row, middle, and column labels commute with rectangular matrix
multiplication. Mathlib's submatrix multiplication transport; supports
`wedin-sin-theta` on arbitrary finite coordinate labels. -/
theorem mul_reindex {m n p m' n' p' : Type*} [Fintype n] [Fintype n']
    (A : Matrix m n ℝ) (B : Matrix n p ℝ)
    (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p') :
    (A * B).reindex em ep = A.reindex em en * B.reindex en ep := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- Relabeling an actual best-rank approximation preserves its minimizing
property. Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem IsBestRankApprox.reindex {k : ℕ} {A B : Matrix m n ℝ}
    (h : IsBestRankApprox k A B) (em : m ≃ p) (en : n ≃ q) :
    IsBestRankApprox k (A.reindex em en) (B.reindex em en) := by
  constructor
  · simpa only [Matrix.rank_reindex] using h.1
  · intro Z hZ
    have hh := h.2 (Z.reindex em.symm en.symm)
      (by simpa only [Matrix.rank_reindex] using hZ)
    have hdiff : A.reindex em en - Z = (A - Z.reindex em.symm en.symm).reindex em en := by
      ext i j
      simp
    have hsub : A.reindex em en - B.reindex em en = (A - B).reindex em en := rfl
    rw [hsub, hdiff, frobSq_reindex, frobSq_reindex]
    exact hh

/-- An actual Frobenius best rank-at-most-`k` approximation exists for every
finite rectangular real matrix, including empty indices and every target rank.
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: eckart-young-frobenius -/
theorem exists_isBestRankApprox (A : Matrix m n ℝ) (k : ℕ) :
    ∃ B : Matrix m n ℝ, IsBestRankApprox k A B := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let AF := A.reindex em en
  have hh := (isBestRankApprox_truncatedSVD AF k).reindex em.symm en.symm
  have hback : AF.reindex em.symm en.symm = A := by ext i j; simp [AF]
  rw [hback] at hh
  exact ⟨_, hh⟩

/-- Equivalent row and column labels preserve the actual rank-constrained
optimal squared Frobenius error. Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem bestRankFrobSq_reindex (A : Matrix m n ℝ) (k : ℕ)
    (em : m ≃ p) (en : n ≃ q) :
    bestRankFrobSq k (A.reindex em en) = bestRankFrobSq k A := by
  unfold bestRankFrobSq
  congr 1
  ext v
  constructor
  · rintro ⟨B, hB, rfl⟩
    refine ⟨B.reindex em.symm en.symm, ?_, ?_⟩
    · simpa only [Matrix.rank_reindex] using hB
    · have he : A.reindex em en - B = (A - B.reindex em.symm en.symm).reindex em en := by
        ext i j
        simp
      rw [he, frobSq_reindex]
  · rintro ⟨B, hB, rfl⟩
    refine ⟨B.reindex em en, ?_, ?_⟩
    · simpa only [Matrix.rank_reindex] using hB
    · rw [show A.reindex em en - B.reindex em en = (A - B).reindex em en from rfl,
        frobSq_reindex]

/-- Every best Frobenius rank-`k` approximation attains the genuine infimum,
on arbitrary finite indices. Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem IsBestRankApprox.frobSq_sub_eq_bestRankFrobSq {k : ℕ} {A B : Matrix m n ℝ}
    (h : IsBestRankApprox k A B) : frobSq (A - B) = bestRankFrobSq k A := by
  let S := {v : ℝ | ∃ Z : Matrix m n ℝ, Z.rank ≤ k ∧ v = frobSq (A - Z)}
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro v ⟨Z, _, rfl⟩
    exact frobSq_nonneg _
  have hmem : frobSq (A - B) ∈ S := ⟨B, h.1, rfl⟩
  change frobSq (A - B) = sInf S
  apply le_antisymm
  · apply le_csInf ⟨_, hmem⟩
    rintro v ⟨Z, hZ, rfl⟩
    exact h.2 Z hZ
  · exact csInf_le hbdd hmem

/-- The squared Frobenius norm is bounded by rank times squared spectral
norm for arbitrary finite real matrices. Horn–Johnson §5.6;
atlas `norms-frob-spec`. No nonempty or positive-rank condition is imposed. -/
theorem frobSq_le_rank_mul_specNorm_sq_fintype [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    frobSq A ≤ (A.rank : ℝ) * specNorm A ^ 2 := by
  have h := frobSq_le_rank_mul_specNorm_sq
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  simpa only [frobSq_reindex, Matrix.rank_reindex, specNorm_reindex] using h

/-- The Frobenius norm is at most the spectral norm times square root of
rank on arbitrary finite indices. Horn–Johnson §5.6; atlas `norms-frob-spec`.
atlas: norms-frob-spec -/
theorem frobNorm_le_sqrt_rank_mul_specNorm_fintype [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    frobNorm A ≤ Real.sqrt (A.rank : ℝ) * specNorm A := by
  have h := frobNorm_le_sqrt_rank_mul_specNorm
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  simpa only [frobNorm_reindex, Matrix.rank_reindex, specNorm_reindex] using h

/-- Reindexing commutes with the general Moore–Penrose inverse, reversing
row and column labels. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem moorePenroseInverse_reindex (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    moorePenroseInverse (A.reindex em en) = (moorePenroseInverse A).reindex en em :=
  (isMoorePenroseInverse (A.reindex em en)).unique
    ((isMoorePenroseInverse A).submatrix em.symm en.symm)

/-- The largest singular value of the explicit finite normalization is the
original spectral norm. Horn–Johnson §5.6; atlas `svd`, `norms-frob-spec`.
The reindex is temporary normalization for the parent `Fin`-only list API. -/
theorem singularValues_reindex_zero_eq_specNorm [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    singularValues (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) 0 =
      specNorm A := by
  rw [singularValues_zero_eq_specNorm, specNorm_reindex]

/-- The Moore–Penrose norm on general indices is zero at rank zero and the
reciprocal of the last positive singular value otherwise. Horn–Johnson §7.3;
atlas `pseudoinverse`. The list uses explicit `Fin(card)` normalization.
atlas: pseudoinverse -/
theorem specNorm_moorePenroseInverse_eq_fintype [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    specNorm (moorePenroseInverse A) = if A.rank = 0 then 0 else
      1 / singularValues (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) (A.rank - 1) := by
  have h := specNorm_moorePenroseInverse_eq
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  simpa only [moorePenroseInverse_reindex, specNorm_reindex, Matrix.rank_reindex] using h

/-- Frobenius Eckart–Young identifies the genuine optimal error on arbitrary
finite indices with the singular-value tail of the explicit `Fin(card)`
normalization. Horn–Johnson Theorem 7.4.9; atlas `eckart-young`.
atlas: eckart-young-frobenius -/
theorem bestRankFrobSq_eq_singularValueTailSq_reindex (A : Matrix m n ℝ) (k : ℕ) :
    bestRankFrobSq k A =
      singularValueTailSq (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) k := by
  rw [← bestRankFrobSq_reindex A k (Fintype.equivFin m) (Fintype.equivFin n),
    bestRankFrobSq_eq_singularValueTailSq]

end NLAlib
