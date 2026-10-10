import NLAlib.Matrix.EckartYoung
import NLAlib.Matrix.RankNorm

/-!
# Matrix norm and best-rank results on arbitrary finite indices

Atlas: `norms-frob-spec`, `pseudoinverse`, `eckart-young`, `svd`.
Equivalent row and column labels preserve rank, norms, the Moore–Penrose
inverse and the actual rank-constrained optimum, including empty index types.
This exposes general finite-index results without another spelling of matrix
norms or optimal error. The parent singular-value API is presently `Fin`-indexed;
statements involving its list explicitly normalize to `Fin (Fintype.card _)`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- Relabeling rows and columns preserves the squared Frobenius norm.
Horn–Johnson §5.6; atlas `norms-frob-spec`. Empty indices are allowed. -/
theorem frobSq_reindex (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    frobSq (A.reindex em en) = frobSq A := by
  rw [frobSq_eq_sum_sq, frobSq_eq_sum_sq]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  calc
    _ = ∑ i : m, ∑ j : q, A i (en.symm j) ^ 2 :=
      em.symm.sum_comp (fun i : m => ∑ j : q, A i (en.symm j) ^ 2)
    _ = _ := Finset.sum_congr rfl (fun i _ => en.symm.sum_comp (fun j : n => A i j ^ 2))

/-- Relabeling rows and columns preserves the Frobenius norm.
Horn–Johnson §5.6; atlas `norms-frob-spec`. -/
theorem frobNorm_reindex (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    frobNorm (A.reindex em en) = frobNorm A := by
  rw [frobNorm, frobNorm, frobSq_reindex]

private theorem reindex_frame_orth [DecidableEq m] (em : m ≃ p) :
    ((1 : Matrix m m ℝ).submatrix em.symm id)ᵀ *
      (1 : Matrix m m ℝ).submatrix em.symm id = 1 := by
  rw [Matrix.transpose_submatrix, Matrix.transpose_one]
  simpa only [Matrix.submatrix_id_id, Matrix.mul_one] using
    Matrix.submatrix_mul_equiv (1 : Matrix m m ℝ) (1 : Matrix m m ℝ)
      id em.symm id

/-- Equivalent row and column labels preserve the spectral norm, by
orthogonal permutation frames. Horn–Johnson §5.6; atlas `norms-frob-spec`. -/
theorem specNorm_reindex [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    specNorm (A.reindex em en) = specNorm A := by
  let P : Matrix p m ℝ := (1 : Matrix m m ℝ).submatrix em.symm id
  let Q : Matrix q n ℝ := (1 : Matrix n n ℝ).submatrix en.symm id
  have hP : Pᵀ * P = 1 := reindex_frame_orth em
  have hQ : Qᵀ * Q = 1 := reindex_frame_orth en
  have hleft : P * A = A.submatrix em.symm id := by
    simpa only [P, Equiv.refl_symm, Equiv.coe_refl, Function.id_comp, Function.comp_id] using
      Matrix.one_submatrix_mul em.symm (Equiv.refl m) A
  have hright : (A.submatrix em.symm id) * Qᵀ = A.reindex em en := by
    rw [show Qᵀ = (1 : Matrix n n ℝ).submatrix id en.symm by
      simp only [Q, Matrix.transpose_submatrix, Matrix.transpose_one]]
    simpa only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.refl_symm, Equiv.coe_refl,
      Function.id_comp, Function.comp_id] using
      Matrix.mul_submatrix_one (Equiv.refl n) en.symm (A.submatrix em.symm id)
  rw [← hright, ← hleft,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hQ,
    specNorm_mul_left_of_hasOrthonormalCols hP]

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
Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
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
rank on arbitrary finite indices. Horn–Johnson §5.6; atlas `norms-frob-spec`. -/
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
atlas `pseudoinverse`. The list uses explicit `Fin(card)` normalization. -/
theorem specNorm_moorePenroseInverse_eq_fintype [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    specNorm (moorePenroseInverse A) = if A.rank = 0 then 0 else
      1 / singularValues (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) (A.rank - 1) := by
  have h := specNorm_moorePenroseInverse_eq
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  simpa only [moorePenroseInverse_reindex, specNorm_reindex, Matrix.rank_reindex] using h

/-- Frobenius Eckart–Young identifies the genuine optimal error on arbitrary
finite indices with the singular-value tail of the explicit `Fin(card)`
normalization. Horn–Johnson Theorem 7.4.9; atlas `eckart-young`. -/
theorem bestRankFrobSq_eq_singularValueTailSq_reindex (A : Matrix m n ℝ) (k : ℕ) :
    bestRankFrobSq k A =
      singularValueTailSq (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) k := by
  rw [← bestRankFrobSq_reindex A k (Fintype.equivFin m) (Fintype.equivFin n),
    bestRankFrobSq_eq_singularValueTailSq]

end NLAlib
