import NLAlib.Matrix.Inequalities.KyFanFiniteIndex
import Mathlib.Algebra.Order.Chebyshev

/-!
# Nuclear norm duality and sharp rank comparisons

The spectral-contraction maximum is attained by the singular-vector partial
isometry. Exact rank support gives the comparison constants, including rank zero.
Source: Horn–Johnson (1991), Corollary 3.4.4; Bhatia (1997), §IV.2.
Atlas: `ky-fan-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- Only the actual positive singular-value rank prefix contributes to the
nuclear norm, including the zero rank. -/
theorem nuclearNorm_eq_sum_rank_singularValues {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A = ∑ i ∈ Finset.range A.rank, singularValues A i := by
  simp only [nuclearNorm, Fintype.card_fin]
  change (∑ i ∈ Finset.range (min m n), singularValues A i) = _
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (le_min A.rank_le_height A.rank_le_width))
  intro i _ hi
  exact singularValues_eq_zero_of_rank_le A (by simpa only [Finset.mem_range, not_lt] using hi)

/-- The nuclear norm is nonnegative. -/
theorem nuclearNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : 0 ≤ nuclearNorm A := kyFanNorm_nonneg A _

/-- A rank-`r` matrix has nuclear norm at most `r` times its spectral norm.
The coefficient is the actual rank, with no positivity assumption. -/
theorem nuclearNorm_le_rank_mul_specNorm_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A ≤ (A.rank : ℝ) * specNorm A := by
  rw [nuclearNorm_eq_sum_rank_singularValues]
  calc
    (∑ i ∈ Finset.range A.rank, singularValues A i) ≤ ∑ _i ∈ Finset.range A.rank, specNorm A :=
      Finset.sum_le_sum fun i _ => singularValues_le_specNorm A i
    _ = (A.rank : ℝ) * specNorm A := by simp

/-- The Frobenius norm is bounded by the nuclear norm, including rank zero. -/
theorem frobNorm_le_nuclearNorm_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobNorm A ≤ nuclearNorm A := by
  have hf : frobNorm A ^ 2 = ∑ i ∈ Finset.range A.rank, singularValues A i ^ 2 := by
    rw [frobNorm_sq, frobSq_eq_sum_rank_singularValues_sq]
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.range A.rank) (fun i _ => singularValues_nonneg A i)
  rw [← hf, ← nuclearNorm_eq_sum_rank_singularValues A] at hs
  nlinarith [frobNorm_nonneg A, nuclearNorm_nonneg A]

/-- The nuclear norm is bounded by the square root of the actual rank times the
Frobenius norm. The zero matrix is covered with constant zero. -/
theorem nuclearNorm_le_sqrt_rank_mul_frobNorm_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A ≤ Real.sqrt A.rank * frobNorm A := by
  have hf : frobNorm A ^ 2 = ∑ i ∈ Finset.range A.rank, singularValues A i ^ 2 := by
    rw [frobNorm_sq, frobSq_eq_sum_rank_singularValues_sq]
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.range A.rank) (f := singularValues A)
  rw [Finset.card_range, ← nuclearNorm_eq_sum_rank_singularValues A, ← hf] at hs
  have hsq : nuclearNorm A ^ 2 ≤ (Real.sqrt A.rank * frobNorm A) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg A.rank)]
    exact hs
  have hn : 0 ≤ Real.sqrt A.rank * frobNorm A := mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg A)
  nlinarith [nuclearNorm_nonneg A]

/-- Every spectral contraction has Frobenius pairing bounded by the nuclear
norm, with no rank or nonempty dimension assumption. -/
theorem frobInner_le_nuclearNorm_of_specNorm_le_one_fin {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (hB : specNorm B ≤ 1) :
    frobInner A B ≤ nuclearNorm A := by
  exact frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one A B
    (by simpa using le_min B.rank_le_height B.rank_le_width) hB

/-- An actual spectral contraction attains the nuclear norm dual pairing.
The attaining partial isometry is built from the SVD and includes empty shapes. -/
theorem exists_specNorm_le_one_frobInner_eq_nuclearNorm_fin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ B : Matrix (Fin m) (Fin n) ℝ, specNorm B ≤ 1 ∧ frobInner A B = nuclearNorm A := by
  obtain ⟨U, V, hU, hV, htrace⟩ := exists_trace_twoSided_compression_eq_kyFanNorm A le_rfl
  refine ⟨U * Vᵀ, ?_, ?_⟩
  · rw [specNorm_mul_transpose_right_of_hasOrthonormalCols hV]
    exact specNorm_le_one_of_orthonormal hU
  · rw [frobInner_comm, frobInner_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.trace_mul_cycle Uᵀ A V]
    simpa only [nuclearNorm, Fintype.card_fin] using htrace

/-- Nuclear–spectral norm duality as an attained greatest value over every
spectral contraction. Horn–Johnson (1991), Corollary 3.4.4.
atlas: ky-fan-norms-def (partial) -/
theorem isGreatest_nuclearNorm_frobInner_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    IsGreatest {z : ℝ | ∃ B : Matrix (Fin m) (Fin n) ℝ, specNorm B ≤ 1 ∧ frobInner A B = z}
      (nuclearNorm A) := by
  refine ⟨exists_specNorm_le_one_frobInner_eq_nuclearNorm_fin A, ?_⟩
  rintro z ⟨B, hB, rfl⟩
  exact frobInner_le_nuclearNorm_of_specNorm_le_one_fin A B hB

end NLAlib
