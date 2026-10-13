import NLAlib.Matrix.Inequalities.KyFanNorms
import Mathlib.Algebra.Order.Chebyshev

/-!
# Nuclear norm: duality, sharp rank comparisons and norm axioms

The spectral-contraction maximum is attained by the top singular frames. Exact rank
support gives the comparison constants, including rank zero. Everything is stated on
arbitrary finite index types (`Fin` statements are private proof steps), with the norm
axioms, orthogonal invariance and attained nuclear–spectral duality, and the bundled
`nuclearSeminorm`.
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

/-- `Fin` step of `nuclearNorm_le_rank_mul_specNorm`. -/
private theorem nuclearNorm_le_rank_mul_specNorm_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A ≤ (A.rank : ℝ) * specNorm A := by
  rw [nuclearNorm_eq_sum_rank_singularValues]
  calc
    (∑ i ∈ Finset.range A.rank, singularValues A i) ≤ ∑ _i ∈ Finset.range A.rank, specNorm A :=
      Finset.sum_le_sum fun i _ => singularValues_le_specNorm A i
    _ = (A.rank : ℝ) * specNorm A := by simp

/-- `Fin` step of `frobNorm_le_nuclearNorm`. -/
private theorem frobNorm_le_nuclearNorm_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobNorm A ≤ nuclearNorm A := by
  have hf : frobNorm A ^ 2 = ∑ i ∈ Finset.range A.rank, singularValues A i ^ 2 := by
    rw [frobNorm_sq, frobSq_eq_sum_rank_singularValues_sq]
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.range A.rank) (fun i _ => singularValues_nonneg A i)
  rw [← hf, ← nuclearNorm_eq_sum_rank_singularValues A] at hs
  nlinarith [frobNorm_nonneg A, nuclearNorm_nonneg A]

/-- `Fin` step of `nuclearNorm_le_sqrt_rank_mul_frobNorm`. -/
private theorem nuclearNorm_le_sqrt_rank_mul_frobNorm_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
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

/-- `Fin` step of `frobInner_le_nuclearNorm_of_specNorm_le_one`. -/
private theorem frobInner_le_nuclearNorm_of_specNorm_le_one_fin {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (hB : specNorm B ≤ 1) :
    frobInner A B ≤ nuclearNorm A := by
  exact frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one A B
    (by simpa using le_min B.rank_le_height B.rank_le_width) hB

/-- Relabeling rows and columns preserves the nuclear norm. -/
theorem nuclearNorm_reindex {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    nuclearNorm (A.reindex em en) = nuclearNorm A := by
  simp only [nuclearNorm, kyFanNorm_reindex, ← Fintype.card_congr em, ← Fintype.card_congr en]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The Frobenius norm is at most the nuclear norm on every finite matrix space,
including rank zero. -/
theorem frobNorm_le_nuclearNorm (A : Matrix m n ℝ) : frobNorm A ≤ nuclearNorm A := by
  have h := frobNorm_le_nuclearNorm_fin (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  rwa [frobNorm_reindex, nuclearNorm_reindex] at h

/-- The spectral norm is at most the nuclear norm, including empty matrix spaces. -/
theorem specNorm_le_nuclearNorm (A : Matrix m n ℝ) : specNorm A ≤ nuclearNorm A :=
  (specNorm_le_frobNorm A).trans (frobNorm_le_nuclearNorm A)

/-- A rank-`r` matrix has nuclear norm at most `r` times its spectral norm, on arbitrary
finite matrix indices. The coefficient is the actual rank, with no positivity assumption. -/
theorem nuclearNorm_le_rank_mul_specNorm (A : Matrix m n ℝ) :
    nuclearNorm A ≤ (A.rank : ℝ) * specNorm A := by
  have h := nuclearNorm_le_rank_mul_specNorm_fin (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  rwa [nuclearNorm_reindex, Matrix.rank_reindex, specNorm_reindex] at h

omit [DecidableEq m] in
/-- The nuclear norm is bounded by the square root of the actual rank times the
Frobenius norm, on arbitrary finite indices; the zero matrix is covered with constant zero. -/
theorem nuclearNorm_le_sqrt_rank_mul_frobNorm (A : Matrix m n ℝ) :
    nuclearNorm A ≤ Real.sqrt A.rank * frobNorm A := by
  have h := nuclearNorm_le_sqrt_rank_mul_frobNorm_fin
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  rwa [nuclearNorm_reindex, Matrix.rank_reindex, frobNorm_reindex] at h

omit [DecidableEq m] in
/-- The nuclear norm is subadditive. -/
theorem nuclearNorm_add_le (A B : Matrix m n ℝ) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := kyFanNorm_add_le A B _

omit [DecidableEq m] in
/-- The nuclear norm is absolutely homogeneous. -/
theorem nuclearNorm_smul (A : Matrix m n ℝ) (c : ℝ) : nuclearNorm (c • A) = |c| * nuclearNorm A :=
  kyFanNorm_smul A c _

/-- The nuclear norm is a genuine norm, including the unique norm on an empty
matrix space. -/
theorem nuclearNorm_eq_zero_iff (A : Matrix m n ℝ) : nuclearNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hn : specNorm A = 0 := le_antisymm (by simpa [h] using specNorm_le_nuclearNorm A)
      (specNorm_nonneg A)
    exact norm_eq_zero.mp (by simpa only [specNorm_eq_norm] using hn)
  · rintro rfl
    exact kyFanNorm_zero_matrix _

/-- Orthogonal multiplication on the left preserves the nuclear norm. -/
theorem nuclearNorm_orthogonal_mul (A : Matrix m n ℝ) {U : Matrix m m ℝ}
    (hU : HasOrthonormalCols U) : nuclearNorm (U * A) = nuclearNorm A := kyFanNorm_orthogonal_mul A hU _

omit [DecidableEq m] in
/-- Orthogonal multiplication on the right preserves the nuclear norm. -/
theorem nuclearNorm_mul_orthogonal (A : Matrix m n ℝ) {V : Matrix n n ℝ}
    (hV : HasOrthonormalCols V) : nuclearNorm (A * V) = nuclearNorm A := kyFanNorm_mul_orthogonal A hV _

/-- Transposition preserves the nuclear norm. -/
theorem nuclearNorm_transpose (A : Matrix m n ℝ) : nuclearNorm Aᵀ = nuclearNorm A := by
  rw [nuclearNorm, nuclearNorm, kyFanNorm_transpose, min_comm]

/-- Every spectral contraction has Frobenius pairing at most the nuclear norm, on
arbitrary finite matrix indices, with no rank or nonempty dimension assumption. -/
theorem frobInner_le_nuclearNorm_of_specNorm_le_one (A B : Matrix m n ℝ) (hB : specNorm B ≤ 1) :
    frobInner A B ≤ nuclearNorm A := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  have hBn : specNorm (B.reindex em en) ≤ 1 := by rwa [specNorm_reindex]
  have h := frobInner_le_nuclearNorm_of_specNorm_le_one_fin (A.reindex em en) (B.reindex em en) hBn
  rwa [frobInner_reindex, nuclearNorm_reindex] at h

/-- An actual spectral contraction attains nuclear–spectral duality on arbitrary
finite index types, including empty shapes: the partial isometry `U Vᵀ` built from the
top singular frames. Horn–Johnson (1991), Corollary 3.4.4. -/
theorem exists_specNorm_le_one_frobInner_eq_nuclearNorm (A : Matrix m n ℝ) :
    ∃ B : Matrix m n ℝ, specNorm B ≤ 1 ∧ frobInner A B = nuclearNorm A := by
  obtain ⟨U, V, hU, hV, htrace⟩ := exists_trace_twoSided_compression_eq_kyFanNorm A le_rfl
  refine ⟨U * Vᵀ, ?_, ?_⟩
  · rw [specNorm_mul_transpose_right_of_hasOrthonormalCols hV.transpose_mul_self]
    exact specNorm_le_one_of_orthonormal hU
  · rw [frobInner_comm, frobInner_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.trace_mul_cycle Uᵀ A V]
    simpa only [nuclearNorm] using htrace

/-- Nuclear–spectral duality with an actual attained greatest value over all
spectral contractions. Horn–Johnson (1991), Corollary 3.4.4.
atlas: ky-fan-norms-def (partial) -/
theorem isGreatest_nuclearNorm_frobInner (A : Matrix m n ℝ) :
    IsGreatest {z : ℝ | ∃ B : Matrix m n ℝ, specNorm B ≤ 1 ∧ frobInner A B = z} (nuclearNorm A) := by
  refine ⟨exists_specNorm_le_one_frobInner_eq_nuclearNorm A, ?_⟩
  rintro z ⟨B, hB, rfl⟩
  exact frobInner_le_nuclearNorm_of_specNorm_le_one A B hB

/-- The bundled nuclear seminorm, with the separating zero criterion proved
above for every finite matrix shape. -/
def nuclearSeminorm : Seminorm ℝ (Matrix m n ℝ) :=
  kyFanSeminorm (min (Fintype.card m) (Fintype.card n))

omit [DecidableEq m] in
/-- The bundled nuclear seminorm agrees with the singular-value sum. -/
@[simp] theorem nuclearSeminorm_apply (A : Matrix m n ℝ) : nuclearSeminorm A = nuclearNorm A := rfl

end NLAlib
