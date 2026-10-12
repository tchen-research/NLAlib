import NLAlib.Matrix.Inequalities.TraceTail
import NLAlib.Matrix.Inequalities.VonNeumann
/-!
# Ky Fan variational trace bounds

The maximum principle for real eigenvalue and singular-value sums, including
attainment and the empty prefix. Eigenvalue bounds use compression interlacing;
singular-value bounds use the already proved von Neumann trace inequality.
Source: Fan (1949), Theorem 1; Horn–Johnson (2013), Corollary 4.3.39.
Atlas: `ky-fan-maximum-principle`, `ky-fan-norms-def`.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib

/-- Selecting distinct columns of an orthonormal frame preserves orthonormality.
This is the finite frame API used by the attaining Ky Fan optimizers. -/
theorem HasOrthonormalCols.submatrix_cols {m n r : Type*} [Fintype m] [Fintype n]
    [Fintype r] [DecidableEq n] [DecidableEq r] {Q : Matrix m n ℝ}
    (hQ : HasOrthonormalCols Q) (e : r ↪ n) : HasOrthonormalCols (Q.submatrix id e) := by
  change (Q.submatrix id e)ᵀ * Q.submatrix id e = 1
  rw [Matrix.transpose_submatrix]
  have h := Matrix.submatrix_mul_equiv Qᵀ Q e (Equiv.refl m) e
  simp only [Equiv.coe_refl] at h
  rw [h, hQ]
  ext i j
  simp [Matrix.one_apply, e.injective.eq_iff]

/-- The sum of a specified number of the largest sorted eigenvalues. The
cardinality proof supplies the actual eigenvalue indices. -/
def eigenvaluePrefix {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {k : ℕ} (hk : k ≤ Fintype.card n) : ℝ :=
  ∑ i : Fin k, hA.eigenvalues₀ (Fin.castLE hk i)

/-- Every orthonormal compression trace is bounded by the corresponding top
eigenvalue sum, including zero columns. Fan (1949), Theorem 1.
atlas: ky-fan-maximum-principle (partial) -/
theorem trace_compression_le_eigenvaluePrefix {n r : Type*} [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) :
    (Qᵀ * A * Q).trace ≤ eigenvaluePrefix hA (card_le_card_of_hasOrthonormalCols hQ) := by
  let hB := isHermitian_transpose_mul_mul hA Q
  rw [hB.trace_eq_sum_eigenvalues]
  change (∑ i, id (hB.eigenvalues i)) ≤ _
  rw [sum_eigenvalues_eq_sum_sorted hB id]
  exact Finset.sum_le_sum fun i _ => eigenvalues₀_compression_le hA hQ hB i

/-- The bottom eigenvalue sum bounds every orthonormal compression trace from
below, including zero columns. Fan (1949), the minimum principle.
atlas: ky-fan-maximum-principle (partial) -/
theorem sum_bottom_eigenvalues_le_trace_compression {n r : Type*} [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) :
    (∑ i : Fin (Fintype.card r), hA.eigenvalues₀
      ⟨i.val + (Fintype.card n - Fintype.card r), by
        have := card_le_card_of_hasOrthonormalCols hQ; omega⟩) ≤ (Qᵀ * A * Q).trace := by
  let hB := isHermitian_transpose_mul_mul hA Q
  rw [hB.trace_eq_sum_eigenvalues]
  change _ ≤ ∑ i, id (hB.eigenvalues i)
  rw [sum_eigenvalues_eq_sum_sorted hB id]
  exact Finset.sum_le_sum fun i _ => eigenvalues₀_le_eigenvalues₀_compression hA hQ hB i

/-- The Ky Fan `k` sum, with the existing zero-padded singular-value convention.
For positive `k` up to the smaller matrix dimension it is a norm; at zero it is
the zero seminorm. Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def (partial) -/
def kyFanNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, A.toEuclideanLin.singularValues i

/-- The nuclear norm is the sum of all singular values, including matrices with
an empty dimension. Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def (partial) -/
def nuclearNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : ℝ :=
  kyFanNorm A (min (Fintype.card m) (Fintype.card n))

/-- A spectral contraction of rank at most `k` pairs with a matrix at most its
Ky Fan `k` sum. Source: von Neumann trace inequality and the singular-value rank
support; helper for Fan (1949), Theorem 1. -/
theorem frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one {m n k : ℕ}
    (A P : Matrix (Fin m) (Fin n) ℝ) (hP : P.rank ≤ k) (hPn : specNorm P ≤ 1) :
    frobInner A P ≤ kyFanNorm A k := by
  calc
    frobInner A P ≤ ∑ i ∈ Finset.range (min m n), singularValues A i * singularValues P i :=
      frobInner_le_sum_singularValues_mul A P
    _ ≤ ∑ i ∈ Finset.range (min m n), if i < k then singularValues A i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i < k
      · rw [if_pos hi]
        simpa using mul_le_mul_of_nonneg_left
          ((singularValues_le_specNorm P i).trans hPn) (singularValues_nonneg A i)
      · rw [if_neg hi, singularValues_eq_zero_of_rank_le P (by omega), mul_zero]
    _ = kyFanNorm A k := by
      rw [← Finset.sum_filter]
      unfold kyFanNorm
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
        exact hi.2
      · intro i hi hni
        simp only [Finset.mem_filter, Finset.mem_range] at hi hni
        exact singularValues_eq_zero_of_min_le A (by omega)

/-- Every two-sided orthonormal compression trace is at most the sum of the
corresponding top singular values. The rank/norm proof includes zero columns.
Fan (1949), Theorem 1; Horn–Johnson (1991), Theorem 3.4.1.
atlas: ky-fan-maximum-principle (partial) -/
theorem trace_twoSided_compression_le_kyFanNorm {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {U : Matrix (Fin m) (Fin k) ℝ}
    {V : Matrix (Fin n) (Fin k) ℝ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    (Uᵀ * A * V).trace ≤ kyFanNorm A k := by
  have hP : (U * Vᵀ).rank ≤ k :=
    (Matrix.rank_mul_le_left U Vᵀ).trans (by simpa using U.rank_le_width)
  have hPn : specNorm (U * Vᵀ) ≤ 1 := by
    rw [specNorm_mul_transpose_right_of_hasOrthonormalCols hV]
    exact specNorm_le_one_of_orthonormal hU
  have htrace : (Uᵀ * A * V).trace = frobInner A (U * Vᵀ) := by
    rw [frobInner_comm, frobInner_eq_trace, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    exact Matrix.trace_mul_cycle Uᵀ A V
  rw [htrace]
  exact frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one A (U * Vᵀ) hP hPn

end NLAlib
