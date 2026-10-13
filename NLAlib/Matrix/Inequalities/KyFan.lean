import NLAlib.Matrix.Inequalities.TraceTail
import NLAlib.Matrix.Inequalities.VonNeumann
import NLAlib.Matrix.Inequalities.MajorizationProperties
import NLAlib.Matrix.Norms.KyFanNorm
import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!
# Ky Fan variational trace bounds

The maximum principle for eigenvalue and singular-value sums, including the empty prefix.
`eigenvaluePrefix hA k = sumLargest hA.eigenvalues₀ k` is the sum of the `k` largest eigenvalues
of a Hermitian matrix; eigenvalue bounds use compression interlacing, singular-value bounds use
the von Neumann trace inequality.
Source: Fan (1949), Theorem 1; Horn–Johnson (2013), Corollary 4.3.39.
Atlas: `ky-fan-maximum-principle`, `ky-fan-norms-def`. The definitions of `kyFanNorm` and
`nuclearNorm` are in `NLAlib.Matrix.Norms.KyFanNorm`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **sum of the `k` largest eigenvalues** of a Hermitian matrix: `sumLargest` of the sorted
spectrum `hA.eigenvalues₀` (`0` for `k = 0`, the trace for `k ≥ card n`). Fan 1949;
Horn–Johnson 2013, Cor. 4.3.39. -/
def eigenvaluePrefix {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  sumLargest hA.eigenvalues₀ k

/-- For `k ≤ card n`, `eigenvaluePrefix hA k = ∑_{i < k} λ_i` along the sorted spectrum. -/
theorem eigenvaluePrefix_eq_sum_castLE {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) :
    eigenvaluePrefix hA k = ∑ i : Fin k, hA.eigenvalues₀ (Fin.castLE hk i) := by
  rw [eigenvaluePrefix, sumLargest_eq_prefix_of_antitone _ hA.eigenvalues₀_antitone,
    sum_fin_ite_lt_eq_sum_castLE hk]

/-- Beyond the dimension the prefix is the whole trace. -/
theorem eigenvaluePrefix_of_card_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : Fintype.card n ≤ k) : eigenvaluePrefix hA k = RCLike.re A.trace := by
  rw [eigenvaluePrefix, sumLargest_eq_sum_of_card_le _ (by simpa using hk),
    hA.trace_eq_sum_eigenvalues, map_sum]
  simp only [RCLike.ofReal_re]
  exact (sum_eigenvalues_eq_sum_sorted hA id).symm

@[simp] theorem eigenvaluePrefix_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    eigenvaluePrefix hA 0 = 0 := by
  simp [eigenvaluePrefix]

/-- **Ky Fan maximum principle, upper bound.** Every orthonormal compression trace
`Re tr(Qᴴ A Q)` is at most the sum of the `card r` largest eigenvalues, including zero columns.
Fan (1949), Theorem 1; Horn–Johnson 2013, Cor. 4.3.39.
atlas: ky-fan-maximum-principle -/
theorem trace_compression_le_eigenvaluePrefix {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) :
    RCLike.re (Qᴴ * A * Q).trace ≤ eigenvaluePrefix hA (Fintype.card r) := by
  let hB : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  rw [eigenvaluePrefix_eq_sum_castLE hA (card_le_card_of_hasOrthonormalCols hQ),
    hB.trace_eq_sum_eigenvalues, map_sum]
  simp only [RCLike.ofReal_re]
  change (∑ i, id (hB.eigenvalues i)) ≤ _
  rw [sum_eigenvalues_eq_sum_sorted hB id]
  exact Finset.sum_le_sum fun i _ => Matrix.IsHermitian.eigenvalues₀_compression_le hA hQ i

/-- **Ky Fan minimum principle.** The sum of the `card r` smallest eigenvalues is at most every
orthonormal compression trace `Re tr(Qᴴ A Q)`, including zero columns. Fan (1949).
atlas: ky-fan-maximum-principle -/
theorem sum_bottom_eigenvalues_le_trace_compression {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) :
    (∑ i : Fin (Fintype.card r), hA.eigenvalues₀
      ⟨i.val + (Fintype.card n - Fintype.card r), by
        have := card_le_card_of_hasOrthonormalCols hQ; omega⟩) ≤ RCLike.re (Qᴴ * A * Q).trace := by
  let hB : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  rw [hB.trace_eq_sum_eigenvalues, map_sum]
  simp only [RCLike.ofReal_re]
  change _ ≤ ∑ i, id (hB.eigenvalues i)
  rw [sum_eigenvalues_eq_sum_sorted hB id]
  exact Finset.sum_le_sum fun i _ => Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_compression hA hQ i

/-- A spectral contraction of rank at most `k` pairs with a matrix at most its Ky Fan `k`
sum. Von Neumann's trace inequality and the singular-value rank support; helper for Fan
(1949), Theorem 1. -/
theorem frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] {k : ℕ}
    (A P : Matrix m n ℝ) (hP : P.rank ≤ k) (hPn : specNorm P ≤ 1) :
    frobInner A P ≤ kyFanNorm A k := by
  calc
    frobInner A P ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i * singularValues P i :=
      frobInner_le_sum_singularValues_mul A P
    _ ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        if i < k then singularValues A i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i < k
      · rw [if_pos hi]
        simpa using mul_le_mul_of_nonneg_left
          ((singularValues_le_specNorm P i).trans hPn) (singularValues_nonneg A i)
      · rw [if_neg hi, singularValues_eq_zero_of_rank_le P (by omega), mul_zero]
    _ = kyFanNorm A k := by
      rw [← Finset.sum_filter]
      rw [kyFanNorm_eq_sum_range]
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
        exact hi.2
      · intro i hi hni
        simp only [Finset.mem_filter, Finset.mem_range] at hi hni
        exact singularValues_eq_zero_of_min_le A (by omega)

/-- Relabeling matrix indices preserves every Ky Fan sum. -/
theorem kyFanNorm_reindex {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) (k : ℕ) :
    kyFanNorm (A.reindex em en) k = kyFanNorm A k := by
  simp only [kyFanNorm_eq_sum_range, singularValues_reindex]

/-- Simultaneously relabeling both frame spaces and the matrix preserves the two-sided
compression trace. -/
theorem twoSided_compression_trace_reindex {m n r p q s : Type*}
    [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q] [Fintype s]
    (A : Matrix m n ℝ) (U : Matrix m r ℝ) (V : Matrix n r ℝ)
    (em : m ≃ p) (en : n ≃ q) (er : r ≃ s) :
    ((U.reindex em er)ᵀ * A.reindex em en * V.reindex en er).trace = (Uᵀ * A * V).trace := by
  have h1 : (U.reindex em er)ᵀ * A.reindex em en = (Uᵀ * A).reindex er en := by
    simpa only [Matrix.reindex_apply, Matrix.transpose_submatrix] using
      Matrix.submatrix_mul_equiv Uᵀ A er.symm em.symm en.symm
  have h2 : (Uᵀ * A).reindex er en * V.reindex en er = (Uᵀ * A * V).reindex er er := by
    simpa only [Matrix.reindex_apply] using
      Matrix.submatrix_mul_equiv (Uᵀ * A) V er.symm en.symm er.symm
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact er.symm.sum_comp (fun i => (Uᵀ * A * V) i i)

/-- `Fin` step of `trace_twoSided_compression_le_kyFanNorm`. -/
private theorem trace_twoSided_compression_le_kyFanNorm_fin {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {U : Matrix (Fin m) (Fin k) ℝ}
    {V : Matrix (Fin n) (Fin k) ℝ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    (Uᵀ * A * V).trace ≤ kyFanNorm A k := by
  have hP : (U * Vᵀ).rank ≤ k :=
    (Matrix.rank_mul_le_left U Vᵀ).trans (by simpa using U.rank_le_width)
  have hPn : specNorm (U * Vᵀ) ≤ 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial V,
      specNorm_mul_conjTranspose_right_of_hasOrthonormalCols hV]
    exact specNorm_le_one_of_orthonormal hU
  have htrace : (Uᵀ * A * V).trace = frobInner A (U * Vᵀ) := by
    rw [frobInner_comm, frobInner_eq_trace, RCLike.re_to_real,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    exact Matrix.trace_mul_cycle Uᵀ A V
  rw [htrace]
  exact frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one A (U * Vᵀ) hP hPn


/-- Every two-sided orthonormal compression trace is at most the sum of the
corresponding top singular values, on arbitrary finite row, column and frame indices.
No dimension hypothesis beyond the orthonormal frames is needed; zero columns are
included. Fan (1949), Theorem 1; Horn–Johnson (1991), Theorem 3.4.1.
atlas: ky-fan-maximum-principle -/
theorem trace_twoSided_compression_le_kyFanNorm {m n r : Type*}
    [Fintype m] [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    (A : Matrix m n ℝ) {U : Matrix m r ℝ} {V : Matrix n r ℝ}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    (Uᵀ * A * V).trace ≤ kyFanNorm A (Fintype.card r) := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let er := Fintype.equivFin r
  have h := trace_twoSided_compression_le_kyFanNorm_fin (A.reindex em en)
    (hU.reindex em er) (hV.reindex en er)
  rwa [twoSided_compression_trace_reindex, kyFanNorm_reindex] at h

end NLAlib
