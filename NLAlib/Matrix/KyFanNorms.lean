import NLAlib.Matrix.KyFanAttainment
import NLAlib.Matrix.SingularValueScaling
import NLAlib.Matrix.SingularValueSpectrum

/-!
# Ky Fan norm axioms and invariances

The variational principle proves the triangle inequality. Native linear-map
singular values give coordinate-free definitions on arbitrary finite matrix
indices. Source: Horn–Johnson (1991), Theorem 3.4.1; Bhatia (1997), §IV.2.
Atlas: `ky-fan-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- Relabeling matrix indices preserves every Ky Fan sum. -/
theorem kyFanNorm_reindex {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) (k : ℕ) :
    kyFanNorm (A.reindex em en) k = kyFanNorm A k := by
  simp only [kyFanNorm, toEuclideanLin_singularValues_reindex]

/-- Every Ky Fan sum is nonnegative, including the zero seminorm. -/
theorem kyFanNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) :
    0 ≤ kyFanNorm A k := Finset.sum_nonneg fun i _ => LinearMap.singularValues_nonneg _ i

/-- The zero prefix is zero. -/
@[simp] theorem kyFanNorm_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) :
    kyFanNorm A 0 = 0 := by simp [kyFanNorm]

/-- Every Ky Fan sum vanishes on the zero matrix. -/
@[simp] theorem kyFanNorm_zero_matrix {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (k : ℕ) :
    kyFanNorm (0 : Matrix m n ℝ) k = 0 := by simp [kyFanNorm]

/-- Prefixes beyond the smaller matrix dimension are the nuclear norm. -/
theorem kyFanNorm_eq_min {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    kyFanNorm A k = kyFanNorm A (min k (min m n)) := by
  change (∑ i ∈ Finset.range k, singularValues A i) =
    ∑ i ∈ Finset.range (min k (min m n)), singularValues A i
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (min_le_left _ _))
  intro i hi hni
  exact singularValues_eq_zero_of_min_le A (by
    simp only [Finset.mem_range] at hi hni
    omega)

/-- The Ky Fan sums obey the triangle inequality, including the zero prefix
and all zero-padded prefixes. Horn–Johnson (1991), Theorem 3.4.1.
atlas: ky-fan-norms-def (partial) -/
theorem kyFanNorm_add_le_fin {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    kyFanNorm (A + B) k ≤ kyFanNorm A k + kyFanNorm B k := by
  have hbound (j : ℕ) (hj : j ≤ min m n) :
      kyFanNorm (A + B) j ≤ kyFanNorm A j + kyFanNorm B j := by
    obtain ⟨U, V, hU, hV, hUV⟩ := exists_trace_twoSided_compression_eq_kyFanNorm (A + B) hj
    rw [← hUV, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    exact add_le_add (trace_twoSided_compression_le_kyFanNorm A hU hV)
      (trace_twoSided_compression_le_kyFanNorm B hU hV)
  rw [kyFanNorm_eq_min (A + B) k, kyFanNorm_eq_min A k, kyFanNorm_eq_min B k]
  exact hbound _ (min_le_right _ _)

/-- Ky Fan sums are absolutely homogeneous. Horn–Johnson (1991), §3.4. -/
theorem kyFanNorm_smul_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) (k : ℕ) :
    kyFanNorm (c • A) k = |c| * kyFanNorm A k := by
  change (∑ i ∈ Finset.range k, singularValues (c • A) i) =
    |c| * ∑ i ∈ Finset.range k, singularValues A i
  simp only [singularValues_smul, Finset.mul_sum]

/-- Left orthogonal multiplication preserves every Ky Fan sum. -/
theorem kyFanNorm_orthogonal_mul_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : HasOrthonormalCols U) (k : ℕ) :
    kyFanNorm (U * A) k = kyFanNorm A k := by
  change (∑ i ∈ Finset.range k, singularValues (U * A) i) =
    ∑ i ∈ Finset.range k, singularValues A i
  rw [singularValues_orthogonal_mul A hU]

/-- Right orthogonal multiplication preserves every Ky Fan sum. -/
theorem kyFanNorm_mul_orthogonal_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : HasOrthonormalCols V) (k : ℕ) :
    kyFanNorm (A * V) k = kyFanNorm A k := by
  change (∑ i ∈ Finset.range k, singularValues (A * V) i) =
    ∑ i ∈ Finset.range k, singularValues A i
  rw [singularValues_mul_orthogonal A hV]

/-- Transposition preserves every Ky Fan sum. -/
theorem kyFanNorm_transpose_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    kyFanNorm Aᵀ k = kyFanNorm A k := by
  change (∑ i ∈ Finset.range k, singularValues Aᵀ i) =
    ∑ i ∈ Finset.range k, singularValues A i
  rw [singularValues_transpose]

/-- The first Ky Fan sum is exactly the spectral norm, including empty indices.
Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def (partial) -/
theorem kyFanNorm_one_eq_specNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) : kyFanNorm A 1 = specNorm A := by
  rw [← kyFanNorm_reindex A (Fintype.equivFin m) (Fintype.equivFin n)]
  simp only [kyFanNorm, Finset.sum_range_one]
  change singularValues (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) 0 = _
  exact singularValues_reindex_zero_eq_specNorm A

/-- Every nonzero Ky Fan prefix dominates the spectral norm. -/
theorem specNorm_le_kyFanNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) {k : ℕ} (hk : 1 ≤ k) :
    specNorm A ≤ kyFanNorm A k := by
  rw [← kyFanNorm_one_eq_specNorm A]
  simp only [kyFanNorm, Finset.sum_range_one]
  change A.toEuclideanLin.singularValues 0 ≤ _
  exact Finset.single_le_sum (fun i _ => LinearMap.singularValues_nonneg _ i)
    (Finset.mem_range.mpr (by omega))

/-- A positive Ky Fan prefix vanishes exactly on the zero matrix. -/
theorem kyFanNorm_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) {k : ℕ} (hk : 1 ≤ k) :
    kyFanNorm A k = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hn : specNorm A = 0 := le_antisymm (by simpa [h] using specNorm_le_kyFanNorm A hk)
      (specNorm_nonneg A)
    exact norm_eq_zero.mp (by simpa only [specNorm_eq_norm] using hn)
  · rintro rfl
    exact kyFanNorm_zero_matrix k

end NLAlib
