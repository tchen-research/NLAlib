import NLAlib.Matrix.Inequalities.KyFanAttainment
import NLAlib.Matrix.Spectral.SingularValueScaling
import NLAlib.Matrix.Spectral.SingularValueSpectrum
/-!
# Ky Fan norm axioms and invariances

The variational principle proves the triangle inequality. Native linear-map
singular values give coordinate-free definitions on arbitrary finite matrix
indices: the norm axioms and invariances hold over `[Fintype m] [Fintype n]`, every
positive prefix is a genuine norm, and the bundled `kyFanSeminorm` packages the axioms.
Source: Horn–Johnson (1991), Theorem 3.4.1; Bhatia (1997), §IV.2.
Atlas: `ky-fan-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- Every Ky Fan sum is nonnegative, including the zero seminorm. -/
theorem kyFanNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) :
    0 ≤ kyFanNorm A k := Finset.sum_nonneg fun i _ => singularValues_nonneg _ i

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
    simp only [Finset.mem_range, Fintype.card_fin] at hi hni ⊢
    omega)

/-- `Fin` step of `kyFanNorm_add_le`: prefixes are capped at `min m n` and the
maximum principle gives the bound at each admissible prefix. -/
private theorem kyFanNorm_add_le_fin {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    kyFanNorm (A + B) k ≤ kyFanNorm A k + kyFanNorm B k := by
  have hbound (j : ℕ) (hj : j ≤ min m n) :
      kyFanNorm (A + B) j ≤ kyFanNorm A j + kyFanNorm B j := by
    obtain ⟨U, V, hU, hV, hUV⟩ :=
      exists_trace_twoSided_compression_eq_kyFanNorm (A + B) (by simpa using hj)
    have h1 := trace_twoSided_compression_le_kyFanNorm A hU hV
    have h2 := trace_twoSided_compression_le_kyFanNorm B hU hV
    rw [Fintype.card_fin] at h1 h2
    rw [← hUV, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    exact add_le_add h1 h2
  rw [kyFanNorm_eq_min (A + B) k, kyFanNorm_eq_min A k, kyFanNorm_eq_min B k]
  exact hbound _ (min_le_right _ _)

section FiniteIndex

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- The Ky Fan sums obey the triangle inequality on arbitrary finite matrix indices,
including the zero prefix and all zero-padded prefixes.
Horn–Johnson (1991), Theorem 3.4.1.
atlas: ky-fan-norms-def (partial) -/
theorem kyFanNorm_add_le (A B : Matrix m n ℝ) (k : ℕ) :
    kyFanNorm (A + B) k ≤ kyFanNorm A k + kyFanNorm B k := by
  have h := kyFanNorm_add_le_fin (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (B.reindex (Fintype.equivFin m) (Fintype.equivFin n)) k
  change kyFanNorm ((A + B).reindex (Fintype.equivFin m) (Fintype.equivFin n)) k ≤ _ at h
  rwa [kyFanNorm_reindex, kyFanNorm_reindex, kyFanNorm_reindex] at h

omit [DecidableEq m] in
/-- Ky Fan sums are absolutely homogeneous on arbitrary finite indices.
Horn–Johnson (1991), §3.4. -/
theorem kyFanNorm_smul (A : Matrix m n ℝ) (c : ℝ) (k : ℕ) :
    kyFanNorm (c • A) k = |c| * kyFanNorm A k := by
  simp only [kyFanNorm, ← singularValues_eq_linearMap, singularValues_smul, Finset.mul_sum]

/-- Orthogonal multiplication on the left preserves Ky Fan sums. -/
theorem kyFanNorm_orthogonal_mul (A : Matrix m n ℝ) {U : Matrix m m ℝ}
    (hU : HasOrthonormalCols U) (k : ℕ) : kyFanNorm (U * A) k = kyFanNorm A k := by
  simp only [kyFanNorm, ← singularValues_eq_linearMap, singularValues_isometry_mul hU A]

omit [DecidableEq m] in
/-- Orthogonal multiplication on the right preserves Ky Fan sums. -/
theorem kyFanNorm_mul_orthogonal (A : Matrix m n ℝ) {V : Matrix n n ℝ}
    (hV : HasOrthonormalCols V) (k : ℕ) : kyFanNorm (A * V) k = kyFanNorm A k := by
  simp only [kyFanNorm, ← singularValues_eq_linearMap, singularValues_mul_orthogonal A hV]

/-- Transposition preserves Ky Fan sums on arbitrary finite indices. -/
theorem kyFanNorm_transpose (A : Matrix m n ℝ) (k : ℕ) : kyFanNorm Aᵀ k = kyFanNorm A k := by
  simp only [kyFanNorm, ← singularValues_eq_linearMap, singularValues_transpose]

/-- The bundled Ky Fan seminorm, using Mathlib's norm vocabulary. For `k ≥ 1`
the separately proved zero criterion shows that this is a genuine norm.
Horn–Johnson (1991), Theorem 3.4.1.
atlas: ky-fan-norms-def (partial) -/
def kyFanSeminorm (k : ℕ) : Seminorm ℝ (Matrix m n ℝ) :=
  Seminorm.of (fun A => kyFanNorm A k) (fun A B => kyFanNorm_add_le A B k)
    (fun c A => by simpa only [Real.norm_eq_abs] using kyFanNorm_smul A c k)

omit [DecidableEq m] in
/-- The bundled Ky Fan seminorm agrees exactly with the singular-value sum. -/
@[simp] theorem kyFanSeminorm_apply (k : ℕ) (A : Matrix m n ℝ) :
    kyFanSeminorm k A = kyFanNorm A k := rfl

end FiniteIndex

/-- The first Ky Fan sum is exactly the spectral norm, including empty indices.
Horn–Johnson (1991), §3.4.
atlas: ky-fan-norms-def (partial) -/
theorem kyFanNorm_one_eq_specNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) : kyFanNorm A 1 = specNorm A := by
  simp only [kyFanNorm, Finset.sum_range_one]
  exact singularValues_zero_eq_specNorm A

/-- Every nonzero Ky Fan prefix dominates the spectral norm. -/
theorem specNorm_le_kyFanNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) {k : ℕ} (hk : 1 ≤ k) :
    specNorm A ≤ kyFanNorm A k := by
  rw [← kyFanNorm_one_eq_specNorm A]
  simp only [kyFanNorm, Finset.sum_range_one]
  change singularValues A 0 ≤ _
  exact Finset.single_le_sum (fun i _ => singularValues_nonneg _ i)
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
