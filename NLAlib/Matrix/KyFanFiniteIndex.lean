import NLAlib.Matrix.KyFanNorms
import Mathlib.Analysis.Seminorm

/-!
# Ky Fan norms on arbitrary finite matrix indices

Finite-coordinate transport preserves the native singular-value definition.
Every positive prefix is a genuine norm; zero is the zero seminorm.
Source: Horn–Johnson (1991), Theorem 3.4.1; Bhatia (1997), §IV.2.
Atlas: `ky-fan-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- Ky Fan triangle inequality on arbitrary finite matrix indices. -/
theorem kyFanNorm_add_le (A B : Matrix m n ℝ) (k : ℕ) :
    kyFanNorm (A + B) k ≤ kyFanNorm A k + kyFanNorm B k := by
  have h := kyFanNorm_add_le_fin (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (B.reindex (Fintype.equivFin m) (Fintype.equivFin n)) k
  change kyFanNorm ((A + B).reindex (Fintype.equivFin m) (Fintype.equivFin n)) k ≤ _ at h
  rwa [kyFanNorm_reindex, kyFanNorm_reindex, kyFanNorm_reindex] at h

omit [DecidableEq m] in
/-- Absolute homogeneity of Ky Fan sums on arbitrary finite indices. -/
theorem kyFanNorm_smul (A : Matrix m n ℝ) (c : ℝ) (k : ℕ) :
    kyFanNorm (c • A) k = |c| * kyFanNorm A k := by
  have h := kyFanNorm_smul_fin (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) c k
  change kyFanNorm ((c • A).reindex (Fintype.equivFin m) (Fintype.equivFin n)) k = _ at h
  rwa [kyFanNorm_reindex, kyFanNorm_reindex] at h

/-- Orthogonal multiplication on the left preserves Ky Fan sums. -/
theorem kyFanNorm_orthogonal_mul (A : Matrix m n ℝ) {U : Matrix m m ℝ}
    (hU : HasOrthonormalCols U) (k : ℕ) : kyFanNorm (U * A) k = kyFanNorm A k := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  have h := kyFanNorm_orthogonal_mul_fin (A.reindex em en) (hU.reindex em em) k
  have hmul : U.reindex em em * A.reindex em en = (U * A).reindex em en := by
    simpa only [Matrix.reindex_apply] using Matrix.submatrix_mul_equiv U A em.symm em.symm en.symm
  rw [hmul, kyFanNorm_reindex, kyFanNorm_reindex] at h
  exact h

omit [DecidableEq m] in
/-- Orthogonal multiplication on the right preserves Ky Fan sums. -/
theorem kyFanNorm_mul_orthogonal (A : Matrix m n ℝ) {V : Matrix n n ℝ}
    (hV : HasOrthonormalCols V) (k : ℕ) : kyFanNorm (A * V) k = kyFanNorm A k := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  have h := kyFanNorm_mul_orthogonal_fin (A.reindex em en) (hV.reindex en en) k
  have hmul : A.reindex em en * V.reindex en en = (A * V).reindex em en := by
    simpa only [Matrix.reindex_apply] using Matrix.submatrix_mul_equiv A V em.symm en.symm en.symm
  rw [hmul, kyFanNorm_reindex, kyFanNorm_reindex] at h
  exact h

/-- Transposition preserves Ky Fan sums on arbitrary finite indices. -/
theorem kyFanNorm_transpose (A : Matrix m n ℝ) (k : ℕ) : kyFanNorm Aᵀ k = kyFanNorm A k := by
  have h := kyFanNorm_transpose_fin (A.reindex (Fintype.equivFin m) (Fintype.equivFin n)) k
  rw [Matrix.transpose_reindex, kyFanNorm_reindex, kyFanNorm_reindex] at h
  exact h

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

end NLAlib
