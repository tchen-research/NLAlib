import NLAlib.Matrix.KyFanFiniteIndex
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.ENNReal.Holder

/-!
# Schatten norm definitions and scalar exponents

Finite real exponents use their usual singular-value power sum. The extended
exponent definition includes infinity explicitly as the spectral norm.
Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.3–3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators ENNReal

namespace NLAlib

/-- The Schatten power sum norm at a finite real exponent. Norm results assume
`1 ≤ p`; the formula is retained for positive-exponent product comparisons.
Bhatia (1997), §IV.2.
atlas: schatten-norms-def (partial) -/
def schattenNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (p : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
    A.toEuclideanLin.singularValues i ^ p) ^ (1 / p)

/-- The Schatten norm at an extended exponent, with infinity defined exactly
as the spectral norm. Norm theorems use `1 ≤ p`.
atlas: schatten-norms-def (partial) -/
def schattenNormExtended {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (p : ℝ≥0∞) : ℝ :=
  if p = ∞ then specNorm A else schattenNorm A p.toReal

/-- At exponent infinity, the Schatten norm is the spectral norm. -/
@[simp] theorem schattenNormExtended_top {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : schattenNormExtended A ∞ = specNorm A := by
  simp [schattenNormExtended]

/-- At every finite extended exponent, the formula is its finite real power sum. -/
theorem schattenNormExtended_eq_of_ne_top {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    schattenNormExtended A p = schattenNorm A p.toReal := by
  simp [schattenNormExtended, hp]

/-- Schatten power sum norms are nonnegative. -/
theorem schattenNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (p : ℝ) : 0 ≤ schattenNorm A p :=
  Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (LinearMap.singularValues_nonneg _ i) p) _

/-- Relabeling matrix rows and columns preserves every Schatten power sum. -/
theorem schattenNorm_reindex {m n r s : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s]
    [DecidableEq n] [DecidableEq s] (A : Matrix m n ℝ) (em : m ≃ r) (en : n ≃ s) (p : ℝ) :
    schattenNorm (A.reindex em en) p = schattenNorm A p := by
  simp only [schattenNorm, toEuclideanLin_singularValues_reindex,
    ← Fintype.card_congr em, ← Fintype.card_congr en]

/-- The Schatten-1 norm is precisely the nuclear norm, at every matrix shape. -/
@[simp] theorem schattenNorm_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : schattenNorm A 1 = nuclearNorm A := by
  simp [schattenNorm, nuclearNorm, kyFanNorm]

/-- The Schatten-2 norm is precisely the Frobenius norm. -/
theorem schattenNorm_two_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    schattenNorm A 2 = frobNorm A := by
  simp only [schattenNorm, Fintype.card_fin, Real.rpow_two, one_div]
  change (∑ i ∈ Finset.range (min m n), singularValues A i ^ 2) ^ ((2 : ℝ)⁻¹) = _
  rw [← frobSq_eq_sum_sq_singularValues, ← one_div (2 : ℝ), ← Real.sqrt_eq_rpow]
  rfl

/-- The Schatten-2 identity holds on arbitrary finite matrix index types. -/
theorem schattenNorm_two {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : schattenNorm A 2 = frobNorm A := by
  rw [← schattenNorm_reindex A (Fintype.equivFin m) (Fintype.equivFin n),
    schattenNorm_two_fin, frobNorm_reindex]

/-- Left orthogonal multiplication preserves the finite Schatten power sum. -/
theorem schattenNorm_orthogonal_mul_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : HasOrthonormalCols U) (p : ℝ) :
    schattenNorm (U * A) p = schattenNorm A p := by
  simp only [schattenNorm, Fintype.card_fin]
  change (∑ i ∈ Finset.range (min m n), singularValues (U * A) i ^ p) ^ (1 / p) = _
  rw [singularValues_orthogonal_mul A hU]
  rfl

/-- Right orthogonal multiplication preserves the finite Schatten power sum. -/
theorem schattenNorm_mul_orthogonal_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : HasOrthonormalCols V) (p : ℝ) :
    schattenNorm (A * V) p = schattenNorm A p := by
  simp only [schattenNorm, Fintype.card_fin]
  change (∑ i ∈ Finset.range (min m n), singularValues (A * V) i ^ p) ^ (1 / p) = _
  rw [singularValues_mul_orthogonal A hV]
  rfl

/-- Transposition preserves the finite Schatten power sum. -/
theorem schattenNorm_transpose_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p : ℝ) :
    schattenNorm Aᵀ p = schattenNorm A p := by
  simp only [schattenNorm, Fintype.card_fin]
  change (∑ i ∈ Finset.range (min n m), singularValues Aᵀ i ^ p) ^ (1 / p) = _
  rw [singularValues_transpose, min_comm]
  rfl

end NLAlib
