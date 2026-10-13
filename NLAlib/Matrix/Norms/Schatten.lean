import NLAlib.Matrix.Inequalities.KyFanNorms

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
    singularValues A i ^ p) ^ (1 / p)

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
    Real.rpow_nonneg (singularValues_nonneg _ i) p) _

/-- Relabeling matrix rows and columns preserves every Schatten power sum. -/
theorem schattenNorm_reindex {m n r s : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s]
    [DecidableEq n] [DecidableEq s] (A : Matrix m n ℝ) (em : m ≃ r) (en : n ≃ s) (p : ℝ) :
    schattenNorm (A.reindex em en) p = schattenNorm A p := by
  simp only [schattenNorm, singularValues_reindex,
    ← Fintype.card_congr em, ← Fintype.card_congr en]

/-- The Schatten-1 norm is precisely the nuclear norm, at every matrix shape. -/
@[simp] theorem schattenNorm_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : schattenNorm A 1 = nuclearNorm A := by
  simp [schattenNorm, nuclearNorm, kyFanNorm, singularValues_eq_linearMap]

/-- `Fin` step of `schattenNorm_two`. -/
private theorem schattenNorm_two_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    schattenNorm A 2 = frobNorm A := by
  simp only [schattenNorm, Real.rpow_two, one_div]
  change (∑ i ∈ Finset.range (min (Fintype.card (Fin m)) (Fintype.card (Fin n))),
    singularValues A i ^ 2) ^ ((2 : ℝ)⁻¹) = _
  rw [← frobSq_eq_sum_sq_singularValues, ← one_div (2 : ℝ), ← Real.sqrt_eq_rpow]
  rfl

/-- The Schatten-2 norm is precisely the Frobenius norm, on arbitrary finite matrix
index types. -/
theorem schattenNorm_two {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : schattenNorm A 2 = frobNorm A := by
  rw [← schattenNorm_reindex A (Fintype.equivFin m) (Fintype.equivFin n),
    schattenNorm_two_fin, frobNorm_reindex]

section FiniteIndex

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Orthogonal left multiplication preserves every finite Schatten power sum. -/
theorem schattenNorm_orthogonal_mul (A : Matrix m n ℝ) {U : Matrix m m ℝ}
    (hU : HasOrthonormalCols U) (p : ℝ) : schattenNorm (U * A) p = schattenNorm A p := by
  simp only [schattenNorm, singularValues_isometry_mul hU A]

omit [DecidableEq m] in
/-- Orthogonal right multiplication preserves every finite Schatten power sum. -/
theorem schattenNorm_mul_orthogonal (A : Matrix m n ℝ) {V : Matrix n n ℝ}
    (hV : HasOrthonormalCols V) (p : ℝ) : schattenNorm (A * V) p = schattenNorm A p := by
  simp only [schattenNorm, singularValues_mul_orthogonal A hV]

/-- Transposition preserves every finite Schatten power sum. -/
theorem schattenNorm_transpose (A : Matrix m n ℝ) (p : ℝ) : schattenNorm Aᵀ p = schattenNorm A p := by
  simp only [schattenNorm, singularValues_transpose, min_comm]

end FiniteIndex

end NLAlib
