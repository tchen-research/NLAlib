import NLAlib.Matrix.Norms.KyFanNorm
import NLAlib.Matrix.Spectral.SingularValueInvariance

/-!
# Schatten norm definitions and scalar exponents

Over `ℝ` or `ℂ` (any `[RCLike 𝕜]`), finite real exponents use their usual singular-value power
sum. The extended exponent definition includes infinity explicitly as the spectral norm. Both are
real-valued and, at `𝕜 := ℝ`, are the real definitions verbatim.

The main scalar interface is `schattenNorm A (p : ℝ≥0∞)`. The finite real formula is
`schattenNormReal A (p : ℝ)`, connected by `schattenNorm_eq_of_ne_top` and
`schattenNorm_ofReal`. The endpoints are `schattenNorm_one` (nuclear),
`schattenNorm_two` (real Frobenius) and `schattenNorm_top` (spectral).
Finite unitary invariance is available over either scalar field; the current Frobenius and
transpose bridges are real-specialized.

Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.3–3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix ENNReal NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

open scoped Matrix.Norms.L2Operator in
/-- The Schatten power sum norm of a matrix over `ℝ` or `ℂ` at a finite real exponent. Norm
results assume `1 ≤ p`; the formula is retained for positive-exponent product comparisons.
Bhatia (1997), §IV.2.
atlas: schatten-norms-def (partial) -/
def schattenNormReal {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (p : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
    singularValues A i ^ p) ^ (1 / p)

open scoped Matrix.Norms.L2Operator in
/-- The Schatten norm of a matrix over `ℝ` or `ℂ` at an extended exponent, with infinity
defined exactly as the spectral norm. Norm theorems use `1 ≤ p`.
atlas: schatten-norms-def (partial) -/
def schattenNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n 𝕜) (p : ℝ≥0∞) : ℝ :=
  if p = ∞ then specNorm A else schattenNormReal A p.toReal

open scoped Matrix.Norms.L2Operator in
/-- At exponent infinity, the Schatten norm is the spectral norm. -/
@[simp] theorem schattenNorm_top {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n 𝕜) : schattenNorm A ∞ = specNorm A := by
  simp [schattenNorm]

open scoped Matrix.Norms.L2Operator in
/-- At every finite extended exponent, the formula is its finite real power sum. -/
theorem schattenNorm_eq_of_ne_top {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n 𝕜) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    schattenNorm A p = schattenNormReal A p.toReal := by
  simp [schattenNorm, hp]

open scoped Matrix.Norms.L2Operator in
/-- At a nonnegative real exponent, the main interface agrees with the finite power sum. -/
@[simp] theorem schattenNorm_ofReal {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n 𝕜) {p : ℝ} (hp : 0 ≤ p) :
    schattenNorm A (ENNReal.ofReal p) = schattenNormReal A p := by
  simp [schattenNorm, ENNReal.toReal_ofReal hp]

open scoped Matrix.Norms.L2Operator in
/-- Coercing a finite nonnegative exponent preserves the finite power-sum formula. -/
@[simp] theorem schattenNorm_coe {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n 𝕜) (p : ℝ≥0) :
    schattenNorm A (p : ℝ≥0∞) = schattenNormReal A (p : ℝ) := by
  simp [schattenNorm]

open scoped Matrix.Norms.L2Operator in
/-- Schatten power sum norms are nonnegative. -/
theorem schattenNormReal_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (p : ℝ) : 0 ≤ schattenNormReal A p :=
  Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg _ i) p) _

open scoped Matrix.Norms.L2Operator in
/-- Schatten norms are nonnegative, including exponent infinity. -/
theorem schattenNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n 𝕜) (p : ℝ≥0∞) : 0 ≤ schattenNorm A p := by
  by_cases hp : p = ∞
  · subst p
    exact specNorm_nonneg A
  · rw [schattenNorm_eq_of_ne_top _ hp]
    exact schattenNormReal_nonneg A _

open scoped Matrix.Norms.L2Operator in
/-- Relabeling the rows and columns preserves every Schatten power sum over
any real or complex scalar field. -/
theorem schattenNormReal_reindex {m n r s : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s]
    [DecidableEq n] [DecidableEq s] (A : Matrix m n 𝕜) (em : m ≃ r) (en : n ≃ s) (p : ℝ) :
    schattenNormReal (A.reindex em en) p = schattenNormReal A p := by
  simp only [schattenNormReal, singularValues_reindex,
    ← Fintype.card_congr em, ← Fintype.card_congr en]

open scoped Matrix.Norms.L2Operator in
/-- The Schatten-1 norm is precisely the nuclear norm, at every matrix shape. -/
@[simp] theorem schattenNormReal_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : schattenNormReal A 1 = nuclearNorm A := by
  simp [schattenNormReal, nuclearNorm, kyFanNorm_eq_sum_range]

open scoped Matrix.Norms.L2Operator in
/-- The Schatten-1 endpoint is the nuclear norm. -/
@[simp] theorem schattenNorm_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n 𝕜) : schattenNorm A 1 = nuclearNorm A := by
  simp [schattenNorm]

open scoped Matrix.Norms.L2Operator in
/-- `Fin` step of `schattenNormReal_two`. -/
private theorem schattenNormReal_two_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    schattenNormReal A 2 = frobNorm A := by
  simp only [schattenNormReal, Real.rpow_two, one_div]
  change (∑ i ∈ Finset.range (min (Fintype.card (Fin m)) (Fintype.card (Fin n))),
    singularValues A i ^ 2) ^ ((2 : ℝ)⁻¹) = _
  rw [← frobSq_eq_sum_sq_singularValues, ← one_div (2 : ℝ), ← Real.sqrt_eq_rpow]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The Schatten-2 norm of a real matrix is precisely the Frobenius norm, on arbitrary finite
matrix index types. Real-only until `frobSq_eq_sum_sq_singularValues` and `frobNorm_reindex`
are generalised. -/
theorem schattenNormReal_two {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : schattenNormReal A 2 = frobNorm A := by
  rw [← schattenNormReal_reindex A (Fintype.equivFin m) (Fintype.equivFin n),
    schattenNormReal_two_fin, frobNorm_reindex]

open scoped Matrix.Norms.L2Operator in
/-- The Schatten-2 endpoint of a real matrix is the Frobenius norm. -/
@[simp] theorem schattenNorm_two {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℝ) : schattenNorm A 2 = frobNorm A := by
  simp [schattenNorm, schattenNormReal_two]

section FiniteIndex

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Unitary left multiplication (`Uᴴ U = 1`; at `ℝ`, orthogonal) preserves every finite Schatten
power sum: the Gram matrices `(UA)ᴴ(UA)` and `AᴴA` agree. -/
theorem schattenNormReal_orthogonal_mul (A : Matrix m n 𝕜) {U : Matrix m m 𝕜}
    (hU : HasOrthonormalCols U) (p : ℝ) : schattenNormReal (U * A) p = schattenNormReal A p := by
  have hσ : singularValues (U * A) = singularValues A := funext <|
    singularValues_eq_of_gram_eq (U * A) A (by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U A,
        hU.conjTranspose_mul_self, Matrix.one_mul])
  simp only [schattenNormReal, hσ]

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- Unitary right multiplication (`Vᴴ V = 1`; at `ℝ`, orthogonal) preserves every finite
Schatten power sum: the Gram matrix `Vᴴ (AᴴA) V` is unitarily similar to `AᴴA`, so the two have
the same characteristic polynomial. -/
theorem schattenNormReal_mul_orthogonal (A : Matrix m n 𝕜) {V : Matrix n n 𝕜}
    (hV : HasOrthonormalCols V) (p : ℝ) : schattenNormReal (A * V) p = schattenNormReal A p := by
  have hVV : V * Vᴴ = 1 := mul_eq_one_comm.1 hV.conjTranspose_mul_self
  have hσ : singularValues (A * V) = singularValues A := funext <|
    singularValues_eq_of_gram_charpoly_eq (A * V) A (by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.charpoly_mul_comm,
        Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one])
  simp only [schattenNormReal, hσ]

open scoped Matrix.Norms.L2Operator in
/-- Transposition preserves every finite Schatten power sum of a real matrix. Real-only until
`singularValues_transpose` has a `conjTranspose` form. -/
theorem schattenNormReal_transpose (A : Matrix m n ℝ) (p : ℝ) :
    schattenNormReal Aᵀ p = schattenNormReal A p := by
  simp only [schattenNormReal, singularValues_transpose, min_comm]

end FiniteIndex

end NLAlib
