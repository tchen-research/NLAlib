import NLAlib.Matrix.Norms.KyFanNorm
import NLAlib.Matrix.Spectral.SingularValueInvariance

/-!
# Schatten norm definitions and scalar exponents

Over `ℝ` or `ℂ` (any `[RCLike 𝕜]`), finite real exponents use their usual singular-value power
sum. The extended exponent definition includes infinity explicitly as the spectral norm. Both are
real-valued and, at `𝕜 := ℝ`, are the real definitions verbatim.

General API: the extended-exponent unfoldings, nonnegativity, `schattenNorm_one` (the nuclear
norm) and invariance under left and right multiplication by a unitary matrix
(`HasOrthonormalCols`, i.e. `Uᴴ U = 1`; at `ℝ` an orthogonal matrix). Still real-only, because the
singular-value facts they rest on are real-only for now: `schattenNorm_reindex`,
`schattenNorm_two` (the Frobenius norm) and `schattenNorm_transpose`.

Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.3–3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

open scoped Matrix.Norms.L2Operator in
/-- The Schatten power sum norm of a matrix over `ℝ` or `ℂ` at a finite real exponent. Norm
results assume `1 ≤ p`; the formula is retained for positive-exponent product comparisons.
Bhatia (1997), §IV.2.
atlas: schatten-norms-def (partial) -/
def schattenNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (p : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
    singularValues A i ^ p) ^ (1 / p)

open scoped Matrix.Norms.L2Operator in
/-- The Schatten norm of a matrix over `ℝ` or `ℂ` at an extended exponent, with infinity
defined exactly as the spectral norm. Norm theorems use `1 ≤ p`.
atlas: schatten-norms-def (partial) -/
def schattenNormExtended {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n 𝕜) (p : ℝ≥0∞) : ℝ :=
  if p = ∞ then specNorm A else schattenNorm A p.toReal

open scoped Matrix.Norms.L2Operator in
/-- At exponent infinity, the Schatten norm is the spectral norm. -/
@[simp] theorem schattenNormExtended_top {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n 𝕜) : schattenNormExtended A ∞ = specNorm A := by
  simp [schattenNormExtended]

open scoped Matrix.Norms.L2Operator in
/-- At every finite extended exponent, the formula is its finite real power sum. -/
theorem schattenNormExtended_eq_of_ne_top {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n 𝕜) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    schattenNormExtended A p = schattenNorm A p.toReal := by
  simp [schattenNormExtended, hp]

open scoped Matrix.Norms.L2Operator in
/-- Schatten power sum norms are nonnegative. -/
theorem schattenNorm_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (p : ℝ) : 0 ≤ schattenNorm A p :=
  Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg _ i) p) _

open scoped Matrix.Norms.L2Operator in
/-- Relabeling the rows and columns of a real matrix preserves every Schatten power sum.
Real-only until `singularValues_reindex` is generalised. -/
theorem schattenNorm_reindex {m n r s : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s]
    [DecidableEq n] [DecidableEq s] (A : Matrix m n ℝ) (em : m ≃ r) (en : n ≃ s) (p : ℝ) :
    schattenNorm (A.reindex em en) p = schattenNorm A p := by
  simp only [schattenNorm, singularValues_reindex,
    ← Fintype.card_congr em, ← Fintype.card_congr en]

open scoped Matrix.Norms.L2Operator in
/-- The Schatten-1 norm is precisely the nuclear norm, at every matrix shape. -/
@[simp] theorem schattenNorm_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : schattenNorm A 1 = nuclearNorm A := by
  simp [schattenNorm, nuclearNorm, kyFanNorm_eq_sum_range]

open scoped Matrix.Norms.L2Operator in
/-- `Fin` step of `schattenNorm_two`. -/
private theorem schattenNorm_two_fin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    schattenNorm A 2 = frobNorm A := by
  simp only [schattenNorm, Real.rpow_two, one_div]
  change (∑ i ∈ Finset.range (min (Fintype.card (Fin m)) (Fintype.card (Fin n))),
    singularValues A i ^ 2) ^ ((2 : ℝ)⁻¹) = _
  rw [← frobSq_eq_sum_sq_singularValues, ← one_div (2 : ℝ), ← Real.sqrt_eq_rpow]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The Schatten-2 norm of a real matrix is precisely the Frobenius norm, on arbitrary finite
matrix index types. Real-only until `frobSq_eq_sum_sq_singularValues` and `frobNorm_reindex`
are generalised. -/
theorem schattenNorm_two {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : schattenNorm A 2 = frobNorm A := by
  rw [← schattenNorm_reindex A (Fintype.equivFin m) (Fintype.equivFin n),
    schattenNorm_two_fin, frobNorm_reindex]

section FiniteIndex

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Unitary left multiplication (`Uᴴ U = 1`; at `ℝ`, orthogonal) preserves every finite Schatten
power sum: the Gram matrices `(UA)ᴴ(UA)` and `AᴴA` agree. -/
theorem schattenNorm_orthogonal_mul (A : Matrix m n 𝕜) {U : Matrix m m 𝕜}
    (hU : HasOrthonormalCols U) (p : ℝ) : schattenNorm (U * A) p = schattenNorm A p := by
  have hσ : singularValues (U * A) = singularValues A := funext <|
    singularValues_eq_of_gram_eq (U * A) A (by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U A,
        hU.conjTranspose_mul_self, Matrix.one_mul])
  simp only [schattenNorm, hσ]

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- Unitary right multiplication (`Vᴴ V = 1`; at `ℝ`, orthogonal) preserves every finite
Schatten power sum: the Gram matrix `Vᴴ (AᴴA) V` is unitarily similar to `AᴴA`, so the two have
the same characteristic polynomial. -/
theorem schattenNorm_mul_orthogonal (A : Matrix m n 𝕜) {V : Matrix n n 𝕜}
    (hV : HasOrthonormalCols V) (p : ℝ) : schattenNorm (A * V) p = schattenNorm A p := by
  have hVV : V * Vᴴ = 1 := mul_eq_one_comm.1 hV.conjTranspose_mul_self
  have hσ : singularValues (A * V) = singularValues A := funext <|
    singularValues_eq_of_gram_charpoly_eq (A * V) A (by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.charpoly_mul_comm,
        Matrix.mul_assoc, Matrix.mul_assoc, hVV, Matrix.mul_one])
  simp only [schattenNorm, hσ]

open scoped Matrix.Norms.L2Operator in
/-- Transposition preserves every finite Schatten power sum of a real matrix. Real-only until
`singularValues_transpose` has a `conjTranspose` form. -/
theorem schattenNorm_transpose (A : Matrix m n ℝ) (p : ℝ) :
    schattenNorm Aᵀ p = schattenNorm A p := by
  simp only [schattenNorm, singularValues_transpose, min_comm]

end FiniteIndex

end NLAlib
