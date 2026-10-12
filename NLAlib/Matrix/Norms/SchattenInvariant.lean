import NLAlib.Matrix.Norms.SchattenEndpoints
import NLAlib.Matrix.Norms.InvariantNorm
/-!
# Schatten norms as genuine invariant matrix norms

Every extended exponent at least one gives a bundled invariant norm on the
actual finite rectangular matrix space. Finite and infinity cases retain the
same native singular-value and spectral-norm definitions.
Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators ENNReal

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Every extended norm exponent obeys the triangle inequality, including infinity. -/
theorem schattenNormExtended_add_le (A B : Matrix m n ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    schattenNormExtended (A + B) p ≤ schattenNormExtended A p + schattenNormExtended B p := by
  by_cases hpt : p = ∞
  · simp only [hpt, schattenNormExtended_top]
    exact specNorm_add_le A B
  · rw [schattenNormExtended_eq_of_ne_top _ hpt, schattenNormExtended_eq_of_ne_top _ hpt,
      schattenNormExtended_eq_of_ne_top _ hpt]
    exact schattenNorm_add_le A B (by simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hpt hp)

/-- Every extended norm exponent is absolutely homogeneous, including infinity. -/
theorem schattenNormExtended_smul (A : Matrix m n ℝ) (c : ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    schattenNormExtended (c • A) p = |c| * schattenNormExtended A p := by
  by_cases hpt : p = ∞
  · simp only [hpt, schattenNormExtended_top]
    simp only [specNorm_eq_norm, norm_smul, Real.norm_eq_abs]
  · rw [schattenNormExtended_eq_of_ne_top _ hpt, schattenNormExtended_eq_of_ne_top _ hpt]
    exact schattenNorm_smul A c (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt)

/-- Every extended Schatten norm separates zero, including infinity and empty shapes. -/
theorem schattenNormExtended_eq_zero_iff (A : Matrix m n ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    schattenNormExtended A p = 0 ↔ A = 0 := by
  by_cases hpt : p = ∞
  · rw [hpt, schattenNormExtended_top, specNorm_eq_norm]
    exact norm_eq_zero
  · rw [schattenNormExtended_eq_of_ne_top _ hpt]
    exact schattenNorm_eq_zero_iff A (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt)

/-- Orthogonal left multiplication preserves the extended Schatten norm. -/
theorem schattenNormExtended_orthogonal_mul (A : Matrix m n ℝ) {U : Matrix m m ℝ}
    (hU : HasOrthonormalCols U) (p : ℝ≥0∞) :
    schattenNormExtended (U * A) p = schattenNormExtended A p := by
  by_cases hpt : p = ∞
  · simp only [hpt, schattenNormExtended_top]
    exact specNorm_mul_left_of_hasOrthonormalCols hU A
  · rw [schattenNormExtended_eq_of_ne_top _ hpt, schattenNormExtended_eq_of_ne_top _ hpt]
    exact schattenNorm_orthogonal_mul A hU _

/-- Orthogonal right multiplication preserves the extended Schatten norm. -/
theorem schattenNormExtended_mul_orthogonal (A : Matrix m n ℝ) {V : Matrix n n ℝ}
    (hV : HasOrthonormalCols V) (p : ℝ≥0∞) :
    schattenNormExtended (A * V) p = schattenNormExtended A p := by
  by_cases hpt : p = ∞
  · simp only [hpt, schattenNormExtended_top]
    have hVt : HasOrthonormalCols Vᵀ := by
      change Vᵀᵀ * Vᵀ = 1
      rw [Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hV
    simpa only [Matrix.transpose_transpose] using specNorm_mul_transpose_right_of_hasOrthonormalCols hVt A
  · rw [schattenNormExtended_eq_of_ne_top _ hpt, schattenNormExtended_eq_of_ne_top _ hpt]
    exact schattenNorm_mul_orthogonal A hV _

/-- Transposition preserves every extended Schatten norm. -/
theorem schattenNormExtended_transpose (A : Matrix m n ℝ) (p : ℝ≥0∞) :
    schattenNormExtended Aᵀ p = schattenNormExtended A p := by
  by_cases hpt : p = ∞
  · simp only [hpt, schattenNormExtended_top]
    exact specNorm_transpose A
  · rw [schattenNormExtended_eq_of_ne_top _ hpt, schattenNormExtended_eq_of_ne_top _ hpt]
    exact schattenNorm_transpose A _

/-- Every Schatten exponent at least one yields an actual bundled invariant
matrix norm, including the spectral infinity endpoint. All norm axioms and
invariances are proved, with no supplied norm-property premise.
atlas: schatten-norms-def (partial) -/
def schattenInvariantNorm (p : ℝ≥0∞) (hp : 1 ≤ p) : OrthogonallyInvariantNorm m n where
  seminorm := Seminorm.of (fun A => schattenNormExtended A p)
    (fun A B => schattenNormExtended_add_le A B hp)
    (fun c A => by simpa only [Real.norm_eq_abs] using schattenNormExtended_smul A c hp)
  eq_zero_of_map_eq_zero A hA := (schattenNormExtended_eq_zero_iff A hp).mp hA
  left_invariant A _U hU := schattenNormExtended_orthogonal_mul A hU p
  right_invariant A _V hV := schattenNormExtended_mul_orthogonal A hV p

/-- The bundled invariant Schatten norm agrees with the given extended exponent formula. -/
@[simp] theorem schattenInvariantNorm_apply (A : Matrix m n ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    (schattenInvariantNorm p hp).seminorm A = schattenNormExtended A p := rfl

end NLAlib
