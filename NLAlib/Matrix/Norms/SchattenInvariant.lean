import NLAlib.Matrix.Norms.SchattenEndpoints
import NLAlib.Matrix.Norms.InvariantNorm
/-!
# Schatten norms as invariant matrix norms

Every extended exponent at least one gives a bundled invariant norm on the
finite rectangular matrix space. Finite and infinity cases retain the
same native singular-value and spectral-norm definitions.
Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix ENNReal

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Every extended norm exponent obeys the triangle inequality, including infinity. -/
theorem schattenNorm_add_le (A B : Matrix m n ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    schattenNorm (A + B) p ≤ schattenNorm A p + schattenNorm B p := by
  by_cases hpt : p = ∞
  · simp only [hpt, schattenNorm_top]
    exact specNorm_add_le A B
  · rw [schattenNorm_eq_of_ne_top _ hpt, schattenNorm_eq_of_ne_top _ hpt,
      schattenNorm_eq_of_ne_top _ hpt]
    exact schattenNormReal_add_le A B (by simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hpt hp)

open scoped Matrix.Norms.L2Operator in
/-- Every extended norm exponent is absolutely homogeneous, including infinity. -/
theorem schattenNorm_smul (A : Matrix m n ℝ) (c : ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    schattenNorm (c • A) p = |c| * schattenNorm A p := by
  by_cases hpt : p = ∞
  · simp only [hpt, schattenNorm_top]
    simp only [specNorm_eq_norm, norm_smul, Real.norm_eq_abs]
  · rw [schattenNorm_eq_of_ne_top _ hpt, schattenNorm_eq_of_ne_top _ hpt]
    exact schattenNormReal_smul A c (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt)

open scoped Matrix.Norms.L2Operator in
/-- Every extended Schatten norm separates zero, including infinity and empty shapes. -/
theorem schattenNorm_eq_zero_iff (A : Matrix m n ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    schattenNorm A p = 0 ↔ A = 0 := by
  by_cases hpt : p = ∞
  · rw [hpt, schattenNorm_top, specNorm_eq_norm]
    exact norm_eq_zero
  · rw [schattenNorm_eq_of_ne_top _ hpt]
    exact schattenNormReal_eq_zero_iff A (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpt)

/-- Orthogonal left multiplication preserves the extended Schatten norm. -/
theorem schattenNorm_orthogonal_mul (A : Matrix m n ℝ) {U : Matrix m m ℝ}
    (hU : HasOrthonormalCols U) (p : ℝ≥0∞) :
    schattenNorm (U * A) p = schattenNorm A p := by
  by_cases hpt : p = ∞
  · simp only [hpt, schattenNorm_top]
    exact specNorm_mul_left_of_hasOrthonormalCols hU A
  · rw [schattenNorm_eq_of_ne_top _ hpt, schattenNorm_eq_of_ne_top _ hpt]
    exact schattenNormReal_orthogonal_mul A hU _

/-- Orthogonal right multiplication preserves the extended Schatten norm. -/
theorem schattenNorm_mul_orthogonal (A : Matrix m n ℝ) {V : Matrix n n ℝ}
    (hV : HasOrthonormalCols V) (p : ℝ≥0∞) :
    schattenNorm (A * V) p = schattenNorm A p := by
  by_cases hpt : p = ∞
  · simp only [hpt, schattenNorm_top]
    have hVt : HasOrthonormalCols Vᵀ := by
      change Vᵀᵀ * Vᵀ = 1
      rw [Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hV
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using specNorm_mul_conjTranspose_right_of_hasOrthonormalCols (P := Vᵀ) hVt A
  · rw [schattenNorm_eq_of_ne_top _ hpt, schattenNorm_eq_of_ne_top _ hpt]
    exact schattenNormReal_mul_orthogonal A hV _

open scoped Matrix.Norms.L2Operator in
/-- Every Schatten exponent at least one yields a bundled invariant
matrix norm, including the spectral infinity endpoint. All norm axioms and
invariances are proved, with no supplied norm-property premise.
atlas: schatten-norms-def (partial) -/
def schattenInvariantNorm (p : ℝ≥0∞) (hp : 1 ≤ p) : UnitarilyInvariantNorm ℝ m n where
  seminorm := Seminorm.of (fun A => schattenNorm A p)
    (fun A B => schattenNorm_add_le A B hp)
    (fun c A => by simpa only [Real.norm_eq_abs] using schattenNorm_smul A c hp)
  eq_zero_of_map_eq_zero A hA := (schattenNorm_eq_zero_iff A hp).mp hA
  left_invariant A _U hU := schattenNorm_orthogonal_mul A hU p
  right_invariant A _V hV := schattenNorm_mul_orthogonal A hV p

open scoped Matrix.Norms.L2Operator in
/-- The bundled invariant Schatten norm agrees with the given extended exponent formula. -/
@[simp] theorem schattenInvariantNorm_apply (A : Matrix m n ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    (schattenInvariantNorm p hp).seminorm A = schattenNorm A p := rfl

end NLAlib
