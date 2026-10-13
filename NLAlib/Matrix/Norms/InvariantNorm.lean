import NLAlib.Matrix.Norms.SymmetricGauge
import NLAlib.Matrix.Spectral.SingularValueInvariance
import NLAlib.Matrix.Inequalities.KyFanNorms
import NLAlib.Matrix.Norms.NuclearNorm
import NLAlib.Matrix.Inequalities.KyFanSums
/-!
# Unitarily invariant norms from symmetric gauges

`UnitarilyInvariantNorm 𝕜 m n` is the bundled vocabulary for unitarily invariant matrix norms
(orthogonally invariant at `𝕜 = ℝ`). Every symmetric gauge defines an invariant matrix norm on a
fixed real rectangular shape (`SymmetricGauge.toUnitarilyInvariantNorm`). The matrix triangle inequality is derived from the proved
Ky Fan weak-majorization theorem and scalar gauge dominance.
Source: Bhatia (1997), Theorem IV.2.1; Horn–Johnson (2013), §7.4.7.
Atlas: `unitarily-invariant-norm-def`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- A unitarily invariant matrix norm on `Matrix m n 𝕜` (`𝕜 = ℝ` or `ℂ`) in Mathlib's bundled
real-seminorm vocabulary, with an explicit separating zero criterion: a real seminorm `ν` with
`ν (U A V) = ν A` for unitary `U`, `V` (`HasOrthonormalCols`). At `𝕜 = ℝ` this is an
orthogonally invariant norm. Horn–Johnson 2013, §7.4.7; Bhatia 1997, §IV.2.
atlas: unitarily-invariant-norm-def -/
structure UnitarilyInvariantNorm (𝕜 : Type*) [RCLike 𝕜] (m n : Type*) [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] where
  /-- The underlying real matrix seminorm. -/
  seminorm : Seminorm ℝ (Matrix m n 𝕜)
  /-- The seminorm separates zero and is therefore a norm. -/
  eq_zero_of_map_eq_zero : ∀ A, seminorm A = 0 → A = 0
  /-- Unitary multiplication on the left preserves the norm. -/
  left_invariant : ∀ (A : Matrix m n 𝕜) (U : Matrix m m 𝕜), HasOrthonormalCols U →
    seminorm (U * A) = seminorm A
  /-- Unitary multiplication on the right preserves the norm. -/
  right_invariant : ∀ (A : Matrix m n 𝕜) (V : Matrix n n 𝕜), HasOrthonormalCols V →
    seminorm (A * V) = seminorm A

/-- Transposition transports a real invariant norm to the transposed matrix shape.
Horn–Johnson 2013, §7.4. -/
def UnitarilyInvariantNorm.transpose {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (ν : UnitarilyInvariantNorm ℝ m n) :
    UnitarilyInvariantNorm ℝ n m where
  seminorm := ν.seminorm.comp (Matrix.transposeLinearEquiv n m ℝ ℝ).toLinearMap
  eq_zero_of_map_eq_zero A hA := by
    have h := ν.eq_zero_of_map_eq_zero Aᵀ hA
    apply Matrix.transpose_injective
    exact h
  left_invariant A V hV := by
    change ν.seminorm (V * A)ᵀ = ν.seminorm Aᵀ
    have hVt : HasOrthonormalCols Vᵀ := by
      change Vᵀᵀ * Vᵀ = 1
      rw [Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hV
    rw [Matrix.transpose_mul, ν.right_invariant _ _ hVt]
  right_invariant A U hU := by
    change ν.seminorm (A * U)ᵀ = ν.seminorm Aᵀ
    have hUt : HasOrthonormalCols Uᵀ := by
      change Uᵀᵀ * Uᵀ = 1
      rw [Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hU
    rw [Matrix.transpose_mul, ν.left_invariant _ _ hUt]

namespace SymmetricGauge

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable (Φ : SymmetricGauge (Fin (min (Fintype.card m) (Fintype.card n))))

/-- Gauge evaluation of the singular values of a matrix. -/
def matrixValue (A : Matrix m n ℝ) : ℝ :=
  Φ.value (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i)

/-- The singular-value gauge is subadditive as a function of the matrix,
by Ky Fan weak majorization and the vector norm triangle inequality. -/
theorem matrixValue_add_le (A B : Matrix m n ℝ) :
    Φ.matrixValue (A + B) ≤ Φ.matrixValue A + Φ.matrixValue B := by
  have hweak := weaklyMajorized_singularValues_add A B
  have h := Φ.value_le_of_weaklyMajorized (fun i => singularValues_nonneg _ i) hweak
  exact h.trans (map_add_le_add Φ.seminorm
    (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i)
    (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues B i))

open scoped Matrix.Norms.L2Operator in
omit [DecidableEq m] in
/-- A singular-value gauge is absolutely homogeneous over real scalars. -/
theorem matrixValue_smul (A : Matrix m n ℝ) (c : ℝ) : Φ.matrixValue (c • A) = |c| * Φ.matrixValue A := by
  have hσ : (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues (c • A) i) =
      |c| • (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i) := by
    funext i
    exact singularValues_smul A c i
  rw [matrixValue, hσ, value, map_smul_eq_mul, Real.norm_eq_abs, abs_abs]
  rfl

omit [DecidableEq m] in
/-- A scalar gauge separates the zero matrix through its singular values. -/
theorem eq_zero_of_matrixValue_eq_zero (A : Matrix m n ℝ) (hA : Φ.matrixValue A = 0) : A = 0 := by
  have hσ : (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i) = 0 :=
    Φ.eq_zero_of_map_eq_zero _ hA
  apply (nuclearNorm_eq_zero_iff A).mp
  rw [nuclearNorm_eq_sum_range]
  rw [← Fin.sum_univ_eq_sum_range (fun i => singularValues A i)]
  rw [hσ]
  simp

open scoped Matrix.Norms.L2Operator in
/-- The bundled matrix seminorm induced by the symmetric gauge. -/
def matrixSeminorm : Seminorm ℝ (Matrix m n ℝ) :=
  Seminorm.of Φ.matrixValue Φ.matrixValue_add_le
    (fun c A => by simpa only [Real.norm_eq_abs] using Φ.matrixValue_smul A c)

open scoped Matrix.Norms.L2Operator in
/-- The induced matrix seminorm evaluates exactly to the gauge of the singular values. -/
@[simp] theorem matrixSeminorm_apply (A : Matrix m n ℝ) : Φ.matrixSeminorm A = Φ.matrixValue A := rfl

open scoped Matrix.Norms.L2Operator in
/-- Every symmetric gauge produces a orthogonally invariant matrix
norm, with all norm axioms proved from singular-value inequalities.
Bhatia (1997), Theorem IV.2.1.
atlas: unitarily-invariant-norm-def (partial) -/
def toUnitarilyInvariantNorm : UnitarilyInvariantNorm ℝ m n where
  seminorm := Φ.matrixSeminorm
  eq_zero_of_map_eq_zero := Φ.eq_zero_of_matrixValue_eq_zero
  left_invariant A U hU := by
    apply congrArg Φ.value
    funext i
    exact congrFun (singularValues_isometry_mul hU A) i
  right_invariant A V hV := by
    apply congrArg Φ.value
    funext i
    exact congrFun (singularValues_mul_unitary A hV) i

open scoped Matrix.Norms.L2Operator in
/-- The invariant norm induced by a symmetric gauge evaluates to the
gauge of the singular-value vector. Bhatia, Theorem IV.2.1. -/
@[simp] theorem toUnitarilyInvariantNorm_apply (A : Matrix m n ℝ) :
    Φ.toUnitarilyInvariantNorm.seminorm A = Φ.matrixValue A := rfl

end SymmetricGauge
end NLAlib
