import NLAlib.Matrix.Norms.SymmetricGauge
import NLAlib.Matrix.Spectral.SingularValueInvariance
import NLAlib.Matrix.Inequalities.KyFanNorms
import NLAlib.Matrix.Norms.NuclearNorm
import NLAlib.Matrix.Inequalities.KyFanSums
/-!
# Orthogonally invariant norms from symmetric gauges

Every symmetric gauge defines a genuine invariant matrix norm on a fixed
rectangular shape. The matrix triangle inequality is derived from the proved
Ky Fan weak-majorization theorem and scalar gauge dominance.
Source: Bhatia (1997), Theorem IV.2.1; Horn–Johnson (2013), §7.4.7.
Atlas: `unitarily-invariant-norm-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- An orthogonally invariant real matrix norm in Mathlib's bundled seminorm
vocabulary, with an explicit separating zero criterion. This is the real form
of a unitarily invariant norm, for arbitrary finite rectangular index types.
atlas: unitarily-invariant-norm-def (partial) -/
structure OrthogonallyInvariantNorm (m n : Type*) [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] where
  /-- The underlying real matrix seminorm. -/
  seminorm : Seminorm ℝ (Matrix m n ℝ)
  /-- The seminorm separates zero and is therefore a genuine norm. -/
  eq_zero_of_map_eq_zero : ∀ A, seminorm A = 0 → A = 0
  /-- Orthogonal multiplication on the left preserves the norm. -/
  left_invariant : ∀ (A : Matrix m n ℝ) (U : Matrix m m ℝ), HasOrthonormalCols U → seminorm (U * A) = seminorm A
  /-- Orthogonal multiplication on the right preserves the norm. -/
  right_invariant : ∀ (A : Matrix m n ℝ) (V : Matrix n n ℝ), HasOrthonormalCols V → seminorm (A * V) = seminorm A

namespace SymmetricGauge

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable (Φ : SymmetricGauge (Fin (min (Fintype.card m) (Fintype.card n))))

/-- Gauge evaluation of the singular values of a matrix. -/
def matrixValue (A : Matrix m n ℝ) : ℝ :=
  Φ.value (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i)

/-- The singular-value gauge is subadditive as a function of the actual matrix,
by Ky Fan weak majorization and the vector norm triangle inequality. -/
theorem matrixValue_add_le (A B : Matrix m n ℝ) :
    Φ.matrixValue (A + B) ≤ Φ.matrixValue A + Φ.matrixValue B := by
  have hweak := weaklyMajorized_singularValues_add A B
  have h := Φ.value_le_of_weaklyMajorized (fun i => singularValues_nonneg _ i) hweak
  exact h.trans (map_add_le_add Φ.seminorm
    (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i)
    (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues B i))

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
/-- A genuine scalar gauge separates the zero matrix through its singular values. -/
theorem eq_zero_of_matrixValue_eq_zero (A : Matrix m n ℝ) (hA : Φ.matrixValue A = 0) : A = 0 := by
  have hσ : (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i) = 0 :=
    Φ.eq_zero_of_map_eq_zero _ hA
  apply (nuclearNorm_eq_zero_iff A).mp
  change (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)), singularValues A i) = 0
  rw [← Fin.sum_univ_eq_sum_range (fun i => singularValues A i)]
  rw [hσ]
  simp

/-- The bundled matrix seminorm induced by the symmetric gauge. -/
def matrixSeminorm : Seminorm ℝ (Matrix m n ℝ) :=
  Seminorm.of Φ.matrixValue Φ.matrixValue_add_le
    (fun c A => by simpa only [Real.norm_eq_abs] using Φ.matrixValue_smul A c)

/-- The induced matrix seminorm evaluates exactly to the gauge of the singular values. -/
@[simp] theorem matrixSeminorm_apply (A : Matrix m n ℝ) : Φ.matrixSeminorm A = Φ.matrixValue A := rfl

/-- Every symmetric gauge produces a genuine orthogonally invariant matrix
norm, with all norm axioms proved from singular-value inequalities.
Bhatia (1997), Theorem IV.2.1.
atlas: unitarily-invariant-norm-def (partial) -/
def toOrthogonallyInvariantNorm : OrthogonallyInvariantNorm m n where
  seminorm := Φ.matrixSeminorm
  eq_zero_of_map_eq_zero := Φ.eq_zero_of_matrixValue_eq_zero
  left_invariant A U hU := by
    apply congrArg Φ.value
    funext i
    exact congrFun (singularValues_isometry_mul hU A) i
  right_invariant A V hV := by
    apply congrArg Φ.value
    funext i
    exact congrFun (singularValues_mul_orthogonal A hV) i

/-- The genuine invariant norm induced by a symmetric gauge evaluates to the
gauge of the actual singular-value vector. Bhatia, Theorem IV.2.1. -/
@[simp] theorem toOrthogonallyInvariantNorm_apply (A : Matrix m n ℝ) :
    Φ.toOrthogonallyInvariantNorm.seminorm A = Φ.matrixValue A := rfl

end SymmetricGauge
end NLAlib
