import NLAlib.Matrix.InvariantNormRepresentation
import NLAlib.Matrix.Mirsky

/-!
# Fan dominance and invariant-norm perturbation bounds

All invariant norms are represented by actual symmetric gauges. Conversely,
testing the genuine Ky Fan norms recovers every weak-majorization prefix.
Mirsky's proved thin singular-value majorization gives its full fixed-shape
invariant-norm consequence. Source: Bhatia (1997), Theorem IV.2.2; Mirsky (1960).
Atlas: `unitarily-invariant-norm-def`, `lidskii`.
-/

noncomputable section
open scoped Matrix BigOperators

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Every positive Ky Fan prefix is a genuine orthogonally invariant matrix norm. -/
def kyFanInvariantNorm (k : ℕ) (hk : 1 ≤ k) : OrthogonallyInvariantNorm m n where
  seminorm := kyFanSeminorm k
  eq_zero_of_map_eq_zero A hA := (kyFanNorm_eq_zero_iff A hk).mp hA
  left_invariant A _U hU := kyFanNorm_orthogonal_mul A hU k
  right_invariant A _V hV := kyFanNorm_mul_orthogonal A hV k

omit [DecidableEq m] in
/-- Intrinsic top-coordinate sums of the singular-value vector are precisely
the Ky Fan sums for every admissible thin prefix. -/
theorem sumLargest_singularValueVector_eq_kyFanNorm (A : Matrix m n ℝ) {k : ℕ}
    (hk : k ≤ min (Fintype.card m) (Fintype.card n)) :
    sumLargest (singularValueVector A) k = kyFanNorm A k := by
  rw [sumLargest_eq_prefix_of_antitone _ (show Antitone (singularValueVector A) from
    fun i j hij => LinearMap.singularValues_antitone _ hij)]
  simp only [singularValueVector]
  rw [sum_fin_ite_lt_eq_sum_range hk A.toEuclideanLin.singularValues]
  rfl

/-- Fan dominance in both directions for all genuine invariant norms on a fixed
rectangular matrix space. This has no gauge-representation or dominance premise.
Bhatia (1997), Theorem IV.2.2.
atlas: unitarily-invariant-norm-def (partial) -/
theorem forall_invariantNorm_le_iff_weaklyMajorized (A B : Matrix m n ℝ) :
    (∀ ν : OrthogonallyInvariantNorm m n, ν.seminorm A ≤ ν.seminorm B) ↔
      WeaklyMajorized (singularValueVector A) (singularValueVector B) := by
  constructor
  · intro h k hk
    have hkN : k ≤ min (Fintype.card m) (Fintype.card n) := by simpa using hk
    rw [sumLargest_singularValueVector_eq_kyFanNorm A hkN,
      sumLargest_singularValueVector_eq_kyFanNorm B hkN]
    by_cases hk0 : k = 0
    · simp [hk0]
    · exact h (kyFanInvariantNorm k (by omega))
  · intro h ν
    rw [ν.seminorm_eq_toSymmetricGauge_matrixValue A, ν.seminorm_eq_toSymmetricGauge_matrixValue B]
    exact ν.toSymmetricGauge.value_le_of_weaklyMajorized
      (fun i => LinearMap.singularValues_nonneg _ i) h

/-- Every invariant norm has a fixed actual symmetric gauge representation,
valid simultaneously for every matrix of that shape.
Bhatia (1997), Theorem IV.2.1.
atlas: unitarily-invariant-norm-def (partial) -/
theorem OrthogonallyInvariantNorm.exists_symmetricGauge_representation
    (ν : OrthogonallyInvariantNorm m n) :
    ∃ Φ : SymmetricGauge (Fin (min (Fintype.card m) (Fintype.card n))),
      ∀ A : Matrix m n ℝ, ν.seminorm A = Φ.matrixValue A :=
  ⟨ν.toSymmetricGauge, ν.seminorm_eq_toSymmetricGauge_matrixValue⟩

/-- Mirsky's perturbation bound in every invariant norm on the actual fixed
rectangular matrix space, with sharp constant one. The diagonal embedding has
the same shape as `E`, avoiding application of a rectangular norm to a different
square space. Includes every zero/degenerate dimension and repeated singular value.
atlas: lidskii (partial) -/
theorem invariantNorm_rectangularDiagonal_singularValues_add_sub_le
    (ν : OrthogonallyInvariantNorm m n) (A E : Matrix m n ℝ) :
    ν.seminorm (rectangularDiagonalMatrix (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      (A + E).toEuclideanLin.singularValues i - A.toEuclideanLin.singularValues i)) ≤ ν.seminorm E := by
  let d : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ := fun i =>
    (A + E).toEuclideanLin.singularValues i - A.toEuclideanLin.singularValues i
  have h := ν.toSymmetricGauge.value_le_of_weaklyMajorized
    (fun i => abs_nonneg (d i)) (weaklyMajorized_abs_toEuclideanLin_singularValues_add_sub A E)
  change ν.toSymmetricGauge.value (fun i => |d i|) ≤ ν.toSymmetricGauge.matrixValue E at h
  rw [ν.toSymmetricGauge.value_abs, ν.value_toSymmetricGauge,
    ← ν.seminorm_eq_toSymmetricGauge_matrixValue E] at h
  exact h

end NLAlib
