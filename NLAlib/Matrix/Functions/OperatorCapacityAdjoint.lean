import NLAlib.Matrix.Functions.OperatorCapacity
import NLAlib.Matrix.Functions.DeterminantTraceVariational

/-!
# Operator capacity and trace adjoints

Positive semidefiniteness-preserving real-linear maps have equal operator
capacities when they are adjoints under the trace pairing. The proof compares
lower bounds through the determinant-trace variational formula. It includes
singular images and zero capacity without assuming an attaining test matrix.

For the actual finite Kraus map, cyclicity of trace proves the adjoint relation
with the family of conjugate-transposed Kraus matrices. Its operator capacity
therefore equals the capacity of that adjoint family.

All finite matrix dimensions and finite Kraus families are allowed. In the empty
matrix dimension, every operator capacity is `1`, since every determinant is `1`.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In the empty matrix dimension, every real-linear map has operator capacity
`1`. No positivity assumption is needed. -/
theorem operatorCapacity_eq_one_of_isEmpty [IsEmpty n]
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    operatorCapacity T = 1 := by
  unfold operatorCapacity
  have hset :
      {d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re} =
        {1} := by
    ext d
    constructor
    · rintro ⟨X, hXpos, hXdet, hd⟩
      rw [hd]
      rw [Matrix.det_isEmpty]
      rfl
    · intro hd
      refine ⟨1, Matrix.PosDef.one, Matrix.det_one, ?_⟩
      rw [Matrix.det_isEmpty, hd]
      rfl
  rw [hset]
  exact csInf_singleton 1

omit [DecidableEq n] in
/-- Exact trace duality between a finite Kraus family and its
conjugate-transposed family. The test matrices need not be Hermitian. -/
theorem trace_mul_krausMap_eq_trace_mul_krausMap_conjTranspose
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (X Y : Matrix n n ℂ) :
    (Y * krausMap A X).trace = (X * krausMap (fun i => (A i).conjTranspose) Y).trace := by
  rw [krausMap_apply, krausMap_apply]
  rw [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  calc
    (Y * (A i * X * (A i).conjTranspose)).trace
        = ((Y * A i) * X * (A i).conjTranspose).trace := by
          simp [Matrix.mul_assoc]
    _ = ((A i).conjTranspose * Y * A i * X).trace := by
          simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle (Y * A i) X
            (A i).conjTranspose
    _ = (X * (A i).conjTranspose * Y * A i).trace := by
          simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm
            ((A i).conjTranspose * Y * A i) X
    _ = (X * ((A i).conjTranspose * Y * ((A i).conjTranspose).conjTranspose)).trace := by
          simp [Matrix.mul_assoc, Matrix.conjTranspose_conjTranspose]

private theorem operatorCapacity_le_of_trace_eq
    (hN : 0 < Fintype.card n)
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (hS : ∀ X, X.PosSemidef → (S X).PosSemidef)
    (htrace : ∀ X Y, (Y * T X).trace = (X * S Y).trace) :
    operatorCapacity T ≤ operatorCapacity S := by
  apply le_csInf (operatorCapacity_attainable_nonempty S)
  rintro d ⟨Y, hY, hYdet, rfl⟩
  apply ((hS Y hY.posSemidef).isGLB_determinantTraceObjectiveSet hN).2
  rintro v ⟨X, hX, hXdet, rfl⟩
  calc
    operatorCapacity T ≤ (T X).det.re :=
      csInf_le (operatorCapacity_attainable_bddBelow T hT) ⟨X, hX, hXdet, rfl⟩
    _ ≤ (RCLike.re (Y * T X).trace / (Fintype.card n : ℝ)) ^ Fintype.card n :=
      (hT X hX.posSemidef).re_det_le_objective_of_det_one hN hY hYdet
    _ = (RCLike.re (X * S Y).trace / (Fintype.card n : ℝ)) ^ Fintype.card n := by
      rw [htrace X Y]

/-- Generic operator-capacity equality: if the real-linear maps `T` and `S`
preserve positive semidefiniteness and satisfy the trace identity
`trace (Y * T X) = trace (X * S Y)` for all `X`, `Y`, then
`operatorCapacity T = operatorCapacity S`.

The proof is a pure lower-bound argument: for a normalized positive definite `Y`
and PSD `M`, `re M.det` is the greatest lower bound of the determinant-trace
objective set of `M` (`Matrix.PosSemidef.isGLB_determinantTraceObjectiveSet`),
and the trace identity converts the objective of `S Y` at `X` into the objective
of `T X` at `Y`.  The empty dimension is handled separately by
`operatorCapacity_eq_one_of_isEmpty`. -/
theorem operatorCapacity_eq_of_trace_eq
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (hS : ∀ X, X.PosSemidef → (S X).PosSemidef)
    (htrace : ∀ X Y, (Y * T X).trace = (X * S Y).trace) :
    operatorCapacity T = operatorCapacity S := by
  classical
  by_cases hN : 0 < Fintype.card n
  · exact le_antisymm
      (operatorCapacity_le_of_trace_eq hN T S hT hS htrace)
      (operatorCapacity_le_of_trace_eq hN S T hS hT fun X Y => (htrace Y X).symm)
  · have hcard0 : Fintype.card n = 0 := Nat.eq_zero_of_not_pos hN
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hcard0
    rw [operatorCapacity_eq_one_of_isEmpty T, operatorCapacity_eq_one_of_isEmpty S]

/-- Operator capacity is invariant under taking the adjoint of a finite Kraus
family: `operatorCapacity (krausMap A) = operatorCapacity (krausMap A†)`.
This covers all finite dimensions, including the empty one, and singular or
zero-capacity maps. -/
theorem operatorCapacity_krausMap_conjTranspose
    {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ) :
    operatorCapacity (krausMap A) = operatorCapacity (krausMap (fun i => (A i).conjTranspose)) := by
  exact operatorCapacity_eq_of_trace_eq (krausMap A) (krausMap (fun i => (A i).conjTranspose))
    (krausMap_posSemidef A) (krausMap_posSemidef (fun i => (A i).conjTranspose))
    (fun X Y => trace_mul_krausMap_eq_trace_mul_krausMap_conjTranspose A X Y)

end NLAlib
