/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyRaisingBound

set_option autoImplicit false

/-!
# Restricted heavy lowering operator bound

Transpose factorization and the zero, one, and general-grade lowering estimates.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Transposing the heavy raising band gives the heavy lowering band.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hplus_transpose_eq_Hminus (F : Frame n d) :
    (Hplus m (frameRows F)).transpose = Hminus m (frameRows F) := by
  rw [Hplus, Hminus, wordSum, wordSum,
    DirectionalConcrete.transpose_physicalWordSum]
  rfl

/-- The lowering band is the literal transpose row-leg product.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hminus_eq_AUpStackTranspose_mul_ADownStack (F : Frame n d) :
    Hminus m (frameRows F) =
      (AUpStack (m := m) F).transpose * ADownStack (m := m) F := by
  rw [← Hplus_transpose_eq_Hminus, Hplus_eq_BUpStack_mul_AUpStack,
    Matrix.transpose_mul, BUpStack_transpose]

/-- The transposed creation stack restricted to its middle grade has norm at most the square root of the input grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpStackTranspose_rowGradeProjection_norm
    (F : Frame n d) (k : ℕ) :
    ‖(AUpStack (m := m) F).transpose *
        rowGradeProjection (m := m) (n := n) (k + 1)‖ ≤ Real.sqrt k := by
  let A := AUpStack (m := m) F
  let R := rowGradeProjection (m := m) (n := n) (k + 1)
  let P := gradeProjection (d := d) (m := m) (n := n) k
  have ht : (A.transpose * R).transpose = R * A := by
    simp [A, R, Matrix.transpose_mul]
  calc
    ‖A.transpose * R‖ = ‖(A.transpose * R).transpose‖ :=
      (norm_transpose_real (A.transpose * R)).symm
    _ = ‖R * A‖ := by rw [ht]
    _ = ‖R * A * P‖ := by
      rw [rowProjection_AUpStack_input (m := m) F k]
    _ = ‖R * (A * P)‖ := by rw [Matrix.mul_assoc]
    _ ≤ ‖R‖ * ‖A * P‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ‖A * P‖ := by
      exact mul_le_mul_of_nonneg_right (rowGradeProjection_norm_le_one (k + 1))
        (norm_nonneg _)
    _ ≤ 1 * Real.sqrt k := by
      exact mul_le_mul_of_nonneg_left
        (AUpStack_gradeProjection_norm (m := m) F k) zero_le_one
    _ = Real.sqrt k := one_mul _

/-- The lowering heavy band factors through its exact intermediate grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hminus_grade_factor_add_two (F : Frame n d) (k : ℕ) :
    Hminus m (frameRows F) * gradeProjection (d := d) (k + 2) =
      ((AUpStack (m := m) F).transpose *
        rowGradeProjection (m := m) (n := n) (k + 1)) *
      (ADownStack (m := m) F * gradeProjection (d := d) (k + 2)) := by
  rw [Hminus_eq_AUpStackTranspose_mul_ADownStack]
  have hout := rowProjection_ADownStack_output (m := m) F (k + 1)
  have hout' :
      rowGradeProjection (m := m) (n := n) (k + 1) *
          ADownStack (m := m) F * gradeProjection (d := d) (k + 2) =
        ADownStack (m := m) F * gradeProjection (d := d) (k + 2) := by
    convert hout using 1
  calc
    ((AUpStack (m := m) F).transpose * ADownStack (m := m) F) *
        gradeProjection (d := d) (k + 2) =
      (AUpStack (m := m) F).transpose *
        (ADownStack (m := m) F * gradeProjection (d := d) (k + 2)) := by
      rw [Matrix.mul_assoc]
    _ = (AUpStack (m := m) F).transpose *
        (rowGradeProjection (m := m) (n := n) (k + 1) *
          ADownStack (m := m) F * gradeProjection (d := d) (k + 2)) := by
      rw [hout']
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The heavy lowering band vanishes on grade zero.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hminus_gradeProjection_zero (F : Frame n d) :
    Hminus m (frameRows F) * gradeProjection (d := d) 0 = 0 := by
  rw [Hminus_eq_AUpStackTranspose_mul_ADownStack, Matrix.mul_assoc,
    ADownStack_gradeProjection_zero, Matrix.mul_zero]

/-- The heavy lowering band vanishes on grade one.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hminus_gradeProjection_one (F : Frame n d) :
    Hminus m (frameRows F) * gradeProjection (d := d) 1 = 0 := by
  rw [Hminus_eq_AUpStackTranspose_mul_ADownStack]
  have hout := rowProjection_ADownStack_output (m := m) F 0
  have hout' :
      rowGradeProjection (m := m) (n := n) 0 * ADownStack (m := m) F *
          gradeProjection (d := d) 1 =
        ADownStack (m := m) F * gradeProjection (d := d) 1 := by
    convert hout using 1
  have hz : (AUpStack (m := m) F).transpose *
      rowGradeProjection (m := m) (n := n) 0 = 0 := by
    have h := congrArg Matrix.transpose (rowProjection_zero_AUpStack (m := m) F)
    simpa [Matrix.transpose_mul] using h
  calc
    ((AUpStack (m := m) F).transpose * ADownStack (m := m) F) *
        gradeProjection (d := d) 1 =
      (AUpStack (m := m) F).transpose *
        (ADownStack (m := m) F * gradeProjection (d := d) 1) := by
      rw [Matrix.mul_assoc]
    _ = (AUpStack (m := m) F).transpose *
        (rowGradeProjection (m := m) (n := n) 0 * ADownStack (m := m) F *
          gradeProjection (d := d) 1) := by rw [hout']
    _ = ((AUpStack (m := m) F).transpose *
        rowGradeProjection (m := m) (n := n) 0) *
          (ADownStack (m := m) F * gradeProjection (d := d) 1) := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hz, Matrix.zero_mul]

/-- Concrete heavy-heavy `-2` estimate in the uniform form used by the
component table.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hminus_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖Hminus m (frameRows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) + 1 := by
  rcases nu with (_ | _ | k)
  · rw [Hminus_gradeProjection_zero]
    norm_num
  · rw [Hminus_gradeProjection_one]
    norm_num
  · rw [Hminus_grade_factor_add_two]
    calc
      _ ≤
          ‖(AUpStack (m := m) F).transpose *
            rowGradeProjection (m := m) (n := n) (k + 1)‖ *
          ‖ADownStack (m := m) F * gradeProjection (d := d) (k + 2)‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ Real.sqrt k * Real.sqrt (k + 2) := by
        have hd := ADownStack_gradeProjection_norm (m := m) F (k + 2)
        have hd' :
            ‖ADownStack (m := m) F * gradeProjection (d := d) (k + 2)‖ ≤
              Real.sqrt ((k : ℝ) + 2) := by
          (convert hd using 1; norm_num)
        exact mul_le_mul
          (AUpStackTranspose_rowGradeProjection_norm (m := m) F k)
          hd'
          (norm_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ (k : ℝ) + 1 := by
        simpa [mul_comm] using sqrt_mul_sqrt_add_two_le k
      _ ≤ ((k + 2 : ℕ) : ℝ) + 1 := by norm_num

end

end NLAlib.SparseFock.HeavyBandsConcrete
