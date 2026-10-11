/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyRowFactorization

set_option autoImplicit false

/-!
# Heavy middle-grade projections

Exact middle-grade insertion and impossible-grade vanishing of the heavy analysis legs.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseFock.HeavyBandsConcrete

open ParsevalFrame LocalOperator FiniteOperator ExternalOperator GlobalBands BandInventory
  NamedBands FiniteHilbert TypedBlockCS ConcreteLadder
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Orthogonal projection on the middle row/Fock space; the row label does
not contribute to occupation grade.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
def rowGradeProjection (mu : ℕ) : Matrix (RowFock m n) (RowFock m n) ℝ :=
  Matrix.diagonal fun x ↦ if x.2.grade = mu then 1 else 0

/-- The exact middle-grade projection on the row-pattern space is symmetric.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem rowGradeProjection_transpose (mu : ℕ) :
    (rowGradeProjection (m := m) (n := n) mu).transpose = rowGradeProjection mu := by
  ext out inp
  by_cases h : out = inp
  · subst inp
    simp [rowGradeProjection, Matrix.transpose_apply]
  · have h' : inp ≠ out := Ne.symm h
    simp [rowGradeProjection, Matrix.transpose_apply, h, h']

/-- The exact middle-grade projection is an operator contraction.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowGradeProjection_norm_le_one (mu : ℕ) :
    ‖rowGradeProjection (m := m) (n := n) mu‖ ≤ 1 := by
  rw [rowGradeProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro x
  by_cases h : x.2.grade = mu <;> simp [h]

/-- Insertion of the exact middle grade after the `A_r` block column.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowProjection_AUpStack_gradeProjection (F : Frame n d) (nu : ℕ) :
    rowGradeProjection (m := m) (n := n) (nu + 1) * AUpStack (m := m) F *
        gradeProjection (d := d) nu =
      AUpStack (m := m) F * gradeProjection nu := by
  classical
  ext out inp
  simp only [rowGradeProjection, gradeProjection, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : AUpStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := AUpMatrix_grade_relation F out.1 hentry
      have hout : out.2.grade = nu + 1 := by
        rw [hin] at hrel
        exact_mod_cast hrel
      simp [hin, hout]
  · simp [hin]

/-- Selecting demotion output grade `mu` forces input grade `mu+1`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowProjection_ADownStack_input (F : Frame n d) (mu : ℕ) :
    rowGradeProjection (m := m) (n := n) mu * ADownStack (m := m) F *
        gradeProjection (d := d) (mu + 1) =
      rowGradeProjection mu * ADownStack (m := m) F := by
  classical
  ext out inp
  simp only [rowGradeProjection, gradeProjection, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hout : out.2.grade = mu
  · by_cases hentry : ADownStack F out inp = 0
    · simp [hout, hentry]
    · have hrel := ADownMatrix_grade_relation F out.1 hentry
      have hin : inp.2.grade = mu + 1 := by
        rw [hout] at hrel
        exact_mod_cast hrel.symm
      simp [hout, hin]
  · simp [hout]

/-- Conversely, fixing the output of an `A_r` leg at grade `k+1` forces its
input to have grade `k`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowProjection_AUpStack_input (F : Frame n d) (k : ℕ) :
    rowGradeProjection (m := m) (n := n) (k + 1) * AUpStack (m := m) F *
        gradeProjection (d := d) k =
      rowGradeProjection (k + 1) * AUpStack (m := m) F := by
  classical
  ext out inp
  simp only [rowGradeProjection, gradeProjection, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hout : out.2.grade = k + 1
  · by_cases hentry : AUpStack F out inp = 0
    · simp [hout, hentry]
    · have hrel := AUpMatrix_grade_relation F out.1 hentry
      have hin : inp.2.grade = k := by
        rw [hout] at hrel
        push_cast at hrel
        have hz : (inp.2.grade : ℤ) = (k : ℤ) := by omega
        exact_mod_cast hz
      simp [hout, hin]
  · simp [hout]

/-- An input of grade `mu+1` under the demotion analysis column lands exactly
in middle grade `mu`.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowProjection_ADownStack_output (F : Frame n d) (mu : ℕ) :
    rowGradeProjection (m := m) (n := n) mu * ADownStack (m := m) F *
        gradeProjection (d := d) (mu + 1) =
      ADownStack (m := m) F * gradeProjection (d := d) (mu + 1) := by
  classical
  ext out inp
  simp only [rowGradeProjection, gradeProjection, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = mu + 1
  · by_cases hentry : ADownStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := ADownMatrix_grade_relation F out.1 hentry
      have hout : out.2.grade = mu := by
        rw [hin] at hrel
        push_cast at hrel
        have hz : (out.2.grade : ℤ) = (mu : ℤ) := by omega
        exact_mod_cast hz
      simp [hin, hout]
  · simp [hin]

/-- Heavy creation analysis cannot produce a grade-zero middle state.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowProjection_zero_AUpStack (F : Frame n d) :
    rowGradeProjection (m := m) (n := n) 0 * AUpStack (m := m) F = 0 := by
  classical
  ext out inp
  simp only [rowGradeProjection, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hout : out.2.grade = 0
  · by_cases hentry : AUpStack F out inp = 0
    · simp [hout, hentry]
    · have hrel := AUpMatrix_grade_relation F out.1 hentry
      rw [hout] at hrel
      have : (0 : ℤ) < (inp.2.grade : ℤ) + 1 := by omega
      omega
  · simp [hout]

/-- Heavy annihilation analysis vanishes on grade-zero input.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownStack_gradeProjection_zero (F : Frame n d) :
    ADownStack (m := m) F * gradeProjection (d := d) (m := m) (n := n) 0 = 0 := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hin : inp.2.grade = 0
  · by_cases hentry : ADownStack F out inp = 0
    · simp [hin, hentry]
    · have hrel := ADownMatrix_grade_relation F out.1 hentry
      rw [hin] at hrel
      have : (0 : ℤ) ≤ (out.2.grade : ℤ) := by omega
      omega
  · simp [hin]

end

end NLAlib.SparseFock.HeavyBandsConcrete
