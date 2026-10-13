/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.Heavy.GradeProjections

/-!
# Restricted heavy raising operator bound

Coordinate energy converts to the exact-grade raising-band norm bound.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch.Heavy

open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Creation block-column energy is the sum of physical-row creation energies.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordNormSq_AUpStack (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    sumSq (Matrix.mulVec (AUpStack F) x) =
      ∑ r, sumSq (Matrix.mulVec (AUpMatrix F r) x) := by
  simp only [sumSq, sumSq, AUpStack, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]

/-- Annihilation block-column energy is the sum of physical-row annihilation energies.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem coordNormSq_ADownStack (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    sumSq (Matrix.mulVec (ADownStack F) x) =
      ∑ r, sumSq (Matrix.mulVec (ADownMatrix F r) x) := by
  simp only [sumSq, sumSq, ADownStack, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]

/-- Operator form of the first heavy-leg Loewner/energy estimate.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem AUpStack_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖AUpStack (m := m) F * gradeProjection (d := d) (m := m) nu‖ ≤
      Real.sqrt nu := by
  apply norm_le_of_normSq_mulVec_le (Real.sqrt_nonneg _)
  intro x
  rw [← Matrix.mulVec_mulVec, coordNormSq_AUpStack]
  calc
    _ ≤ (nu : ℝ) * sumSq x := AUp_grade_energy F nu x
    _ = (Real.sqrt nu) ^ 2 * sumSq x := by
      rw [Real.sq_sqrt (Nat.cast_nonneg nu)]

/-- Operator form of the second heavy-leg Loewner/energy estimate.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem ADownStack_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖ADownStack (m := m) F * gradeProjection (d := d) (m := m) nu‖ ≤
      Real.sqrt nu := by
  apply norm_le_of_normSq_mulVec_le (Real.sqrt_nonneg _)
  intro x
  rw [← Matrix.mulVec_mulVec, coordNormSq_ADownStack]
  calc
    _ ≤ (nu : ℝ) * sumSq x := ADown_grade_energy F nu x
    _ = (Real.sqrt nu) ^ 2 * sumSq x := by
      rw [Real.sq_sqrt (Nat.cast_nonneg nu)]

/-- The transpose of a heavy synthesis row is the matching annihilation analysis column.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
@[simp] theorem BUpMatrix_transpose (F : Frame n d) (r : Fin m) :
    (BUpMatrix F r).transpose = ADownMatrix F r := by
  ext σ inp
  simp only [BUpMatrix, ADownMatrix, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have h := congrArg (fun K : FockOp m n ↦ K σ inp.2) (rUpAt_transpose r i)
  simpa [Matrix.transpose_apply] using h

/-- The row synthesis factor, restricted to middle grade `mu`, has norm at
most `√(mu+1)`.  This is the concrete `B_r B_r†` estimate.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem BUpStack_rowGradeProjection_norm (F : Frame n d) (mu : ℕ) :
    ‖BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) mu‖ ≤
      Real.sqrt (mu + 1) := by
  let B := BUpStack (m := m) F
  let R := rowGradeProjection (m := m) (n := n) mu
  let A := ADownStack (m := m) F
  let P := gradeProjection (d := d) (m := m) (n := n) (mu + 1)
  have ht : (B * R).transpose = R * A := by
    simp [B, R, A, Matrix.transpose_mul]
  calc
    ‖B * R‖ = ‖(B * R).transpose‖ := (specNorm_transpose (B * R)).symm
    _ = ‖R * A‖ := by rw [ht]
    _ = ‖R * A * P‖ := by
      rw [rowProjection_ADownStack_input (m := m) F mu]
    _ = ‖R * (A * P)‖ := by rw [Matrix.mul_assoc]
    _ ≤ ‖R‖ * ‖A * P‖ := Matrix.l2_opNorm_mul R (A * P)
    _ ≤ 1 * ‖A * P‖ := by
      exact mul_le_mul_of_nonneg_right (rowGradeProjection_norm_le_one mu)
        (norm_nonneg _)
    _ ≤ 1 * Real.sqrt (mu + 1) := by
      have ha := ADownStack_gradeProjection_norm (m := m) F (mu + 1)
      have ha' : ‖A * P‖ ≤ Real.sqrt ((mu : ℝ) + 1) := by
        simpa [A, P, Nat.cast_add, Nat.cast_one] using ha
      exact mul_le_mul_of_nonneg_left ha' zero_le_one
    _ = Real.sqrt (mu + 1) := one_mul _

/-- The raising heavy band factors through the exact intermediate grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hplus_grade_factor (F : Frame n d) (nu : ℕ) :
    Hplus m (Frame.rows F) * gradeProjection (d := d) nu =
      (BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) (nu + 1)) *
        (AUpStack (m := m) F * gradeProjection (d := d) nu) := by
  rw [Hplus_eq_BUpStack_mul_AUpStack]
  have hins := rowProjection_AUpStack_gradeProjection (m := m) F nu
  calc
    (BUpStack (m := m) F * AUpStack (m := m) F) * gradeProjection (d := d) nu =
        BUpStack (m := m) F *
          (AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [Matrix.mul_assoc]
    _ = BUpStack (m := m) F *
        (rowGradeProjection (m := m) (n := n) (nu + 1) *
          AUpStack (m := m) F * gradeProjection (d := d) nu) := by
      rw [hins]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The square-root product of grades separated by two is bounded by the intervening grade.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem sqrt_mul_sqrt_add_two_le (nu : ℕ) :
    Real.sqrt (nu + 2) * Real.sqrt nu ≤ (nu : ℝ) + 1 := by
  have hnu : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
  have hnu2 : 0 ≤ (nu : ℝ) + 2 := by positivity
  have hs0 : 0 ≤ Real.sqrt ((nu : ℝ) + 2) * Real.sqrt (nu : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsquare :
      (Real.sqrt ((nu : ℝ) + 2) * Real.sqrt (nu : ℝ)) ^ 2 ≤
        ((nu : ℝ) + 1) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hnu2, Real.sq_sqrt hnu]
    nlinarith
  nlinarith [sq_nonneg
    (((nu : ℝ) + 1) + Real.sqrt ((nu : ℝ) + 2) * Real.sqrt (nu : ℝ))]

/-- Concrete heavy-heavy `+2` component estimate required by the component
table.  No abstract component-bound premise occurs in the statement.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hplus_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖Hplus m (Frame.rows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) + 1 := by
  rw [Hplus_grade_factor]
  calc
    _ ≤
        ‖BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) (nu + 1)‖ *
          ‖AUpStack (m := m) F * gradeProjection (d := d) nu‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ Real.sqrt ((nu : ℝ) + 2) * Real.sqrt nu := by
      have hb := BUpStack_rowGradeProjection_norm (m := m) F (nu + 1)
      have hb' :
          ‖BUpStack (m := m) F * rowGradeProjection (m := m) (n := n) (nu + 1)‖ ≤
            Real.sqrt ((nu : ℝ) + 2) := by
        (convert hb using 1; norm_num; ring)
      exact mul_le_mul hb' (AUpStack_gradeProjection_norm (m := m) F nu)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ (nu : ℝ) + 1 := sqrt_mul_sqrt_add_two_le nu

end

end NLAlib.SparseSketch.Heavy
