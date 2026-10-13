/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.Heavy.OccupationIdentity
import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Sketching.Sparse.MomentMethod.GramTail
set_option autoImplicit false

/-!
# Restricted heavy preserving operator bound

Explicit quadratic forms prove the sharp exact-grade preserving-band norm estimate.
Ported from `SparseFockFormal.HeavyBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch.Heavy

open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- A real Gram quadratic form equals the squared coordinate energy of its matrix action.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_gram
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (A : Matrix I J ℝ) (x : J → ℝ) :
    quadForm (A.transpose * A) x =
      sumSq (Matrix.mulVec A x) := by
  rw [quadForm_transpose_mul_self, sumSq_eq_dotProduct]

/-- The creation diagonal quadratic form is the sum of same-site creation-analysis energies.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_DUp (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    quadForm (DUp (m := m) F) x =
      ∑ r, ∑ i, sumSq (Matrix.mulVec (AUpOne F r i) x) := by
  calc
    quadForm (DUp (m := m) F) x =
        ∑ r, ∑ i,
          quadForm ((AUpOne F r i).transpose * AUpOne F r i) x := by
      simp only [quadForm, DUp, Matrix.sum_mulVec, dotProduct_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      rw [quadratic_gram]

/-- The annihilation diagonal quadratic form is the sum of same-site annihilation-analysis energies.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_DDown (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    quadForm (DDown (m := m) F) x =
      ∑ r, ∑ i, sumSq (Matrix.mulVec (ADownOne F r i) x) := by
  calc
    quadForm (DDown (m := m) F) x =
        ∑ r, ∑ i,
          quadForm ((ADownOne F r i).transpose * ADownOne F r i) x := by
      simp only [quadForm, DDown, Matrix.sum_mulVec, dotProduct_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      rw [quadratic_gram]

/-- The preserving heavy quadratic form is its two analysis energies minus the diagonal corrections.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_Hzero (F : Frame n d)
    (x : Fin d × Pattern m n → ℝ) :
    quadForm (Hzero m (Frame.rows F)) x =
      sumSq (Matrix.mulVec (AUpStack (m := m) F) x) +
      sumSq (Matrix.mulVec (ADownStack (m := m) F) x) -
      (quadForm (DUp (m := m) F) x + quadForm (DDown (m := m) F) x) := by
  rw [Hzero_gram_sub_diagonal]
  calc
    quadForm
          ((AUpStack (m := m) F).transpose * AUpStack F +
            (ADownStack (m := m) F).transpose * ADownStack F -
            (DUp F + DDown F)) x =
        quadForm
            ((AUpStack (m := m) F).transpose * AUpStack F +
              (ADownStack (m := m) F).transpose * ADownStack F) x -
          quadForm (DUp F + DDown F) x := by
      simp [quadForm, Matrix.add_mulVec, Matrix.sub_mulVec,
        dotProduct_add, dotProduct_sub]
    _ =
        (quadForm ((AUpStack (m := m) F).transpose * AUpStack F) x +
          quadForm ((ADownStack (m := m) F).transpose * ADownStack F) x) -
        (quadForm (DUp F) x + quadForm (DDown F) x) := by
      simp [quadForm, Matrix.add_mulVec, dotProduct_add]
    _ = _ := by
      rw [quadratic_gram, quadratic_gram]

/-- Conjugating by the grade projection evaluates the quadratic form on the projected vector.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem quadratic_gradeConj (M : FullOp d m n) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    quadForm (gradeProjection (d := d) nu * M * gradeProjection nu) x =
      quadForm M (Matrix.mulVec (gradeProjection (d := d) nu) x) := by
  have h := quadForm_transpose_mul_mul M
    (gradeProjection (d := d) (m := m) (n := n) nu) x
  rwa [gradeProjection_transpose] at h

/-- The grade-preserving heavy band is symmetric.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_transpose (F : Frame n d) :
    (Hzero m (Frame.rows F)).transpose = Hzero m (Frame.rows F) := by
  unfold Hzero wordSum
  rw [Matrix.transpose_add,
    Directional.transpose_physicalWordSum,
    Directional.transpose_physicalWordSum]
  rfl

/-- The heavy preserving band has grade shift zero.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_homogeneous (F : Frame n d) :
    IsFullGradeShift 0 (Hzero m (Frame.rows F)) := by
  apply homogeneous_add
  · simpa [Hzero, wordSum, Word.degree, Leg.degree] using
      Directional.physicalWordSum_homogeneous
        (m := m) (Frame.rows F) (.rUp, .rDown)
  · simpa [Hzero, wordSum, Word.degree, Leg.degree] using
      Directional.physicalWordSum_homogeneous
        (m := m) (Frame.rows F) (.rDown, .rUp)

/-- The grade-zero heavy band preserves every exact-grade subspace.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_grade_factor (F : Frame n d) (nu : ℕ) :
    gradeProjection (d := d) nu * Hzero m (Frame.rows F) * gradeProjection nu =
      Hzero m (Frame.rows F) * gradeProjection nu := by
  apply output_projection_of_homogeneous
    (Hzero_homogeneous (m := m) F) nu nu
  norm_num

/-- Sharp quadratic-form estimate for the concrete grade-zero heavy band,
after restriction to one exact total grade.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_gradeConj_quadratic_abs_le (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    |quadForm
      (gradeProjection (d := d) nu * Hzero m (Frame.rows F) *
        gradeProjection nu) x| ≤
      2 * (nu : ℝ) * sumSq x := by
  let P := gradeProjection (d := d) (m := m) (n := n) nu
  let y := Matrix.mulVec P x
  have hUp :
      sumSq (Matrix.mulVec (AUpStack (m := m) F) y) ≤
        (nu : ℝ) * sumSq x := by
    rw [coordNormSq_AUpStack]
    simpa only [P, y] using
      AUp_grade_energy (m := m) F nu x
  have hDown :
      sumSq (Matrix.mulVec (ADownStack (m := m) F) y) ≤
        (nu : ℝ) * sumSq x := by
    rw [coordNormSq_ADownStack]
    simpa only [P, y] using
      ADown_grade_energy (m := m) F nu x
  have hDiag :
      quadForm (DUp (m := m) F) y + quadForm (DDown (m := m) F) y ≤
        (nu : ℝ) * sumSq x := by
    calc
      quadForm (DUp (m := m) F) y + quadForm (DDown (m := m) F) y =
          (∑ r, ∑ i, sumSq (Matrix.mulVec (AUpOne F r i) y)) +
          (∑ r, ∑ i, sumSq (Matrix.mulVec (ADownOne F r i) y)) := by
        rw [quadratic_DUp, quadratic_DDown]
      _ ≤ ∑ p, (p.grade : ℝ) * euclideanNormSq (Directional.fiber y p) :=
        Dcombined_energy_le_weighted F y
      _ = (nu : ℝ) * sumSq y := by
        simpa [P, y] using weighted_gradeProjection (d := d) (m := m) (n := n) nu x
      _ ≤ (nu : ℝ) * sumSq x := by
        exact mul_le_mul_of_nonneg_left
          (gradeProjection_normSq_le nu x) (Nat.cast_nonneg _)
  have hDiag0 :
      0 ≤ quadForm (DUp (m := m) F) y + quadForm (DDown (m := m) F) y := by
    rw [quadratic_DUp, quadratic_DDown]
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ sumSq_nonneg _)
      (Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ sumSq_nonneg _)
  have hUp0 :
      0 ≤ sumSq (Matrix.mulVec (AUpStack (m := m) F) y) :=
    sumSq_nonneg _
  have hDown0 :
      0 ≤ sumSq (Matrix.mulVec (ADownStack (m := m) F) y) :=
    sumSq_nonneg _
  have hNorm0 : 0 ≤ sumSq x := sumSq_nonneg x
  have hNu0 : 0 ≤ (nu : ℝ) := Nat.cast_nonneg _
  rw [quadratic_gradeConj, quadratic_Hzero, abs_le]
  change
    -(2 * (nu : ℝ) * sumSq x) ≤
          sumSq (Matrix.mulVec (AUpStack (m := m) F) y) +
            sumSq (Matrix.mulVec (ADownStack (m := m) F) y) -
            (quadForm (DUp (m := m) F) y + quadForm (DDown (m := m) F) y) ∧
      sumSq (Matrix.mulVec (AUpStack (m := m) F) y) +
            sumSq (Matrix.mulVec (ADownStack (m := m) F) y) -
            (quadForm (DUp (m := m) F) y + quadForm (DDown (m := m) F) y) ≤
        2 * (nu : ℝ) * sumSq x
  constructor <;> nlinarith

/-- Restricting the preserving heavy band to one grade gives a Hermitian matrix.
Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_gradeConj_isHermitian (F : Frame n d) (nu : ℕ) :
    (gradeProjection (d := d) nu * Hzero m (Frame.rows F) *
      gradeProjection nu).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, gradeProjection_transpose,
    Hzero_transpose, Matrix.mul_assoc]

/-- Concrete heavy-heavy grade-zero component estimate required by the
component table.

Source: ported from `SparseFockFormal.HeavyBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem Hzero_gradeProjection_norm (F : Frame n d) (nu : ℕ) :
    ‖Hzero m (Frame.rows F) * gradeProjection (d := d) nu‖ ≤
      2 * (nu : ℝ) := by
  rw [← Hzero_grade_factor]
  apply (specNorm_le_iff_abs_dotProduct_mulVec_le _
    (Hzero_gradeConj_isHermitian (m := m) F nu) (2 * (nu : ℝ)) (by positivity)).2
  intro x
  have h := Hzero_gradeConj_quadratic_abs_le (m := m) F nu x
  rwa [sumSq_eq_dotProduct] at h

end

end NLAlib.SparseSketch.Heavy
