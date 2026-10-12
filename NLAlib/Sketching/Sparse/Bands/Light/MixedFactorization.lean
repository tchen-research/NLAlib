/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.Bands.Light.PreservingDiagonal
set_option autoImplicit false

/-!
# Light synthesis and mixed row factors

Restricted light synthesis norms. The exact factorization of the mixed bands through
heavy analysis is in `MixedRowFactorization`.
Ported from `SparseFockFormal.LightBandsConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace NLAlib.SparseSketch.Light

open SparseSketch.Directional

noncomputable section

variable {d m n : ℕ}

/-- The transpose synthesis stack sends full grade `mu+1` exactly to row
grade `mu`.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem rowProjection_CStackTranspose_gradeProjection
    (F : Frame n d) (mu : ℕ) :
    Heavy.rowGradeProjection (m := m) (n := n) mu *
        (CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1) =
      (CStack (m := m) F).transpose *
        gradeProjection (d := d) (m := m) (n := n) (mu + 1) := by
  classical
  ext out inp
  simp only [Heavy.rowGradeProjection, gradeProjection,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hin : inp.2.grade = mu + 1
  · by_cases hentry : (CStack F).transpose out inp = 0
    · have hz : CStack F inp out = 0 := by
        simpa [Matrix.transpose_apply] using hentry
      simp [hin, hz]
    · have hentry' : CStack F inp out ≠ 0 := by
        simpa [Matrix.transpose_apply] using hentry
      have hrel := CMatrix_grade_relation F out.1 hentry'
      have hout : out.2.grade = mu := by
        rw [hin] at hrel
        push_cast at hrel
        have hz : (out.2.grade : ℤ) = (mu : ℤ) := by omega
        exact_mod_cast hz
      simp [hin, hout]
  · simp [hin]

/-- Exact cogram of the projected synthesis factor.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CStack_restricted_cogram (F : Frame n d) (mu : ℕ) :
    let P := gradeProjection (d := d) (m := m) (n := n) (mu + 1)
    let R := Heavy.rowGradeProjection (m := m) (n := n) mu
    let B := P * CStack (m := m) F * R
    B * B.transpose = P * ghat F * P := by
  dsimp
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Heavy.rowGradeProjection_transpose, gradeProjection_transpose]
  have hins := rowProjection_CStackTranspose_gradeProjection
    (m := m) F mu
  have hins' :
      Heavy.rowGradeProjection (m := m) (n := n) mu *
        ((CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1)) =
      (CStack (m := m) F).transpose *
        gradeProjection (d := d) (m := m) (n := n) (mu + 1) := by
    rw [← Matrix.mul_assoc, hins]
  calc
    (gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        Heavy.rowGradeProjection (m := m) (n := n) mu) *
      (Heavy.rowGradeProjection (m := m) (n := n) mu *
        ((CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1))) =
      (gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
          CStack (m := m) F *
        Heavy.rowGradeProjection (m := m) (n := n) mu) *
          ((CStack (m := m) F).transpose *
            gradeProjection (d := d) (m := m) (n := n) (mu + 1)) := by
      rw [hins']
    _ = gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
          (Heavy.rowGradeProjection (m := m) (n := n) mu *
            ((CStack (m := m) F).transpose *
              gradeProjection (d := d) (m := m) (n := n) (mu + 1))) := by
      simp only [Matrix.mul_assoc]
    _ = gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        ((CStack (m := m) F).transpose *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1)) := by
      rw [hins']
    _ = gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        (CStack (m := m) F * (CStack (m := m) F).transpose) *
          gradeProjection (d := d) (m := m) (n := n) (mu + 1) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [CStack_mul_transpose]

/-- Sharp restricted synthesis-stack bound.  The output projection is one
grade above the row input projection, exactly as required by the light and
mixed factorizations.

Source: ported from `SparseFockFormal.LightBandsConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem CStack_restricted_norm (F : Frame n d) (mu : ℕ) :
    ‖gradeProjection (d := d) (m := m) (n := n) (mu + 1) *
        CStack (m := m) F *
        Heavy.rowGradeProjection (m := m) (n := n) mu‖ ≤
      Real.sqrt ((d : ℝ) + (mu : ℝ)) := by
  let P := gradeProjection (d := d) (m := m) (n := n) (mu + 1)
  let R := Heavy.rowGradeProjection (m := m) (n := n) mu
  let B := P * CStack (m := m) F * R
  have hP : ‖P‖ ≤ 1 := gradeProjection_norm_le_one (mu + 1)
  have hG :
      ‖ghat (m := m) F * P‖ ≤ (d : ℝ) + (mu : ℝ) := by
    have hsharp := ghat_gradeProjection_norm_le
      (m := m) F (mu + 1) (Nat.succ_le_succ (Nat.zero_le mu))
    dsimp [P]
    (convert hsharp using 1; push_cast; ring)
  have hcogram : ‖B * B.transpose‖ ≤ (d : ℝ) + (mu : ℝ) := by
    rw [show B * B.transpose = P * ghat (m := m) F * P by
      simpa [B, P, R] using CStack_restricted_cogram (m := m) F mu]
    calc
      ‖P * ghat (m := m) F * P‖ ≤ ‖P‖ * ‖ghat (m := m) F * P‖ := by
        rw [Matrix.mul_assoc]
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ((d : ℝ) + (mu : ℝ)) := by
        exact mul_le_mul hP hG (norm_nonneg _) (by positivity)
      _ = (d : ℝ) + (mu : ℝ) := one_mul _
  have hBconj : B.transpose.conjTranspose = B := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hsquare : ‖B * B.transpose‖ = ‖B‖ * ‖B‖ := by
    calc
      ‖B * B.transpose‖ =
          ‖B.transpose.conjTranspose * B.transpose‖ := by rw [hBconj]
      _ = ‖B.transpose‖ * ‖B.transpose‖ :=
        Matrix.l2_opNorm_conjTranspose_mul_self B.transpose
      _ = ‖B‖ * ‖B‖ := by
        rw [show ‖B.transpose‖ = ‖B‖ from specNorm_transpose B]
  have hdm : 0 ≤ (d : ℝ) + (mu : ℝ) := by positivity
  have hsqrt := Real.sq_sqrt hdm
  change ‖B‖ ≤ Real.sqrt ((d : ℝ) + (mu : ℝ))
  rw [hsquare] at hcogram
  nlinarith [norm_nonneg B, Real.sqrt_nonneg ((d : ℝ) + (mu : ℝ))]

end

end NLAlib.SparseSketch.Light
