import NLAlib.Matrix.Structured.JacobiBorders
import NLAlib.Matrix.Functions.HermitianCalculus

/-! # Actual Radau borders from scalar Schur complements

The left and right endpoint corners are computed from inverses of the positive
definite endpoint shifts. The resulting actual matrices have the endpoint eigenvalue
and bracket the original symmetric border in the matrix order.
-/

noncomputable section
open Matrix Finset
open scoped Matrix MatrixOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The left Radau Schur corner; the endpoint shift must be invertible when applying
the spectral and positivity theorems. Source: focused reroutes, Section 3 (BL4). -/
def leftRadauCorner (J : Matrix n n ℝ) (v : n → ℝ) (a : ℝ) : ℝ :=
  a + quadForm (J - a • 1)⁻¹ v

/-- The right Radau Schur corner. Source: focused reroutes, Section 3 (BL4). -/
def rightRadauCorner (J : Matrix n n ℝ) (v : n → ℝ) (c : ℝ) : ℝ :=
  c - quadForm (c • 1 - J)⁻¹ v

/-- Finite real matrices with a singular endpoint shift have that endpoint in their
real algebraic spectrum, including arbitrary finite index types. -/
theorem mem_spectrum_of_det_sub_smul_one_eq_zero {A : Matrix n n ℝ} {a : ℝ}
    (h : (A - a • 1).det = 0) : a ∈ spectrum ℝ A := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have heq : algebraMap ℝ (Matrix n n ℝ) a - A = -(A - a • 1) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact neg_sub _ _ |>.symm
  rw [heq, Matrix.det_neg, h, mul_zero]
  simp

omit [DecidableEq n] in
/-- Increasing only the actual scalar border corner increases its matrix order. -/
theorem symmetricBorder_le_symmetricBorder (J : Matrix n n ℝ) (v : n → ℝ)
    {d e : ℝ} (hde : d ≤ e) : symmetricBorder J v d ≤ symmetricBorder J v e := by
  rw [Matrix.le_iff]
  have heq : symmetricBorder J v e - symmetricBorder J v d =
      fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal (fun _ : Fin 1 => e - d)) := by
    ext (i | i) (j | j)
    · simp [symmetricBorder]
    · simp [symmetricBorder]
    · simp [symmetricBorder]
    · simp [symmetricBorder, Subsingleton.elim i j]
  rw [heq]
  apply posSemidef_fromBlocks_diag Matrix.PosSemidef.zero
  rw [posSemidef_diagonal_iff]
  exact fun _ => sub_nonneg.mpr hde

/-- The actual left Radau border has the left endpoint eigenvalue and a PSD left
endpoint shift. Source: focused mathematical reroutes, Section 3 (BL4).
atlas: gauss-radau-lobatto (partial) -/
theorem leftRadauBorder_posSemidef_shift_and_mem_spectrum
    (J : Matrix n n ℝ) (v : n → ℝ) (a : ℝ) (hJ : (J - a • 1).PosDef) :
    (symmetricBorder J v (leftRadauCorner J v a) - a • 1).PosSemidef ∧
      a ∈ spectrum ℝ (symmetricBorder J v (leftRadauCorner J v a)) := by
  have h := posSemidef_and_det_eq_zero_symmetricBorder_of_schur_zero hJ v
  have heq : symmetricBorder J v (leftRadauCorner J v a) - a • 1 =
      symmetricBorder (J - a • 1) v (quadForm (J - a • 1)⁻¹ v) := by
    rw [symmetricBorder_sub_smul_one, leftRadauCorner, add_sub_cancel_left]
  rw [← heq] at h
  exact ⟨h.1, mem_spectrum_of_det_sub_smul_one_eq_zero h.2⟩

/-- The actual right Radau border has the right endpoint eigenvalue and a PSD right
endpoint shift. Source: focused mathematical reroutes, Section 3 (BL4).
atlas: gauss-radau-lobatto (partial) -/
theorem rightRadauBorder_posSemidef_shift_and_mem_spectrum
    (J : Matrix n n ℝ) (v : n → ℝ) (c : ℝ) (hJ : (c • 1 - J).PosDef) :
    (c • 1 - symmetricBorder J v (rightRadauCorner J v c)).PosSemidef ∧
      c ∈ spectrum ℝ (symmetricBorder J v (rightRadauCorner J v c)) := by
  have h := posSemidef_and_det_eq_zero_symmetricBorder_of_schur_zero hJ (-v)
  have hv : quadForm (c • 1 - J)⁻¹ (-v) = quadForm (c • 1 - J)⁻¹ v := by
    simpa using quadForm_smul (c • 1 - J)⁻¹ (-1 : ℝ) v
  have heq : c • 1 - symmetricBorder J v (rightRadauCorner J v c) =
      symmetricBorder (c • 1 - J) (-v) (quadForm (c • 1 - J)⁻¹ (-v)) := by
    rw [smul_one_sub_symmetricBorder, rightRadauCorner, sub_sub_cancel, hv]
  rw [← heq] at h
  refine ⟨h.1, mem_spectrum_of_det_sub_smul_one_eq_zero ?_⟩
  rw [← neg_sub, Matrix.det_neg, h.2, mul_zero]

/-- The actual left/right Radau borders bracket the original border in matrix order.
The leading endpoint shifts are positive definite; the original border endpoint
shifts need only be PSD. Source: focused reroutes, Section 3 (BL4).
atlas: gauss-radau-lobatto (partial) -/
theorem leftRadauBorder_le_original_le_rightRadauBorder
    (J : Matrix n n ℝ) (v : n → ℝ) (d a c : ℝ)
    (hJa : (J - a • 1).PosDef) (hJc : (c • 1 - J).PosDef)
    (hMa : (symmetricBorder J v d - a • 1).PosSemidef)
    (hMc : (c • 1 - symmetricBorder J v d).PosSemidef) :
    a • 1 ≤ symmetricBorder J v (leftRadauCorner J v a) ∧
      symmetricBorder J v (leftRadauCorner J v a) ≤ symmetricBorder J v d ∧
      symmetricBorder J v d ≤ symmetricBorder J v (rightRadauCorner J v c) ∧
      symmetricBorder J v (rightRadauCorner J v c) ≤ c • 1 := by
  have hda : leftRadauCorner J v a ≤ d := by
    rw [symmetricBorder_sub_smul_one] at hMa
    have h := (posSemidef_symmetricBorder_iff hJa v (d - a)).mp hMa
    dsimp only [leftRadauCorner]
    linarith
  have hdc : d ≤ rightRadauCorner J v c := by
    rw [smul_one_sub_symmetricBorder] at hMc
    have h := (posSemidef_symmetricBorder_iff hJc (-v) (c - d)).mp hMc
    have hv : quadForm (c • 1 - J)⁻¹ (-v) = quadForm (c • 1 - J)⁻¹ v := by
      simpa using quadForm_smul (c • 1 - J)⁻¹ (-1 : ℝ) v
    rw [hv] at h
    dsimp only [rightRadauCorner]
    linarith
  exact ⟨(Matrix.le_iff).mpr (leftRadauBorder_posSemidef_shift_and_mem_spectrum J v a hJa).1,
    symmetricBorder_le_symmetricBorder J v hda,
    symmetricBorder_le_symmetricBorder J v hdc,
    (Matrix.le_iff).mpr (rightRadauBorder_posSemidef_shift_and_mem_spectrum J v c hJc).1⟩

end NLAlib
