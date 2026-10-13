import NLAlib.Matrix.Structured.Measurable
import Mathlib.Analysis.Matrix.Order

/-!
# A measurable polar frame for full-column-rank real matrices

The map `Y ↦ Y (sqrt(YᵀY))⁻¹` is entrywise measurable on all inputs. On matrices whose
column Gram matrix is invertible, it is an orthonormal frame with exactly the same range.
Outside that full-column-rank set the definition remains measurable; orthonormality is
not asserted. Atlas: `gn-expected-error`.
-/

noncomputable section

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace NLAlib

/-- The polar frame candidate, defined on every real matrix. Orthogonality is asserted
only on full-column-rank inputs. Horn–Johnson, Matrix Analysis, §7.3;
atlas `gn-expected-error` (measurable frame constructor). -/
def polarFrame {m q : Type*} [Fintype m] [Fintype q] [DecidableEq q]
    (Y : Matrix m q ℝ) : Matrix m q ℝ := Y * (CFC.sqrt (Yᵀ * Y))⁻¹

private theorem gram_nonneg {m q : Type*} [Fintype m] [Fintype q]
    (Y : Matrix m q ℝ) : 0 ≤ Yᵀ * Y := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self Y).nonneg

private theorem sqrtGram_transpose {m q : Type*} [Fintype m] [Fintype q] [DecidableEq q]
    (Y : Matrix m q ℝ) : (CFC.sqrt (Yᵀ * Y))ᵀ = CFC.sqrt (Yᵀ * Y) := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (CFC.sqrt_nonneg (Yᵀ * Y)).star_eq

/-- The polar frame has orthonormal columns whenever the column Gram matrix is invertible.
The statement includes an empty column index. Horn–Johnson §7.3;
atlas `gn-expected-error`. -/
theorem hasOrthonormalCols_polarFrame {m q : Type*} [Fintype m] [Fintype q]
    [DecidableEq q] (Y : Matrix m q ℝ) (hY : IsUnit (Yᵀ * Y)) :
    HasOrthonormalCols (polarFrame Y) := by
  let S := CFC.sqrt (Yᵀ * Y)
  have hS : IsUnit S := (CFC.isUnit_sqrt_iff _ (gram_nonneg Y)).2 hY
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hSl : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSd
  have hSr : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSd
  have hSq : S * S = Yᵀ * Y := CFC.sqrt_mul_sqrt_self _ (gram_nonneg Y)
  have hSt : Sᵀ = S := sqrtGram_transpose Y
  have hSit : S⁻¹ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSt]
  change (Y * S⁻¹)ᵀ * (Y * S⁻¹) = 1
  rw [Matrix.transpose_mul, hSit]
  calc
    S⁻¹ * Yᵀ * (Y * S⁻¹) = S⁻¹ * (Yᵀ * Y) * S⁻¹ := by simp only [Matrix.mul_assoc]
    _ = S⁻¹ * (S * S) * S⁻¹ := by rw [hSq]
    _ = (S⁻¹ * S) * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hSl, hSr]; simp

/-- The polar frame reproduces its input exactly under its orthogonal projector when
the column Gram matrix is invertible. Horn–Johnson §7.3; atlas `gn-expected-error`. -/
theorem polarFrame_mul_transpose_mul_eq {m q : Type*} [Fintype m] [Fintype q]
    [DecidableEq q] (Y : Matrix m q ℝ) (hY : IsUnit (Yᵀ * Y)) :
    polarFrame Y * ((polarFrame Y)ᵀ * Y) = Y := by
  let S := CFC.sqrt (Yᵀ * Y)
  have hS : IsUnit S := (CFC.isUnit_sqrt_iff _ (gram_nonneg Y)).2 hY
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hSl : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSd
  have hSq : S * S = Yᵀ * Y := CFC.sqrt_mul_sqrt_self _ (gram_nonneg Y)
  have hSt : Sᵀ = S := sqrtGram_transpose Y
  have hSit : S⁻¹ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSt]
  change (Y * S⁻¹) * ((Y * S⁻¹)ᵀ * Y) = Y
  rw [Matrix.transpose_mul, hSit]
  calc
    (Y * S⁻¹) * (S⁻¹ * Yᵀ * Y) = Y * S⁻¹ * S⁻¹ * (Yᵀ * Y) := by
      simp only [Matrix.mul_assoc]
    _ = Y * S⁻¹ * S⁻¹ * (S * S) := by rw [hSq]
    _ = Y * S⁻¹ * (S⁻¹ * S) * S := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [hSl]; simp only [Matrix.mul_one, hSl, Matrix.mul_assoc, Matrix.mul_one]

/-- The polar frame map is entrywise measurable on all real matrices, so it defines a
valid random frame without any measurability certificate from the caller.
Horn–Johnson §7.3; atlas `gn-expected-error`. -/
theorem measurable_polarFrame_entry {m q : Type*} [Fintype m] [Fintype q] [DecidableEq q]
    (i : m) (j : q) : Measurable fun Y : Matrix m q ℝ => polarFrame Y i j := by
  have hcGram : Continuous fun Y : Matrix m q ℝ => Yᵀ * Y :=
    continuous_id.matrix_transpose.matrix_mul continuous_id
  have hcS : Continuous fun Y : Matrix m q ℝ => CFC.sqrt (Yᵀ * Y) :=
    CFC.continuousOn_sqrt.comp_continuous hcGram (fun Y => gram_nonneg Y)
  have hS : ∀ a b, Measurable fun Y : Matrix m q ℝ => CFC.sqrt (Yᵀ * Y) a b :=
    fun a b => (hcS.matrix_elem a b).measurable
  have hInv := measurable_inv_entry_of hS
  exact measurable_mul_entry_of (Matrix.measurable_iff_entries.mp measurable_id) hInv i j

end NLAlib
