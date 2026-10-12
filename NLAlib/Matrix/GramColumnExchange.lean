import NLAlib.Matrix.DeterminantDiagonalUpdate
import NLAlib.Matrix.GramColumnDeterminant

/-!
# Exact maximum-volume column exchange identity

Replacing one selected column by a range component plus an orthogonal residual
changes its squared volume by an exact interpolation/cofactor formula.
Gu–Eisenstat 1996, Theorem 3.2; derivations §alg:rrqr.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- The exact one-column Gram-volume exchange identity. Here `C t` is the
component in the selected column range and `d` is perpendicular to that range.
The inverse-Gram diagonal is the squared norm of the corresponding inverse
triangular-factor row in QR coordinates. No approximation or relaxed constant
is used. Gu–Eisenstat 1996, Theorem 3.2; derivations equation alg:swap.
Supports `rank-revealing-qr`. -/
theorem det_gram_updateCol_eq_det_mul {m p : Type*}
    [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
    (C : Matrix m p ℝ) (hC : IsUnit (Cᵀ * C).det) (i : p) (t : p → ℝ) (d : m → ℝ)
    (hd : Cᵀ *ᵥ d = 0) :
    ((C.updateCol i (C *ᵥ t + d))ᵀ * C.updateCol i (C *ᵥ t + d)).det =
      (Cᵀ * C).det * (t i ^ 2 + (d ⬝ᵥ d) * (Cᵀ * C)⁻¹ i i) := by
  let K := (1 : Matrix p p ℝ).updateCol i t
  let M := C * K
  let R := (0 : Matrix m p ℝ).updateCol i d
  have hM : M = C.updateCol i (C *ᵥ t) := by
    simp only [M, K, Matrix.mul_updateCol, Matrix.mul_one]
  have hUpdate : C.updateCol i (C *ᵥ t + d) = M + R := by
    rw [hM]
    ext a b
    by_cases hb : b = i
    · subst b
      simp [R]
    · simp [R, Matrix.updateCol_ne hb]
  have hCR : Cᵀ * R = 0 := by
    simp only [R, Matrix.mul_updateCol, Matrix.mul_zero, hd, Matrix.updateCol_zero_zero]
  have hMR : Mᵀ * R = 0 := by
    rw [show Mᵀ = Kᵀ * Cᵀ from Matrix.transpose_mul C K,
      Matrix.mul_assoc, hCR, Matrix.mul_zero]
  have hRM : Rᵀ * M = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using
      congrArg Matrix.transpose hMR
  have hRR : Rᵀ * R = Matrix.single i i (d ⬝ᵥ d) := by
    change ((0 : Matrix m p ℝ).updateCol i d)ᵀ * (0 : Matrix m p ℝ).updateCol i d = _
    rw [← Matrix.updateRow_transpose, Matrix.transpose_zero,
      Matrix.updateRow_zero_mul_updateCol_zero]
  have hGram : (M + R)ᵀ * (M + R) = Mᵀ * M + Matrix.single i i (d ⬝ᵥ d) := by
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      hMR, hRM, hRR, add_zero, zero_add]
  have hMinor : ((Mᵀ * M).updateCol i (Pi.single i 1)).det =
      ((Cᵀ * C).updateCol i (Pi.single i 1)).det := by
    apply det_updateCol_single_eq_of_complement_eq
    intro a b ha hb
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hM, Matrix.updateCol_ne ha, Matrix.updateCol_ne hb]
  have hKdet : K.det = t i := by
    change ((1 : Matrix p p ℝ).updateCol i t).det = t i
    rw [← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  have hMdet : (Mᵀ * M).det = (Cᵀ * C).det * t i ^ 2 := by
    have heq : Mᵀ * M = Kᵀ * (Cᵀ * C) * K := by
      simp only [M, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [heq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hKdet]
    ring
  rw [hUpdate, hGram, det_add_single_diagonal, hMinor,
    det_updateCol_single_eq_det_mul_inv _ hC, hMdet]
  ring

end NLAlib
