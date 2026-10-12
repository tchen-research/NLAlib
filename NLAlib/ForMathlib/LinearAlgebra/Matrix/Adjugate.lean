import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Cramer's rule at the leading entry

`inv_apply_zero_zero`: `(N⁻¹)₀₀ = det N_{[1:],[1:]} / det N` for a square matrix over a field
indexed by `Fin (m + 1)`, with no invertibility hypothesis. Mathlib has the adjugate expansion
`Matrix.adjugate_fin_succ_eq_det_submatrix` but no named form of this entry.
Helper for atlas `jacobi-matrix-identities`.
-/

open scoped Matrix

namespace NLAlib

/-- Cramer's rule at `(0, 0)`: `(N⁻¹)₀₀ = det N_{[1:],[1:]} / det N` (no hypothesis; both sides
vanish when `N` is singular). Stated over any field. Helper for `jacobi-matrix-identities`. -/
theorem inv_apply_zero_zero {K : Type*} [Field K] {m : ℕ}
    (N : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    N⁻¹ 0 0 = (N.submatrix Fin.succ Fin.succ).det / N.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix,
    Ring.inverse_eq_inv', smul_eq_mul]
  simp [div_eq_inv_mul]

end NLAlib
