import NLAlib.Matrix.Factorizations.ComplexCholeskyPivot
import NLAlib.Matrix.Functions.RealComplexCFC
/-!
# Cholesky trailing Schur residual

The trailing block after the first scalar pivot is PSD even when the pivot
vanishes. Reuse the existing coordinate-pivot proof through complexification.
Source: Higham, Theorem 10.1; supports `cholesky-decomposition`.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

/-- The trailing Schur residual after the first Cholesky pivot, with total
inverse at a zero pivot. Higham, Theorem 10.1; supports `cholesky-decomposition`. -/
def choleskyTrailingResidual {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  A i.succ j.succ - A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ

/-- The trailing residual is PSD at positive and zero pivots.
Higham, Theorem 10.1; supports `cholesky-decomposition`. -/
theorem posSemidef_choleskyTrailingResidual {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.PosSemidef) :
    (choleskyTrailingResidual A).PosSemidef := by
  have hAc := (posSemidef_realMatrixComplexification_iff A).mpr hA
  have hR := (posSemidef_complexCholeskyResidualStep hAc 0).submatrix Fin.succ
  apply (posSemidef_realMatrixComplexification_iff (choleskyTrailingResidual A)).mp
  convert hR using 1
  ext i j
  simp [realMatrixComplexification_apply, choleskyTrailingResidual,
    Matrix.submatrix, complexCholeskyResidualStep_apply]

end NLAlib
