import NLAlib.Matrix.Spectral.Complexification

/-! # Units under real matrix scalar extension -/
noncomputable section
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real square matrix is invertible exactly when its complexification is.
The reflection uses the actual determinant, including dimension zero. -/
theorem isUnit_realMatrixComplexification_iff (A : Matrix n n ℝ) :
    IsUnit (realMatrixComplexification A : Matrix n n ℂ) ↔ IsUnit A := by
  constructor
  · intro hA
    apply (Matrix.isUnit_iff_isUnit_det A).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hn := (Matrix.isUnit_iff_isUnit_det _).mp hA
    apply (isUnit_iff_ne_zero.mp hn)
    have hd := (algebraMap ℝ ℂ).map_det A
    rw [hz, map_zero] at hd
    exact hd.symm
  · intro hA
    exact hA.map realMatrixComplexification

end NLAlib
