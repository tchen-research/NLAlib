import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import NLAlib.Matrix.Spectral.SpectralBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order

/-! # Spectral norm bounds from the Loewner order

The positive Gram matrix translates finite matrix order bounds to named
spectral norms. Largest-eigenvalue bounds do not require positivity of the
matrix whose quadratic form is being bounded.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A PSD matrix has spectral norm at most a nonnegative scalar precisely
when it lies below that scalar times the identity. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_iff {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {r : ℝ} (hr : 0 ≤ r) :
    specNorm A ≤ r ↔ A ≤ r • (1 : Matrix n n ℂ) := by
  simpa only [specNorm_eq_norm, Algebra.algebraMap_eq_smul_one] using
    CStarAlgebra.norm_le_iff_le_algebraMap A hr hA.nonneg

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian matrix lies below its spectral norm times the identity. -/
theorem _root_.Matrix.IsHermitian.le_specNorm_smul_one {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : A ≤ specNorm A • (1 : Matrix n n ℂ) := by
  simpa only [specNorm_eq_norm, Algebra.algebraMap_eq_smul_one] using
    hA.isSelfAdjoint.le_algebraMap_norm_self

open scoped Matrix.Norms.L2Operator in
/-- A Hermitian matrix lies below its largest eigenvalue times the identity.
The largest eigenvalue is used, rather than the largest absolute eigenvalue. -/
theorem _root_.Matrix.IsHermitian.le_lambdaMax_smul_one {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : A ≤ lambdaMax A • (1 : Matrix n n ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  apply le_algebraMap_of_spectrum_le (a := A)
  intro x hx
  exact le_csSup (by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).bddAbove) hx

/-- A rectangular Gram domination bounds the squared spectral norm, including
empty index sets and a zero upper bound. -/
theorem specNorm_sq_le_of_conjTranspose_mul_self_le (A : Matrix m n ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hA : Aᴴ * A ≤ r • (1 : Matrix n n ℂ)) :
    specNorm A ^ 2 ≤ r := by
  rw [specNorm_sq_eq_specNorm_conjTranspose_mul_self]
  exact (Matrix.posSemidef_conjTranspose_mul_self A).specNorm_le_iff hr |>.mpr hA

end NLAlib
