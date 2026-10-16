import NLAlib.Matrix.Functions.CFCTrace
import NLAlib.Matrix.Norms.Core
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Nonreal resolvents of Hermitian matrices

The native algebraic resolvent agrees with the total matrix inverse. Hermitian
spectral coordinates give invertibility and the sharp `1/|Im ζ|` spectral-norm
bound without any simple-spectrum or nonzero-eigenvalue assumptions.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's native resolvent is the inverse of the shifted matrix. -/
theorem resolvent_matrix_eq_inv (A : Matrix n n ℂ) (ζ : ℂ) :
    resolvent A ζ = (ζ • (1 : Matrix n n ℂ)-A)⁻¹ := by
  rw [resolvent,←Matrix.nonsing_inv_eq_ringInverse,Algebra.algebraMap_eq_smul_one]

private theorem shifted_hermitian_diagonalization {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (ζ : ℂ) :
    ζ • (1 : Matrix n n ℂ)-A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => ζ-(hA.eigenvalues i : ℂ))) := by
  have hd : Matrix.diagonal (fun i => ζ-(hA.eigenvalues i : ℂ)) =
      ζ • (1 : Matrix n n ℂ)-Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
  rw [hd,map_sub,map_smul,map_one,←hA.spectral_theorem]

private theorem shifted_eigenvalue_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) (i : n) : ζ-(hA.eigenvalues i : ℂ) ≠ 0 := by
  intro heq
  have hi := congrArg Complex.im heq
  exact hζ (by simpa using hi)

/-- A nonreal shift of a Hermitian matrix is invertible, including empty
matrix dimensions. -/
theorem _root_.Matrix.IsHermitian.isUnit_smul_one_sub_of_im_ne_zero {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    IsUnit (ζ • (1 : Matrix n n ℂ)-A) := by
  rw [shifted_hermitian_diagonalization hA]
  apply IsUnit.map _
  rw [Matrix.isUnit_diagonal,Pi.isUnit_iff]
  exact fun i => isUnit_iff_ne_zero.mpr (shifted_eigenvalue_ne_zero hA hζ i)

/-- A Hermitian resolvent is the unitary conjugate of its scalar resolvents. -/
theorem resolvent_eq_eigenvectorUnitary_conj_diagonal {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    resolvent A ζ = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => (ζ-(hA.eigenvalues i : ℂ))⁻¹)) := by
  rw [resolvent_matrix_eq_inv]
  apply Matrix.inv_eq_right_inv
  rw [shifted_hermitian_diagonalization hA,←map_mul]
  have hd : Matrix.diagonal (fun i => ζ-(hA.eigenvalues i : ℂ)) *
      Matrix.diagonal (fun i => (ζ-(hA.eigenvalues i : ℂ))⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [shifted_eigenvalue_ne_zero hA hζ]
  rw [hd,map_one]

/-- The spectral norm of a Hermitian matrix's nonreal resolvent is at most
`1/|Im ζ|`. The empty matrix has norm zero and is included. -/
theorem _root_.Matrix.IsHermitian.specNorm_resolvent_le {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    NLAlib.specNorm (resolvent A ζ) ≤ |ζ.im|⁻¹ := by
  rw [resolvent_eq_eigenvectorUnitary_conj_diagonal hA hζ]
  unfold NLAlib.specNorm
  rw [Unitary.conjStarAlgAut_apply]
  change ‖(hA.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => (ζ-(hA.eigenvalues i : ℂ))⁻¹) *
    ((star hA.eigenvectorUnitary : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)‖ ≤ _
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (abs_nonneg _))).mpr
  intro i
  rw [norm_inv]
  have hi : |ζ.im| ≤ ‖ζ-(hA.eigenvalues i : ℂ)‖ := by
    simpa using Complex.abs_im_le_norm (ζ-(hA.eigenvalues i : ℂ))
  simpa only [one_div] using one_div_le_one_div_of_le (abs_pos.mpr hζ) hi

end NLAlib
