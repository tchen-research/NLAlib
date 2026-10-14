import NLAlib.Matrix.Functions.PolynomialCalculus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Resolvents of real Hermitian matrices over a field extension

The real eigenvector matrix diagonalizes the scalar-extended resolvent.
Only the final spectral differences must be nonzero; no nested fraction
denominator is imposed.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace NLAlib

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜]

/-- The resolvent of a scalar-extended real Hermitian matrix is obtained by
inverting its scalar spectral differences. -/
theorem inv_smul_one_sub_map_eq_eigenvector_mul_diagonal
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ →+* 𝕜) {z : 𝕜}
    (hz : ∀ i, z ≠ f (hA.eigenvalues i)) :
    (z • (1 : Matrix ι ι 𝕜) - A.map f)⁻¹ =
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).map f *
        diagonal (fun i => (z - f (hA.eigenvalues i))⁻¹) *
          ((hA.eigenvectorUnitary : Matrix ι ι ℝ).map f)ᵀ := by
  let U : Matrix ι ι 𝕜 := (hA.eigenvectorUnitary : Matrix ι ι ℝ).map f
  have hUtU : Uᵀ * U = 1 := by
    change (((hA.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ).map f) * _ = _
    rw [← Matrix.map_mul, transpose_eigenvectorUnitary_mul_self hA,
      Matrix.map_one _ (map_zero f) (map_one f)]
  have hUUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hUtU
  let φ : Matrix ι ι 𝕜 →+* Matrix ι ι 𝕜 :=
    { toFun := fun M => U * M * Uᵀ
      map_one' := by simp [hUUt]
      map_mul' := fun M N => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᵀ U, hUtU, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun M N => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hAmap : A.map f = φ (diagonal (fun i => f (hA.eigenvalues i))) := by
    conv_lhs => rw [eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA]
    simp only [Matrix.map_mul, ← Matrix.diagonal_map (map_zero f)]
    rfl
  have hscalar : φ (z • 1) = z • 1 := by
    change U * (z • 1) * Uᵀ = _
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUUt]
  have hdiag : z • (1 : Matrix ι ι 𝕜) - diagonal (fun i => f (hA.eigenvalues i)) =
      diagonal (fun i => z - f (hA.eigenvalues i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hres : z • 1 - A.map f = φ (diagonal (fun i => z - f (hA.eigenvalues i))) := by
    rw [← hdiag, map_sub, hscalar, hAmap]
  have hprod : diagonal (fun i => z - f (hA.eigenvalues i)) *
      diagonal (fun i => (z - f (hA.eigenvalues i))⁻¹) = (1 : Matrix ι ι 𝕜) := by
    rw [Matrix.diagonal_mul_diagonal]
    have hentry (i : ι) : (z - f (hA.eigenvalues i)) * (z - f (hA.eigenvalues i))⁻¹ = 1 :=
      mul_inv_cancel₀ (sub_ne_zero.mpr (hz i))
    simp only [hentry, Matrix.diagonal_one]
  apply Matrix.inv_eq_right_inv
  change (z • 1 - A.map f) * φ (diagonal (fun i => (z - f (hA.eigenvalues i))⁻¹)) = 1
  rw [hres, ← map_mul, hprod, map_one]

/-- Every entry of the scalar-extended resolvent is the finite spectral
partial fraction at every point outside the actual spectrum. In particular
the first diagonal entry gives the Jacobi spectral weights over complex
shifts. Source: operator derivations (OF27), (AQ18).
atlas: jacobi-fraction-second-kind (partial), jacobi-matrix-identities (partial) -/
theorem inv_smul_one_sub_map_apply_eq_sum {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (f : ℝ →+* 𝕜) {z : 𝕜} (hz : ∀ i, z ≠ f (hA.eigenvalues i)) (r s : ι) :
    (z • (1 : Matrix ι ι 𝕜) - A.map f)⁻¹ r s =
      ∑ i, f ((hA.eigenvectorBasis i : ι → ℝ) r) *
        f ((hA.eigenvectorBasis i : ι → ℝ) s) / (z - f (hA.eigenvalues i)) := by
  rw [inv_smul_one_sub_map_eq_eigenvector_mul_diagonal hA f hz,
    Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

end NLAlib
