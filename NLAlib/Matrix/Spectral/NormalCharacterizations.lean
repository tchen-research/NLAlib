import NLAlib.Matrix.Spectral.NormalSimilarity
import NLAlib.Matrix.Spectral.SchurFrobenius
import NLAlib.Matrix.Spectral.NormalBlocks
import NLAlib.Matrix.Spectral.NormalRectangularIntertwining
import NLAlib.Matrix.Spectral.RealNormalSpecializations
import NLAlib.Matrix.Spectral.SchurTriangularization
/-!
# The complex and real normal-matrix toolkit

Equivalent spectral descriptions, block reduction, unitary classification,
rectangular Fuglede–Putnam, and real scalar/rotation-dilation normal forms.
Source: Horn–Johnson (2013), §2.5.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius in
/-- An orthonormal eigenbasis makes a complex matrix normal.
Horn–Johnson (2013), Theorem 2.5.3; the change-of-basis matrix is unitary. -/
theorem normal_of_orthonormalBasis_eigenvectors
    (A : Matrix n n ℂ) (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (d : n → ℂ)
    (hb : ∀ j, A *ᵥ ⇑(b j) = d j • ⇑(b j)) : A * Aᴴ = Aᴴ * A := by
  let U : Matrix.unitaryGroup n ℂ :=
    ⟨(EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hAU : A * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * Matrix.diagonal d := by
    ext i j
    have hcol : ∀ k, (U : Matrix n n ℂ) k j = (b j) k := fun _ => rfl
    rw [Matrix.mul_diagonal]
    have h := congrFun (hb j) i
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Matrix.mul_apply, hcol, mul_comm] using h
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  apply mul_conjTranspose_eq_conjTranspose_mul_of_unitary_diagonalization U d
  rw [← hAU, Matrix.mul_assoc, hUU, Matrix.mul_one]

open scoped Matrix.Norms.Frobenius in
/-- A complex matrix is normal exactly when it has an orthonormal eigenbasis.
Source: Horn–Johnson (2013), Theorem 2.5.3; empty dimensions are included.
atlas: normal-matrices (partial) -/
theorem normal_iff_exists_orthonormalBasis_eigenvectors (A : Matrix n n ℂ) :
    A * Aᴴ = Aᴴ * A ↔
      ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (d : n → ℂ),
        ∀ j, A *ᵥ ⇑(b j) = d j • ⇑(b j) :=
  ⟨exists_orthonormalBasis_eigenvectors_of_normal,
    fun ⟨b, d, hb⟩ => normal_of_orthonormalBasis_eigenvectors A b d hb⟩

open scoped Matrix.Norms.Frobenius in
/-- Equality of squared Frobenius mass with the squared magnitudes of any
complete characteristic-root list characterizes normality.
Horn–Johnson (2013), Theorem 2.5.3; root order and multiplicities are explicit.
atlas: normal-matrices (partial) -/
theorem sum_norm_sq_characteristic_eq_frobSq_iff_normal (A : Matrix n n ℂ) (d : n → ℂ)
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    (∑ i, ‖d i‖ ^ 2) = frobSq A ↔ A * Aᴴ = Aᴴ * A := by
  classical
  obtain ⟨U, T, hA, _, hchar⟩ := exists_unitary_schur_triangularization A (Fintype.equivFin n).symm
  have hsum := sum_norm_sq_eq_of_prod_X_sub_C_eq d (fun i => T i i) (hd.symm.trans hchar)
  rw [hsum]
  exact sum_norm_sq_schur_diagonal_eq_frobSq_iff_normal U T hA hchar

end NLAlib
