import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Complex Hermitian Rayleigh expansions

The sorted eigenbasis identifies a complex Euclidean space with its complex
coordinate space. Parseval and the diagonal action of a Hermitian matrix give
its real Rayleigh form as a weighted sum of squared coordinate norms.
These helpers support the complex Courant–Fischer variational principle.

Source: Horn–Johnson 2013, Theorem 4.2.6 and the Hermitian spectral theorem;
Mathlib's `Matrix.IsHermitian.eigenvalues₀` and sorted eigenvector basis.
The catalogue id `courant-fischer` refers to the consuming variational theorem.
-/

noncomputable section
set_option autoImplicit false

open scoped InnerProductSpace

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- Complex-linear coordinates in the sorted orthonormal eigenbasis of a
Hermitian matrix. The basis is the one underlying Mathlib's `eigenvalues₀` and
`eigenvectorBasis`; empty finite index types are included. Source: the Hermitian
spectral theorem, Horn–Johnson 2013, §4.2; supports `courant-fischer`. -/
def complexEigenvectorCoordinates (hA : A.IsHermitian) :
    EuclideanSpace ℂ n →ₗ[ℂ] (Fin (Fintype.card n) → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (Fintype.card n) → ℂ)).toLinearMap.comp
    ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
      (finrank_euclideanSpace (𝕜 := ℂ) (ι := n))).repr.toLinearEquiv.toLinearMap

/-- The real Hermitian quadratic form is the eigenvalue-weighted sum of squared
norms of its sorted complex coordinates. No real-vector restriction is imposed.
Source: the Hermitian spectral theorem, Horn–Johnson 2013, Theorem 4.2.6;
supports `courant-fischer`. -/
theorem re_inner_euclideanLin_eq_sum (hA : A.IsHermitian) (x : EuclideanSpace ℂ n) :
    (inner ℂ x (A.toEuclideanLin x)).re =
      ∑ j, hA.eigenvalues₀ j * ‖complexEigenvectorCoordinates hA x j‖ ^ 2 := by
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let b := hT.eigenvectorBasis (finrank_euclideanSpace (𝕜 := ℂ) (ι := n))
  change (inner ℂ x (A.toEuclideanLin x)).re =
    ∑ j, hA.eigenvalues₀ j * ‖b.repr x j‖ ^ 2
  rw [← b.repr.inner_map_map x (A.toEuclideanLin x), PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hT.eigenvectorBasis_apply_self_apply
    (finrank_euclideanSpace (𝕜 := ℂ) (ι := n)) x j]
  change (inner ℂ (b.repr x j) ((hA.eigenvalues₀ j : ℂ) • b.repr x j)).re = _
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- Parseval's identity for the sorted complex eigenbasis, including the empty
space: the sum of squared coordinate norms is the Euclidean norm squared.
Source: orthonormal coordinates, Horn–Johnson 2013, §4.2;
supports `courant-fischer`. -/
theorem sum_norm_sq_complexEigenvectorCoordinates (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ n) :
    (∑ j, ‖complexEigenvectorCoordinates hA x j‖ ^ 2) = ‖x‖ ^ 2 := by
  let b := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
    (finrank_euclideanSpace (𝕜 := ℂ) (ι := n))
  change (∑ j, ‖b.repr x j‖ ^ 2) = ‖x‖ ^ 2
  rw [← EuclideanSpace.norm_sq_eq, b.repr.norm_map]

end NLAlib
