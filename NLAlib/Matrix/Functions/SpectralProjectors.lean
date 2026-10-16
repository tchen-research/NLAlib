import NLAlib.Matrix.Functions.ExpLog

/-!
# Finite spectral projectors in a supplied unitary basis

Coordinate projections transported by a unitary form a positive resolution
of the identity. Their weighted sum is the corresponding diagonalization.
These finite identities support positive-map inequalities without assuming
complete positivity of a map on the full matrix algebra.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one coordinate projector in a supplied unitary basis. -/
def unitarySpectralProjector (U : unitary (Matrix n n ℂ)) (i : n) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * diagonal (Pi.single i 1) * (U : Matrix n n ℂ)ᴴ

/-- Every unitary coordinate projector is positive semidefinite. -/
theorem posSemidef_unitarySpectralProjector (U : unitary (Matrix n n ℂ)) (i : n) :
    (unitarySpectralProjector U i).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  exact Matrix.posSemidef_diagonal_iff.mpr (fun j => by
    by_cases h : j = i <;> simp [h])

/-- A diagonal matrix is the weighted sum of its coordinate projectors. -/
theorem diagonal_eq_sum_smul_coordinateProjector (a : n → ℂ) :
    diagonal a = ∑ i, a i • (diagonal (Pi.single i 1) : Matrix n n ℂ) := by
  ext j k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : j = k
  · subst k
    simp [diagonal, Pi.single_apply]
  · simp [diagonal, h]

/-- Unitary diagonalization is a weighted sum of positive spectral projectors. -/
theorem unitary_mul_diagonal_mul_conjTranspose_eq_sum
    (U : unitary (Matrix n n ℂ)) (a : n → ℂ) :
    (U : Matrix n n ℂ) * diagonal a * (U : Matrix n n ℂ)ᴴ =
      ∑ i, a i • unitarySpectralProjector U i := by
  rw [diagonal_eq_sum_smul_coordinateProjector, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, unitarySpectralProjector]

/-- The positive spectral projectors resolve the identity. -/
theorem sum_unitarySpectralProjector (U : unitary (Matrix n n ℂ)) :
    ∑ i, unitarySpectralProjector U i = 1 := by
  have h := unitary_mul_diagonal_mul_conjTranspose_eq_sum U (fun _ => 1)
  simpa [← Matrix.star_eq_conjTranspose] using h.symm

/-- A Hermitian matrix is the real-eigenvalue weighted sum of its spectral projectors. -/
theorem sum_eigenvalue_smul_unitarySpectralProjector {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    A = ∑ i, (hA.eigenvalues i : ℂ) • unitarySpectralProjector hA.eigenvectorUnitary i := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  exact unitary_mul_diagonal_mul_conjTranspose_eq_sum _ _

/-- Powers use the same projectors, including repeated and zero eigenvalues. -/
theorem pow_eq_sum_eigenvalue_pow_smul_unitarySpectralProjector
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    A ^ k = ∑ i, (hA.eigenvalues i : ℂ) ^ k •
      unitarySpectralProjector hA.eigenvectorUnitary i := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Matrix.diagonal_pow, Unitary.conjStarAlgAut_apply]
  exact unitary_mul_diagonal_mul_conjTranspose_eq_sum _ _

/-- Every scalar function on a finite Hermitian spectrum uses the same
positive projectors; no global regularity assumption is needed. -/
theorem cfc_eq_sum_smul_unitarySpectralProjector {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = ∑ i, (f (hA.eigenvalues i) : ℂ) •
      unitarySpectralProjector hA.eigenvectorUnitary i := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  exact unitary_mul_diagonal_mul_conjTranspose_eq_sum _ _

end NLAlib
