import NLAlib.Matrix.Functions.LoewnerDerivative
import NLAlib.Matrix.Functions.HermiteDifferentiation

/-!
# Daleckii--Krein differentiation

Finite Hermite interpolation and the flat spectral remainder prove the
actual real Fréchet derivative on the Hermitian subspace. The formula
holds in any supplied unitary eigenbasis, including repeated eigenvalues.
Tropp (2022), Theorem 14.13; toolkit derivations, formulas (F6)--(F9).
-/

noncomputable section
open Matrix Polynomial Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every real diagonal node in a unitary diagonalization is a real
spectral value of the original matrix. -/
theorem mem_real_spectrum_of_unitary_diagonalization (ev : n → ℝ)
    (U : unitary (Matrix n n ℂ)) {A : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * diagonal (fun i => (ev i : ℂ)) *
      (U : Matrix n n ℂ).conjTranspose) (i : n) : ev i ∈ spectrum ℝ A := by
  have hc : (ev i : ℂ) ∈ spectrum ℂ A := by
    rw [hA]
    change (ev i : ℂ) ∈ spectrum ℂ
      ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U) (diagonal (fun j => (ev j : ℂ))))
    rw [AlgEquiv.spectrum_eq, spectrum_diagonal]
    exact ⟨i, rfl⟩
  exact (spectrum.algebraMap_mem_iff ℂ).mp hc

/-- The CFC has its divided-difference derivative along the Hermitian
subspace. Differentiability at just the finite spectrum is sufficient. -/
theorem hasFDerivWithinAt_cfc_loewner {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {f : ℝ → ℝ} (hf : ∀ i, DifferentiableAt ℝ f (hA.eigenvalues i))
    (ev : n → ℝ) (U : unitary (Matrix n n ℂ))
    (hdiag : A = (U : Matrix n n ℂ) * diagonal (fun i => (ev i : ℂ)) *
      (U : Matrix n n ℂ).conjTranspose) :
    HasFDerivWithinAt (fun B : Matrix n n ℂ => cfc f B)
      (loewnerDerivative f ev U) {B | B.IsHermitian} A := by
  obtain ⟨p, hv, hd, hp⟩ := exists_hermite_polynomial_hasFDerivWithinAt_cfc hA hf
  have hnodes (i : n) : ∃ j, hA.eigenvalues j = ev i := by
    have hi := mem_real_spectrum_of_unitary_diagonalization ev U hdiag i
    rwa [hA.spectrum_real_eq_range_eigenvalues] at hi
  have hv' (i : n) : p.eval (ev i) = f (ev i) := by
    obtain ⟨j, hj⟩ := hnodes i
    rw [← hj]
    exact hv j
  have hd' (i : n) : p.derivative.eval (ev i) = deriv f (ev i) := by
    obtain ⟨j, hj⟩ := hnodes i
    rw [← hj]
    exact hd j
  rw [frechetDerivative_eq_loewnerDerivative p ev U hdiag,
    loewnerDerivative_eq_of_values_deriv p f ev U hv' hd'] at hp
  exact hp

/-- Daleckii--Krein: the actual real Fréchet derivative on the Hermitian
matrix space is the conjugated divided-difference Hadamard operator.
Differentiability at each eigenvalue is enough, hence in particular the
source's `C¹` hypothesis on any open spectral interval is sufficient.
The supplied unitary basis need not order or separate repeated eigenvalues.
atlas: matrix-function-frechet-divided-difference -/
theorem hasFDerivAt_cfc_hermitian_loewner
    (A : selfAdjoint.submodule ℝ (Matrix n n ℂ)) {f : ℝ → ℝ}
    (hf : ∀ i, DifferentiableAt ℝ f ((show (A : Matrix n n ℂ).IsHermitian from A.property).eigenvalues i))
    (ev : n → ℝ) (U : unitary (Matrix n n ℂ))
    (hdiag : (A : Matrix n n ℂ) = (U : Matrix n n ℂ) * diagonal (fun i => (ev i : ℂ)) *
      (U : Matrix n n ℂ).conjTranspose) :
    HasFDerivAt (fun B : selfAdjoint.submodule ℝ (Matrix n n ℂ) => cfc f (B : Matrix n n ℂ))
      ((loewnerDerivative f ev U).comp (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL) A := by
  have h := hasFDerivWithinAt_cfc_loewner (show (A : Matrix n n ℂ).IsHermitian from A.property)
    hf ev U hdiag
  exact h.comp_hasFDerivAt A (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtypeL.hasFDerivAt
    (Filter.Eventually.of_forall fun B : selfAdjoint.submodule ℝ (Matrix n n ℂ) => B.property)

end NLAlib
