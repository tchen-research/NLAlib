import NLAlib.Matrix.Spectral.EigenvectorDeflation
import NLAlib.Matrix.Spectral.GeneralizedEigenPairing
import NLAlib.ForMathlib.LinearAlgebra.IsolatedCharpoly

/-!
# Characteristic factors of isolated eigenlines

The distinguished invariant line contributes one linear characteristic
factor. Algebraic simplicity excludes that eigenvalue from the remaining
principal block. Source: Horn–Johnson (2013), Lemma 1.4.11 and Lemma 6.3.10;
atlas `left-right-eigenvectors` and `simple-eigenvalue-perturbation`.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Algebraic simplicity excludes the isolated eigenvalue from the remaining
principal block. Source: Horn–Johnson (2013), Lemma 6.3.10.
atlas: simple-eigenvalue-perturbation (partial) -/
theorem not_mem_spectrum_submatrix_of_isolated_coordinate_of_simple
    (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hrow : ∀ j, M i j = if j = i then μ else 0)
    (hμ : M.charpoly.rootMultiplicity μ = 1) :
    μ ∉ spectrum K
      (M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  classical
  let B := M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)
  have hfactor : M.charpoly = (X - C μ) * B.charpoly :=
    charpoly_eq_X_sub_C_mul_submatrix_of_isolated_coordinate M i μ hcol hrow
  have hprod : (X - C μ) * B.charpoly ≠ 0 := hfactor ▸ M.charpoly_monic.ne_zero
  rw [hfactor, Polynomial.rootMultiplicity_mul hprod] at hμ
  simp only [Polynomial.rootMultiplicity_X_sub_C] at hμ
  have hB : B.charpoly.rootMultiplicity μ = 0 := Nat.add_eq_left.mp hμ
  intro hspec
  have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hspec
  have hpos := Polynomial.rootMultiplicity_pos'.mpr ⟨B.charpoly_monic.ne_zero, hroot⟩
  rw [hB] at hpos
  exact (Nat.lt_irrefl 0) hpos

/-- A simple eigenvalue admits a left–right normalized isolated similarity,
and the remaining principal block excludes that eigenvalue. Source:
Horn–Johnson (2013), Lemmas 1.4.11 and 6.3.10; the distinguished coordinate
can be relabeled as the first coordinate of the scalar/direct-sum split.
atlas: left-right-eigenvectors (partial), simple-eigenvalue-perturbation (partial) -/
theorem exists_simple_eigenvalue_isolated_similarity [IsAlgClosed K]
    {A : Matrix n n K} {x y : n → K} {μ : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      μ ∉ spectrum K ((S⁻¹ * A * S).submatrix
        (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  have hpair := dotProduct_ne_zero_of_simple_eigenvalue hx hy hAx hyA hμ
  obtain ⟨S, i, hS, hcol, hrow, hright, hleft, hproj⟩ :=
    exists_isolated_eigenvector_similarity hAx hyA hpair
  have hchar : (S⁻¹ * A * S).charpoly = A.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv S (S.isUnit_iff_isUnit_det.mp hS), Matrix.one_mul]
  exact ⟨S, i, hS, hcol, hrow, hright, hleft,
    not_mem_spectrum_submatrix_of_isolated_coordinate_of_simple (S⁻¹ * A * S) i μ
      hright hleft (by simpa only [hchar] using hμ)⟩

end NLAlib
