import NLAlib.Matrix.SeparableCharpolyDensity
import NLAlib.Matrix.SchurTriangularization

/-!
# Dense distinct characteristic-root lists over the real and complex fields

The separability density theorem yields actual injective complex eigenvalue
lists, with real matrices perturbed within the real matrix space.
Source: Horn–Johnson (2013), §2.3.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex matrices admitting a complete list of pairwise distinct
characteristic eigenvalues are dense. Source: Horn–Johnson (2013), §2.3;
the characteristic factorization explicitly certifies multiplicities.
atlas: schur-triangularization (partial) -/
theorem dense_exists_injective_charpoly_factors_complex :
    Dense {A : Matrix n n ℂ | ∃ d : n → ℂ, Function.Injective d ∧
      A.charpoly = ∏ i, (X - C (d i))} := by
  classical
  apply (dense_separable_charpoly (n := n) (K := ℂ)).mono
  intro A hA
  obtain ⟨U, T, _, _, hchar⟩ := exists_unitary_schur_triangularization A (Fintype.equivFin n).symm
  refine ⟨fun i => T i i, ?_, hchar⟩
  apply Polynomial.separable_prod_X_sub_C_iff.mp
  rw [← hchar]
  exact hA

/-- Real matrices admitting a complete list of pairwise distinct complex
characteristic eigenvalues are dense among real matrices. Source:
Horn–Johnson (2013), §2.3; complexification records possible nonreal conjugate
pairs and imposes no real-spectrum restriction.
atlas: schur-triangularization (partial) -/
theorem dense_exists_injective_charpoly_factors_real :
    Dense {A : Matrix n n ℝ | ∃ d : n → ℂ, Function.Injective d ∧
      (A.map Complex.ofReal).charpoly = ∏ i, (X - C (d i))} := by
  classical
  apply (dense_separable_charpoly (n := n) (K := ℝ)).mono
  intro A hA
  have hcharMap : (A.map Complex.ofReal).charpoly = Polynomial.map Complex.ofRealHom A.charpoly :=
    Matrix.charpoly_map A Complex.ofRealHom
  have hsep : (A.map Complex.ofReal).charpoly.Separable := by
    rw [hcharMap]
    exact hA.map
  obtain ⟨U, T, _, _, hchar⟩ := exists_unitary_schur_triangularization
    (A.map Complex.ofReal) (Fintype.equivFin n).symm
  refine ⟨fun i => T i i, ?_, hchar⟩
  apply Polynomial.separable_prod_X_sub_C_iff.mp
  rw [← hchar]
  exact hsep

end NLAlib
