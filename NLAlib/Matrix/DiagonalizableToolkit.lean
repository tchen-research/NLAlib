import NLAlib.Matrix.DiagonalizablePrincipal

/-!
# The diagonalizability toolkit

The complete equivalences, direct-sum rule, freedom in an aligned eigenbasis,
and geometric-multiplicity obstruction for principal submatrices.
Source: Horn–Johnson (2013), §§1.3–1.4; atlas `diagonalizable-def`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  {K : Type*} [Field K] [IsAlgClosed K]

/-- The full diagonalizability toolkit: similarity and eigenbasis criteria,
equality of algebraic and geometric multiplicity, distinct-eigenvalue
sufficiency, the direct-sum rule, invertible changes within aligned
eigenspaces, and the principal-submatrix multiplicity obstruction.
Source: Horn–Johnson (2013), Definition 1.3.6, Theorems 1.3.7, 1.3.9, 1.3.27
and 1.4.10, and Lemma 1.3.10. Matrices have arbitrary finite index types;
the field may be any algebraically closed field.
atlas: diagonalizable-def -/
theorem diagonalizable_properties (A : Matrix n n K) (B : Matrix m m K) :
    (IsDiagonalizable A ↔ ∃ (V : Matrix n n K) (d : n → K),
      IsUnit V ∧ A = V * Matrix.diagonal d * V⁻¹) ∧
    (IsDiagonalizable A ↔ ∃ (v : n → n → K) (d : n → K),
      LinearIndependent K v ∧ ∀ j, A *ᵥ v j = d j • v j) ∧
    (IsDiagonalizable A ↔ ∀ μ : K,
      Module.finrank K (Module.End.eigenspace A.toLin' μ) = A.charpoly.rootMultiplicity μ) ∧
    (∀ d : n → K, Function.Injective d → (∀ j, d j ∈ spectrum K A) → IsDiagonalizable A) ∧
    (IsDiagonalizable (Matrix.fromBlocks A 0 0 B) ↔ IsDiagonalizable A ∧ IsDiagonalizable B) ∧
    (∀ (V W : Matrix n n K) (d : n → K), IsUnit V → IsUnit W →
      A * V = V * Matrix.diagonal d → A * W = W * Matrix.diagonal d →
      IsUnit (V⁻¹ * W) ∧ ∀ i j, d i ≠ d j → (V⁻¹ * W) i j = 0) ∧
    (∀ (μ : K) (s : Finset n) (k : ℕ),
      k ≤ Module.finrank K (Module.End.eigenspace A.toLin' μ) →
      Fintype.card n < s.card + k →
      μ ∈ spectrum K (A.submatrix (fun j : s => j.val) (fun j : s => j.val))) ∧
    (∀ μ : K, Module.finrank K (Module.End.eigenspace A.toLin' μ) ≤
      A.charpoly.rootMultiplicity μ) := by
  refine ⟨isDiagonalizable_iff_exists_similarity A,
    isDiagonalizable_iff_exists_independent_eigenvectors A,
    isDiagonalizable_iff_finrank_eigenspace_eq_rootMultiplicity A,
    fun d hd hspec => isDiagonalizable_of_distinct_eigenvalues d hd hspec,
    isDiagonalizable_fromBlocks_zero_zero_iff A B,
    fun _ _ _ hV hW hAV hAW => isUnit_change_eigenbasis_and_apply_eq_zero hV hW hAV hAW,
    fun μ s k hk hs => mem_spectrum_principal_submatrix_of_le_finrank_eigenspace A μ s k hk hs,
    ?_⟩
  intro μ
  simpa only [Matrix.charpoly_toLin'] using LinearMap.finrank_eigenspace_le A.toLin' μ

end NLAlib
