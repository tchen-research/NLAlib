import NLAlib.Matrix.Spectral.EigenvectorDeflationConverse
/-!
# The left–right eigenvector toolkit

Biorthogonality, paired oblique deflation and its converse, simplicity from
pairing at geometric multiplicity one, the nonzero adjugate factor, and
transport under intertwining.
Source: Horn–Johnson (2013), §§1.4 and 2.4; atlas `left-right-eigenvectors`.
-/

noncomputable section
open Module
open scoped Matrix

namespace NLAlib

/-- The complete left–right eigenvector contract. Geometric multiplicity
one suffices for the nonzero rank-one adjugate, including defective
eigenvalues. Left columns over the complex field are represented by their
conjugate rows. Source: Horn–Johnson (2013), Theorems 1.4.7, 1.4.12 and
2.4.11.1 and Lemma 1.4.11; arbitrary finite and empty matrix shapes are
allowed wherever the hypotheses can hold.
atlas: left-right-eigenvectors -/
theorem left_right_eigenvector_properties
    {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K] [IsAlgClosed K]
    {A : Matrix n n K} {x y : n → K} {μ : K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y) :
    (∀ (z : n → K) (ν : K), z ᵥ* A = ν • z → μ ≠ ν → z ⬝ᵥ x = 0) ∧
    (y ⬝ᵥ x ≠ 0 → ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y = S * Matrix.diagonal (Pi.single i 1) * S⁻¹) ∧
    (∀ (S : Matrix n n K) (i : n), IsUnit S →
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) →
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) →
      Matrix.col S i ≠ 0 ∧ (fun j => S⁻¹ i j) ≠ 0 ∧
        (fun j => S⁻¹ i j) ⬝ᵥ Matrix.col S i = 1 ∧
        A *ᵥ Matrix.col S i = μ • Matrix.col S i ∧
        (fun j => S⁻¹ i j) ᵥ* A = μ • (fun j => S⁻¹ i j)) ∧
    (A.charpoly.rootMultiplicity μ = 1 → y ⬝ᵥ x ≠ 0) ∧
    (finrank K (Module.End.eigenspace A.toLin' μ) = 1 →
      (A.charpoly.rootMultiplicity μ = 1 ↔ y ⬝ᵥ x ≠ 0)) ∧
    (finrank K (Module.End.eigenspace A.toLin' μ) = 1 →
      ∃ γ : K, γ ≠ 0 ∧ (μ • (1 : Matrix n n K) - A).adjugate = γ • Matrix.vecMulVec x y) ∧
    (∀ (B S : Matrix n n K) (z : n → K) (ν : K), A * S = S * B →
      B *ᵥ z = ν • z → A *ᵥ (S *ᵥ z) = ν • (S *ᵥ z)) ∧
    (∀ (B S : Matrix n n K) (z : n → K) (ν : K), S * A = B * S →
      z ᵥ* B = ν • z → (z ᵥ* S) ᵥ* A = ν • (z ᵥ* S)) :=
  ⟨fun _ _ hz hμν => dotProduct_eq_zero_of_left_right_eigenvalues_ne hAx hz hμν,
    exists_isolated_eigenvector_similarity hAx hyA,
    fun S i hS hcol hrow => eigenpair_of_isolated_similarity A S i μ hS hcol hrow,
    dotProduct_ne_zero_of_simple_eigenvalue hx hy hAx hyA,
    rootMultiplicity_eq_one_iff_pairing_ne_zero_of_finrank_eigenspace_eq_one hx hy hAx hyA,
    exists_adjugate_shift_eq_smul_vecMulVec_of_finrank_eigenspace_eq_one hx hy hAx hyA,
    fun _ _ _ _ hS hz => mulVec_eigenvector_of_intertwines hS hz,
    fun _ _ _ _ hS hz => vecMul_eigenvector_of_intertwines hS hz⟩

end NLAlib
