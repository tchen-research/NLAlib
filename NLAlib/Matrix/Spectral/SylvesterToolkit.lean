import NLAlib.Matrix.Spectral.PrimaryTriangularization
/-!
# The qualitative Sylvester toolkit

Unique solvability, real descent, polynomial intertwining, block intertwiners,
the corrected block commutant, and triangular primary decomposition.
Source: Horn–Johnson (2013), §2.4; atlas `sylvester-equation`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- The full qualitative Sylvester contract: spectral disjointness exactly
characterizes invertibility of the rectangular Sylvester map; disjoint real
data have real solutions; polynomial intertwining holds; disjoint block
spectra force block diagonal intertwiners and characterize conjugated
commutants with commuting diagonal blocks; and arbitrary complex matrices
admit single-eigenvalue upper triangular primary blocks. Source:
Horn–Johnson (2013), Theorem 2.4.4.1, Corollaries 2.4.4.2–2.4.4.3, and
Theorem 2.4.6.1. Empty shapes and arbitrary finite block sizes are included.
atlas: sylvester-equation -/
theorem sylvester_equation_properties
    {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] {p q : ι → Type*}
    [∀ i, Fintype (p i)] [∀ i, DecidableEq (p i)]
    [∀ i, Fintype (q i)] [∀ i, DecidableEq (q i)]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (Ar : Matrix m m ℝ) (Br : Matrix n n ℝ)
    (P : ∀ i, Matrix (p i) (p i) ℂ) (Q : ∀ i, Matrix (q i) (q i) ℂ) :
    (Function.Bijective (sylvesterLinearMap A B) ↔
      Disjoint (spectrum ℂ A) (spectrum ℂ B)) ∧
    (Disjoint (spectrum ℂ A) (spectrum ℂ B) →
      ∀ C : Matrix m n ℂ, ∃! X : Matrix m n ℂ, A * X - X * B = C) ∧
    (∀ X : Matrix m n ℂ, A * X = X * B → ∀ g : Polynomial ℂ,
      Polynomial.aeval A g * X = X * Polynomial.aeval B g) ∧
    (Disjoint (spectrum ℂ (Ar.map Complex.ofReal)) (spectrum ℂ (Br.map Complex.ofReal)) →
      ∀ C : Matrix m n ℝ, ∃! X : Matrix m n ℝ, Ar * X - X * Br = C) ∧
    ((∀ i j, i ≠ j → Disjoint (spectrum ℂ (P i)) (spectrum ℂ (Q j))) →
      ∀ X : Matrix (Σ i, p i) (Σ i, q i) ℂ,
      Matrix.blockDiagonal' P * X = X * Matrix.blockDiagonal' Q →
        X = Matrix.blockDiagonal' (Matrix.blockDiag' X) ∧
        ∀ i, P i * Matrix.blockDiag' X i = Matrix.blockDiag' X i * Q i) ∧
    ((Pairwise fun i j => Disjoint (spectrum ℂ (P i)) (spectrum ℂ (P j))) →
      ∀ S X : Matrix (Σ i, p i) (Σ i, p i) ℂ, IsUnit S →
      (Commute (S * Matrix.blockDiagonal' P * S⁻¹) X ↔
        ∃ Y : ∀ i, Matrix (p i) (p i) ℂ,
          X = S * Matrix.blockDiagonal' Y * S⁻¹ ∧ ∀ i, Commute (P i) (Y i))) ∧
    (∃ (d : ℂ → ℕ) (e : (Σ μ : ℂ, Fin (d μ)) ≃ m)
      (S : Matrix m m ℂ) (T : ∀ μ : ℂ, Matrix (Fin (d μ)) (Fin (d μ)) ℂ),
      IsUnit S ∧ (S⁻¹ * A * S).submatrix e e = Matrix.blockDiagonal' T ∧
      (∀ μ, (T μ).IsUpperTriangular) ∧ (∀ μ i, T μ i i = μ)) :=
  ⟨sylvesterLinearMap_bijective_iff_disjoint_spectrum A B,
    fun h C => existsUnique_sylvester_of_disjoint_spectrum A B h C,
    fun _ h g => aeval_intertwines h g,
    fun h C => existsUnique_real_sylvester_of_disjoint_complex_spectrum Ar Br h C,
    fun h _ hX => eq_blockDiagonal'_of_intertwines_of_disjoint_spectrum P Q h hX,
    fun h S X hS => commute_similarity_blockDiagonal'_iff P h S X hS,
    exists_similarity_primary_upperTriangular A⟩

end NLAlib
