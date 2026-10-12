import NLAlib.Matrix.SimultaneousNormal
import NLAlib.Matrix.SimultaneousTriangularBasis
import NLAlib.Matrix.CommutingSpectra

/-!
# The simultaneous diagonalization and triangularization toolkit

Common eigenvectors and Schur bases for arbitrary commuting families,
diagonalizable and normal equivalences, prescribed diagonal eigenvalue order,
real diagonalizing similarities, and paired sum/product spectra.
Source: Horn–Johnson (2013), §§1.3, 2.3 and 2.4.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

/-- The complete simultaneous-family contract: common eigenvectors and
unitary Schur bases, similarity/unitary triangularization equivalence,
commuting/diagonalization equivalences for diagonalizable and normal families,
prescribed complete eigenvalue order of one diagonalized member, common real
similarities for real diagonalizable families, and paired spectra of commuting
sums and products. Source: Horn–Johnson (2013), Lemma 1.3.19, Theorems 1.3.21,
2.3.3 and 2.4.8.1, and Corollaries 2.4.8.5–2.4.8.6. The family index is
arbitrary; nonempty shape is needed only for a nonzero common eigenvector.
atlas: simultaneous-diagonalization -/
theorem simultaneous_diagonalization_properties
    {n ι : Type*} [Fintype n] [DecidableEq n]
    (A : ι → Matrix n n ℂ) (Ar : ι → Matrix n n ℝ)
    (e : Fin (Fintype.card n) ≃ n) :
    ((Pairwise fun a b => Commute (A a) (A b)) → Nonempty n →
      ∃ (x : n → ℂ) (d : ι → ℂ), x ≠ 0 ∧ ∀ a, A a *ᵥ x = d a • x) ∧
    ((Pairwise fun a b => Commute (A a) (A b)) →
      ∃ (U : Matrix.unitaryGroup n ℂ) (T : ι → Matrix n n ℂ), ∀ a,
        A a = (U : Matrix n n ℂ) * T a * (U : Matrix n n ℂ)ᴴ ∧
        (∀ i j, e.symm j < e.symm i → T a i j = 0) ∧
        (A a).charpoly = ∏ i, (X - C (T a i i))) ∧
    ((∃ V : Matrix n n ℂ, IsUnit V ∧
      ∀ a i j, e.symm j < e.symm i → (V⁻¹ * A a * V) i j = 0) ↔
      ∃ U : Matrix.unitaryGroup n ℂ,
        ∀ a i j, e.symm j < e.symm i →
          ((U : Matrix n n ℂ)ᴴ * A a * (U : Matrix n n ℂ)) i j = 0) ∧
    ((∀ a, IsDiagonalizable (A a)) →
      ((Pairwise fun a b => Commute (A a) (A b)) ↔
        ∃ (V : Matrix n n ℂ) (d : ι → n → ℂ), IsUnit V ∧
          ∀ a, A a * V = V * Matrix.diagonal (d a))) ∧
    ((∀ a, A a * (A a)ᴴ = (A a)ᴴ * A a) →
      ((Pairwise fun a b => Commute (A a) (A b)) ↔
        ∃ (U : Matrix.unitaryGroup n ℂ) (d : ι → n → ℂ),
          ∀ a, A a = (U : Matrix n n ℂ) * Matrix.diagonal (d a) * (U : Matrix n n ℂ)ᴴ)) ∧
    ((∀ a, IsDiagonalizable (A a)) → (Pairwise fun a b => Commute (A a) (A b)) →
      ∀ (a₀ : ι) (d₀ : n → ℂ), (A a₀).charpoly = ∏ j, (X - C (d₀ j)) →
      ∃ (V : Matrix n n ℂ) (d : ι → n → ℂ), IsUnit V ∧ d a₀ = d₀ ∧
        ∀ a, A a * V = V * Matrix.diagonal (d a)) ∧
    ((∀ a, A a * (A a)ᴴ = (A a)ᴴ * A a) → (Pairwise fun a b => Commute (A a) (A b)) →
      ∀ (a₀ : ι) (d₀ : n → ℂ), (A a₀).charpoly = ∏ j, (X - C (d₀ j)) →
      ∃ (U : Matrix.unitaryGroup n ℂ) (d : ι → n → ℂ), d a₀ = d₀ ∧
        ∀ a, A a = (U : Matrix n n ℂ) * Matrix.diagonal (d a) * (U : Matrix n n ℂ)ᴴ) ∧
    ((∀ a, IsDiagonalizable (Ar a)) → (Pairwise fun a b => Commute (Ar a) (Ar b)) →
      ∃ (V : Matrix n n ℝ) (d : ι → n → ℝ), IsUnit V ∧
        ∀ a, Ar a * V = V * Matrix.diagonal (d a)) ∧
    ((Pairwise fun a b => Commute (A a) (A b)) → ∀ i j,
      ∃ a b : n → ℂ,
        (A i).charpoly = ∏ k, (X - C (a k)) ∧ (A j).charpoly = ∏ k, (X - C (b k)) ∧
        (A i + A j).charpoly = ∏ k, (X - C (a k + b k)) ∧
        (A i * A j).charpoly = ∏ k, (X - C (a k * b k))) := by
  refine ⟨?_, fun h => exists_simultaneous_unitary_schur_triangularization A h e,
    exists_simultaneous_triangular_similarity_iff_unitary_of_equiv A e,
    fun h => pairwise_commute_iff_exists_simultaneous_diagonalization A h,
    fun h => pairwise_commute_iff_exists_simultaneous_unitary_diagonalization A h,
    fun hd hc a₀ d₀ hchar => exists_simultaneous_diagonalization_with_charpoly A hd hc a₀ d₀ hchar,
    fun hn hc a₀ d₀ hchar => exists_simultaneous_unitary_diagonalization_with_charpoly A hn hc a₀ d₀ hchar,
    fun hd hc => exists_simultaneous_diagonalization_of_commute Ar hd hc, ?_⟩
  · intro h hn
    let := hn
    exact exists_common_mulVec_eigenvector_of_commute A h
  · intro h i j
    apply exists_paired_charpoly_factors_add_mul_of_commute
    rcases eq_or_ne i j with rfl | hij
    · exact Commute.refl _
    · exact h hij

end NLAlib
