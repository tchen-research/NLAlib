import NLAlib.Matrix.Spectral.IndefiniteCongruence
import NLAlib.Matrix.Spectral.SemidefiniteCongruence
import NLAlib.Matrix.Spectral.DefiniteCongruence
/-!
# Simultaneous real congruence: definite, indefinite, and semidefinite pairs

Complete simultaneous-congruence contract, with the real relative spectrum,
inertia, and the singular three-block dimensions. Source: Horn--Johnson
(2013), Theorems 4.5.17 and 7.6.1 and Corollary 7.6.2;
atlas `simultaneous-diagonalization-congruence`.
-/

noncomputable section
open Matrix Polynomial
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Simultaneous congruence for every real symmetric pair: definite whitening
with the exact relative eigenvalue multiset and inertia; the indefinite
nonsingular criterion; and the PSD three-block form with rank and common-kernel
dimensions. The block index sets may be permuted into the customary order.
Horn--Johnson (2013), Theorems 4.5.17 and 7.6.1 and Corollary 7.6.2.
atlas: simultaneous-diagonalization-congruence -/
theorem simultaneous_congruence_characterizations {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A.PosDef →
      (∃ (S : Matrix n n ℝ) (d : n → ℝ), IsUnit S ∧ A = S * Sᵀ ∧
        B = S * diagonal d * Sᵀ ∧
        (A⁻¹ * B).charpoly = ∏ i, (X - C (d i)) ∧
        spectrum ℝ (A⁻¹ * B) = Set.range d ∧ IsDiagonalizable (A⁻¹ * B) ∧
        inertiaPos (diagonal d) = inertiaPos B ∧ inertiaNeg (diagonal d) = inertiaNeg B ∧
        (B.PosSemidef → ∀ i, 0 ≤ d i)) ∧
      IsDiagonalizable (A * B) ∧ (B.PosSemidef → spectrum ℝ (A * B) ⊆ Set.Ici 0)) ∧
    (IsUnit A →
      ((∃ (T : Matrix n n ℝ) (a b : n → ℝ), IsUnit T ∧
        Tᵀ * A * T = diagonal a ∧ Tᵀ * B * T = diagonal b) ↔
          IsDiagonalizable (A⁻¹ * B))) ∧
    (A.PosSemidef → B.PosSemidef →
      ∃ (S : Matrix n n ℝ) (a b : n → ℝ), IsUnit S ∧
        A = S * diagonal a * Sᵀ ∧ B = S * diagonal b * Sᵀ ∧
        (∀ i, a i = 0 ∨ a i = 1) ∧ (∀ i, 0 ≤ b i) ∧
        (∀ i, a i = 0 → b i = 0 ∨ b i = 1) ∧
        A.rank = Fintype.card {i // a i = 1} ∧
        (A + B).rank = Fintype.card {i // a i = 1} +
          Fintype.card {i // a i = 0 ∧ b i = 1} ∧
        Module.finrank ℝ ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) =
          Fintype.card {i // a i = 0 ∧ b i = 0}) :=
  ⟨fun h => definite_pair_congruence_characterizations h hB,
    fun h => exists_diagonal_congruence_iff_isDiagonalizable_inverse_mul hA h hB,
    semidefinite_pair_congruence_normal_form⟩

end NLAlib
