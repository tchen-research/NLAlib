import NLAlib.Matrix.Inequalities.HadamardInverse
/-!
# Minimum spectrum of a positive Hadamard product

Relative spectral order and `A ⊙ A⁻¹ ≥ I` give the lower bound by the
actual minimum real spectrum of the ordinary product.
Source: Horn--Johnson (2013), Theorem 7.7.18;
atlas `schur-product-inequalities`.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The product of two real positive definite matrices has a nonempty
positive real spectrum in positive dimension, and its infimum is its
smallest actual eigenvalue. Horn--Johnson (2013), Section 7.6;
helper for Schur-product spectral bounds. -/
theorem spectrum_mul_nonempty_and_sInf_nonneg_of_posDef [Nonempty n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (spectrum ℝ (A * B)).Nonempty ∧ 0 ≤ sInf (spectrum ℝ (A * B)) := by
  let : Invertible A := hA.isUnit.invertible
  obtain ⟨S, d, hS, hAA, hBB, hd⟩ := exists_definite_pair_congruence_diagonal hA.inv hB.isHermitian
  have hs : spectrum ℝ (A * B) = Set.range d := by
    simpa only [Matrix.inv_inv_of_invertible] using
      spectrum_inverse_mul_eq_range_of_congruence hS hAA hBB
  have hne : (spectrum ℝ (A * B)).Nonempty := hs ▸ Set.range_nonempty d
  refine ⟨hne, le_csInf hne ?_⟩
  intro z hz
  exact spectrum_mul_subset_nonneg_of_posDef hA hB.posSemidef hz

/-- The smallest eigenvalue of the Hadamard product of two real SPD matrices
is at least the smallest eigenvalue of their ordinary product. The second
source bound with the transposed second factor is identical for symmetric
real inputs; both are included by the displayed maximum.
Horn--Johnson (2013), Theorem 7.7.18.
atlas: schur-product-inequalities (partial) -/
theorem max_sInf_spectrum_mul_le_sInf_spectrum_hadamard [Nonempty n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    max (sInf (spectrum ℝ (A * B))) (sInf (spectrum ℝ (A * Bᵀ))) ≤
      sInf (spectrum ℝ (A ⊙ B)) := by
  let : Invertible A := hA.isUnit.invertible
  have hBt : Bᵀ = B := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.eq
  rw [hBt, max_self]
  let c := sInf (spectrum ℝ (A * B))
  have hc := (spectrum_mul_nonempty_and_sInf_nonneg_of_posDef hA hB).2
  have hlow : c • A⁻¹ ≤ B := by
    apply (smul_le_iff_relative_spectrum_lower hA.inv hB.isHermitian c).mpr
    intro z hz
    rw [Matrix.inv_inv_of_invertible] at hz
    exact csInf_le (A * B).finite_real_spectrum.bddBelow hz
  have hSchur := hadamard_le_hadamard_of_posSemidef_left hA.posSemidef hlow
  rw [Matrix.hadamard_smul] at hSchur
  have hunit : c • (1 : Matrix n n ℝ) ≤ c • (A ⊙ A⁻¹) :=
    smul_le_smul_of_nonneg_left (one_le_hadamard_inv hA) hc
  have hC : c • (1 : Matrix n n ℝ) ≤ A ⊙ B := hunit.trans hSchur
  have hAB := hA.hadamard hB
  have hne : (spectrum ℝ (A ⊙ B)).Nonempty := by
    rw [hAB.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact Set.range_nonempty _
  apply le_csInf hne
  have h := (smul_le_iff_relative_spectrum_lower Matrix.PosDef.one hAB.isHermitian c).mp hC
  simpa only [inv_one, Matrix.one_mul] using h

end NLAlib
