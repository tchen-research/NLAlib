import NLAlib.Matrix.HadamardExponential
import NLAlib.Matrix.HadamardDeterminantLower
import NLAlib.Matrix.HadamardMinimumSpectrum
import NLAlib.Matrix.HadamardDominanceCounterexample

/-!
# Complete Schur-product inequalities

Positive diagonal strengthening, powers and actual convergent power series,
the exact exponential finite certificate, Oppenheim, inverse and minimum
spectrum inequalities, and the corrected Hermitian dominance refinement.
Source: Horn--Johnson (2013), Sections 7.5, 7.7 and 7.8;
atlas `schur-product-inequalities`.
-/

noncomputable section
open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Full Schur-product contract for real PSD matrices, including every
positive-definite refinement, actual formal-series radius, exact exponential
row-distinctness and finite-truncation certificate, both Oppenheim bounds,
inverse order, product-spectrum minima, and Hermitian quadratic dominance.
Empty and singular cases are included wherever the source quantity is
defined; minimum eigenvalues are selected only in positive dimension.
The Hermitian dominance restriction repairs the false arbitrary-comparand
extension, with a separate explicit counterexample.
Horn--Johnson (2013), Theorems 7.5.3, 7.5.9, 7.7.17, 7.7.18, 7.8.16,
Corollary 7.7.14, and Lemma 7.8.15.
atlas: schur-product-inequalities -/
theorem schur_product_inequalities {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A.PosDef → (∀ i, 0 < B i i) → (A ⊙ B).PosDef) ∧
    (∀ k : ℕ, (A.map (fun t => t ^ k)).PosSemidef) ∧
    (∀ (c : ℕ → ℝ), (∀ k, 0 ≤ c k) → ∀ f : ℝ → ℝ,
      (∀ i j, HasSum (fun k => c k * (A i j) ^ k) (f (A i j))) → (A.map f).PosSemidef) ∧
    (∀ (c : ℕ → ℝ), (∀ k, 0 ≤ c k) →
      (∀ i j, (‖A i j‖₊ : ENNReal) < (FormalMultilinearSeries.ofScalars ℝ c).radius) →
        (A.map (FormalMultilinearSeries.ofScalarsSum c)).PosSemidef) ∧
    (A.map Real.exp).PosSemidef ∧
    ((A.map Real.exp).PosDef ↔ Function.Injective A.row) ∧
    ((∑ k ∈ Finset.range (Fintype.card n), (k.factorial : ℝ)⁻¹ • A.map (fun t => t ^ k)).PosDef ↔
      Function.Injective A.row) ∧
    (A.map Real.exp - ∑ k ∈ Finset.range (Fintype.card n),
      (k.factorial : ℝ)⁻¹ • A.map (fun t => t ^ k)).PosSemidef ∧
    (max (A.det * ∏ i, B i i) (B.det * ∏ i, A i i) ≤ (A ⊙ B).det) ∧
    (A.PosDef → B.PosDef → (A ⊙ B)⁻¹ ≤ A⁻¹ ⊙ B⁻¹) ∧
    (A.PosDef → 1 ≤ A ⊙ A⁻¹) ∧
    (A.PosDef → B.PosDef → 0 < Fintype.card n →
      max (sInf (spectrum ℝ (A * B))) (sInf (spectrum ℝ (A * Bᵀ))) ≤
        sInf (spectrum ℝ (A ⊙ B))) ∧
    (∀ C D E F : Matrix n n ℝ,
      C.IsHermitian → D.IsHermitian → E.IsHermitian → F.IsHermitian →
      (∀ x, |quadForm D x| ≤ quadForm C x) → (∀ x, |quadForm F x| ≤ quadForm E x) →
      ∀ x, |quadForm (D ⊙ F) x| ≤ quadForm (C ⊙ E) x) := by
  have he := entrywise_exponential_positivity_characterizations hA
  refine ⟨fun hAPD hdiag => posDef_hadamard_of_posDef_of_diag_pos hAPD hB hdiag,
    posSemidef_map_pow hA, posSemidef_map_of_nonneg_powerSeries hA,
    posSemidef_map_ofScalarsSum_of_lt_radius hA,
    he.1, he.2.1, he.2.2.1, he.2.2.2,
    max_det_mul_prod_diag_le_det_hadamard hA hB, inv_hadamard_le_hadamard_inv,
    one_le_hadamard_inv, ?_, fun _ _ _ _ hC hD hE hF hCD hEF =>
      abs_quadForm_hadamard_le_of_abs_quadForm_le hC hD hE hF hCD hEF⟩
  intro hAPD hBPD hN
  let : Nonempty n := Fintype.card_pos_iff.mp hN
  exact max_sInf_spectrum_mul_le_sInf_spectrum_hadamard hAPD hBPD

end NLAlib
