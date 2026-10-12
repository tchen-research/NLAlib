import NLAlib.Matrix.Perturbation.InversePerturbation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Neumann series and quantitative inverse perturbation

The spectral and Frobenius estimates are valid for arbitrary finite indices,
including the empty matrix. Source: Golub--Van Loan, Lemma 2.3.3 and
Theorem 2.3.4; operator derivations, Section `root:inverse`.
Atlas target: `inverse-perturbation`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The same inverse estimate for an additive perturbation of the identity.
Golub--Van Loan, Lemma 2.3.3; supports `inverse-perturbation`. -/
theorem specNorm_inv_one_add_le {F : Matrix n n ℝ} (hF : specNorm F < 1) :
    specNorm (1 + F)⁻¹ ≤ (1 - specNorm F)⁻¹ := by
  simpa only [sub_neg_eq_add, specNorm_neg, one_div] using
    (specNorm_inv_one_sub_le (F := -F) (by simpa only [specNorm_neg] using hF))

/-- Factor the perturbed matrix using its original nonsingular inverse.
Stewart--Sun, Section III.2; supports `inverse-perturbation`. -/
theorem add_eq_mul_one_add_inv_mul (A E : Matrix n n ℝ) (hA : IsUnit A) :
    A + E = A * (1 + A⁻¹ * E) := by
  rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mul]

/-- Complete quantitative Neumann and inverse perturbation contract. The actual
matrix inverses are used throughout, and both the spectral and Frobenius
difference estimates retain the product-scale denominator. Empty dimensions
are included. Golub--Van Loan, Lemma 2.3.3 and Theorem 2.3.4.
atlas: inverse-perturbation -/
theorem neumann_and_inverse_perturbation (F A E : Matrix n n ℝ)
    (hF : specNorm F < 1) (hA : IsUnit A) (hE : specNorm (A⁻¹ * E) < 1) :
    IsUnit (1 - F) ∧
    (1 - F)⁻¹ = ∑' k : ℕ, F ^ k ∧
    specNorm (1 - F)⁻¹ ≤ (1 - specNorm F)⁻¹ ∧
    specNorm ((1 - F)⁻¹ - 1) ≤ specNorm F / (1 - specNorm F) ∧
    IsUnit (A + E) ∧
    specNorm (A + E)⁻¹ ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) ∧
    specNorm ((A + E)⁻¹ - A⁻¹) ≤
      specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm (A⁻¹ * E)) ∧
    frobNorm ((A + E)⁻¹ - A⁻¹) ≤
      specNorm A⁻¹ ^ 2 * frobNorm E / (1 - specNorm (A⁻¹ * E)) :=
  ⟨isUnit_one_sub_of_specNorm_lt_one hF, (hasSum_pow_inv_one_sub hF).tsum_eq.symm,
    (by simpa only [one_div] using specNorm_inv_one_sub_le hF),
    specNorm_inv_one_sub_sub_one_le hF,
    isUnit_add_of_specNorm_inv_mul_lt_one hA hE, specNorm_inv_add_le hA hE,
    specNorm_inv_add_sub_inv_le hA hE, frobNorm_inv_add_sub_inv_le hA hE⟩

end NLAlib
