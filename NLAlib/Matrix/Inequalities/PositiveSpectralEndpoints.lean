import NLAlib.Matrix.Inequalities.RelativeSpectrum
/-!
# Positive extreme eigenvalues and endpoint constants

The actual smallest and largest sorted eigenvalues bound a positive definite
matrix in Loewner order and identify its condition number.
Source: Horn--Johnson (2013), Section 7.4.12;
supports `kantorovich-inequality`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The extreme sorted eigenvalues of a positive definite matrix are positive
spectral endpoints for a Loewner sandwich. Positive dimension is explicit.
Horn--Johnson (2013), Section 7.4.12; helper for sharp constants. -/
theorem posDef_extreme_eigenvalues_sandwich {A : Matrix n n ℝ} (hA : A.PosDef)
    (hN : 0 < Fintype.card n) :
    let a := hA.isHermitian.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hN (by decide)⟩
    let b := hA.isHermitian.eigenvalues₀ ⟨0, hN⟩
    0 < a ∧ a ≤ b ∧ a • (1 : Matrix n n ℝ) ≤ A ∧ A ≤ b • (1 : Matrix n n ℝ) := by
  let lo : Fin (Fintype.card n) := ⟨Fintype.card n - 1, Nat.sub_lt hN (by decide)⟩
  let hi : Fin (Fintype.card n) := ⟨0, hN⟩
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hpos : 0 < hA.isHermitian.eigenvalues₀ lo := by
    simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hA.eigenvalues_pos (e lo)
  refine ⟨hpos, hA.isHermitian.eigenvalues₀_antitone (by exact Nat.zero_le _), ?_⟩
  apply (loewner_sandwich_iff_relative_spectrum_subset Matrix.PosDef.one hA.isHermitian _ _).mpr
  simp only [inv_one, Matrix.one_mul, hA.isHermitian.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨j, rfl⟩
  exact ⟨hA.isHermitian.eigenvalues₀_antitone (by exact Nat.le_pred_of_lt (Fin.isLt _)),
    hA.isHermitian.eigenvalues₀_antitone (by exact Nat.zero_le _)⟩

/-- The symmetric endpoint ratio equals the condition-ratio expression
involving the square root and its reciprocal. Horn--Johnson (2013),
Section 7.4.12; helper for the equivalent sharp constants. -/
theorem sq_add_div_four_mul_eq_sq_sqrt_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) ^ 2 / (4 * a * b) =
      (1 / 4 : ℝ) * (Real.sqrt (b / a) + (Real.sqrt (b / a))⁻¹) ^ 2 := by
  let t := Real.sqrt (b / a)
  have ht : t ≠ 0 := Real.sqrt_ne_zero'.mpr (div_pos hb ha)
  have hs : t ^ 2 = b / a := Real.sq_sqrt (div_nonneg hb.le ha.le)
  calc
    (a + b) ^ 2 / (4 * a * b) = (1 / 4 : ℝ) * ((b / a + 1) ^ 2 / (b / a)) := by
      field_simp
      ring
    _ = (1 / 4 : ℝ) * ((t ^ 2 + 1) ^ 2 / t ^ 2) := by rw [hs]
    _ = (1 / 4 : ℝ) * (t + t⁻¹) ^ 2 := by
      congr 1
      field_simp

end NLAlib
