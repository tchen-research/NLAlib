import NLAlib.Matrix.Functions.LogDetConcavity
/-!
# Homogeneity of the positive determinant root

The determinant root has degree one and normalization to determinant one
when the dimension is positive. Source: Horn--Johnson (2013), Section 7.6;
supports `log-det-concavity` and Minkowski's determinant inequality.
-/

noncomputable section
open Matrix
open scoped MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Raising the positive-dimensional determinant root back to the dimension
recovers the determinant. Horn--Johnson (2013), Section 7.6;
helper for Minkowski's determinant inequality. -/
theorem det_rpow_inv_card_pow_card {A : Matrix n n ℝ} (hA : A.PosDef)
    (hN : 0 < Fintype.card n) :
    (A.det ^ (1 / (Fintype.card n : ℝ))) ^ Fintype.card n = A.det := by
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [← Real.rpow_natCast, ← Real.rpow_mul hA.det_pos.le, one_div_mul_cancel hn, Real.rpow_one]

/-- The positive-dimensional determinant root is homogeneous of degree one
under every nonnegative scalar, including scalar zero.
Horn--Johnson (2013), Section 7.6; helper for determinant-root concavity. -/
theorem det_smul_rpow_inv_card {A : Matrix n n ℝ} (hA : A.PosDef)
    (hN : 0 < Fintype.card n) {c : ℝ} (hc : 0 ≤ c) :
    (c • A).det ^ (1 / (Fintype.card n : ℝ)) =
      c * A.det ^ (1 / (Fintype.card n : ℝ)) := by
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [Matrix.det_smul, Real.mul_rpow (pow_nonneg hc _) hA.det_pos.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hc, mul_one_div_cancel hn, Real.rpow_one]

/-- Scaling by the reciprocal determinant root normalizes a positive
definite matrix to determinant one. Positive dimension is essential.
Horn--Johnson (2013), Section 7.6; helper for determinant-root concavity. -/
theorem det_inv_rpow_smul_eq_one {A : Matrix n n ℝ} (hA : A.PosDef)
    (hN : 0 < Fintype.card n) :
    ((A.det ^ (1 / (Fintype.card n : ℝ)))⁻¹ • A).det = 1 := by
  rw [Matrix.det_smul, inv_pow, det_rpow_inv_card_pow_card hA hN, inv_mul_cancel₀ hA.det_pos.ne']

end NLAlib
