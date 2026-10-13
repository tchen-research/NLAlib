import NLAlib.Matrix.Inequalities.Wielandt
import NLAlib.Matrix.Inequalities.PositiveSpectralEndpoints
import NLAlib.Matrix.Perturbation.ConditionNumber
/-!
# Sharp quadratic inverse and orthogonal angle bounds

Kantorovich and Wielandt estimates, their equivalence, extreme
eigenvalue endpoints, and the existing matrix condition-number expression.
Source: Horn--Johnson (2013), Section 7.4.12;
atlas `kantorovich-inequality`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Kantorovich's condition-number formula uses the existing matrix condition
number and the Euclidean norm, with the square root and its reciprocal.
Positive dimension is required only to identify the condition number with
the extreme-eigenvalue ratio. Horn--Johnson (2013), Section 7.4.12.
atlas: kantorovich-inequality -/
theorem quadForm_mul_quadForm_inv_le_moorePenroseConditionNumber_sqrt {A : Matrix n n ℝ}
    (hA : A.PosDef) (hN : 0 < Fintype.card n) (x : n → ℝ) :
    quadForm A x * quadForm A⁻¹ x ≤
      (1 / 4 : ℝ) * (Real.sqrt (moorePenroseConditionNumber A) + (Real.sqrt (moorePenroseConditionNumber A))⁻¹) ^ 2 *
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 4 := by
  let : Nonempty n := Fintype.card_pos_iff.mp hN
  let a := hA.isHermitian.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hN (by decide)⟩
  let b := hA.isHermitian.eigenvalues₀ ⟨0, hN⟩
  obtain ⟨ha, hab, hlo, hhi⟩ := posDef_extreme_eigenvalues_sandwich hA hN
  have hc : moorePenroseConditionNumber A = b / a := moorePenroseConditionNumber_eq_eigenvalues₀_ratio A hA
  have hconst : (a + b) ^ 2 / (4 * a * b) =
      (1 / 4 : ℝ) * (Real.sqrt (moorePenroseConditionNumber A) + (Real.sqrt (moorePenroseConditionNumber A))⁻¹) ^ 2 := by
    rw [hc]
    exact sq_add_div_four_mul_eq_sq_sqrt_ratio ha (ha.trans_le hab)
  have hk := quadForm_mul_quadForm_inv_le_of_sandwich hA ha hab hlo hhi x
  change quadForm A x * quadForm A⁻¹ x ≤ ((a + b) ^ 2 / (4 * a * b)) *
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 4 at hk
  rw [hconst] at hk
  exact hk

end NLAlib
