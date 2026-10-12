import NLAlib.Matrix.Inequalities.Wielandt
import NLAlib.Matrix.Inequalities.PositiveSpectralEndpoints
import NLAlib.Matrix.Perturbation.ConditionNumber
/-!
# Sharp quadratic inverse and orthogonal angle bounds

Kantorovich and Wielandt estimates, their equivalence, actual extreme
eigenvalue endpoints, and the existing matrix condition-number expression.
Source: Horn--Johnson (2013), Section 7.4.12;
atlas `kantorovich-inequality`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The complete endpoint form gives both sharp inequalities and their
logical equivalence. Positive scalar endpoints include the empty-dimensional
case without selecting eigenvalues. Horn--Johnson (2013), Section 7.4.12.
atlas: kantorovich-inequality (partial) -/
theorem quadratic_inverse_and_bilinear_bounds_of_sandwich {A : Matrix n n ℝ}
    (hA : A.PosDef) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlo : a • (1 : Matrix n n ℝ) ≤ A) (hhi : A ≤ b • (1 : Matrix n n ℝ)) :
    (∀ x : n → ℝ, quadForm A x * quadForm A⁻¹ x ≤
      ((a + b) ^ 2 / (4 * a * b)) * (x ⬝ᵥ x) ^ 2) ∧
    (∀ x y : n → ℝ, x ⬝ᵥ y = 0 → (x ⬝ᵥ A *ᵥ y) ^ 2 ≤
      ((b - a) / (b + a)) ^ 2 * quadForm A x * quadForm A y) ∧
    ((∀ x : n → ℝ, quadForm A x * quadForm A⁻¹ x ≤
        ((a + b) ^ 2 / (4 * a * b)) * (x ⬝ᵥ x) ^ 2) ↔
      (∀ x y : n → ℝ, x ⬝ᵥ y = 0 → (x ⬝ᵥ A *ᵥ y) ^ 2 ≤
        ((b - a) / (b + a)) ^ 2 * quadForm A x * quadForm A y)) := by
  have hK := quadForm_mul_quadForm_inv_le_of_sandwich hA ha hab hlo hhi
  have hW := sq_bilinear_le_sq_ratio_mul_quadForm_of_sandwich hA ha hab hlo hhi
  exact ⟨hK, hW, ⟨fun _ => hW, fun _ => hK⟩⟩

/-- Kantorovich's condition-number formula uses the existing matrix condition
number and the actual Euclidean norm, with the square root and its reciprocal.
Positive dimension is required only to identify the condition number with
the extreme-eigenvalue ratio. Horn--Johnson (2013), Section 7.4.12.
atlas: kantorovich-inequality (partial) -/
theorem quadForm_mul_quadForm_inv_le_conditionNumber_sqrt {A : Matrix n n ℝ}
    (hA : A.PosDef) (hN : 0 < Fintype.card n) (x : n → ℝ) :
    quadForm A x * quadForm A⁻¹ x ≤
      (1 / 4 : ℝ) * (Real.sqrt (conditionNumber A) + (Real.sqrt (conditionNumber A))⁻¹) ^ 2 *
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 4 := by
  let : Nonempty n := Fintype.card_pos_iff.mp hN
  let a := hA.isHermitian.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hN (by decide)⟩
  let b := hA.isHermitian.eigenvalues₀ ⟨0, hN⟩
  obtain ⟨ha, hab, hlo, hhi⟩ := posDef_extreme_eigenvalues_sandwich hA hN
  have hc : conditionNumber A = b / a := conditionNumber_eq_eigenvalues₀_ratio A hA
  have hconst : (a + b) ^ 2 / (4 * a * b) =
      (1 / 4 : ℝ) * (Real.sqrt (conditionNumber A) + (Real.sqrt (conditionNumber A))⁻¹) ^ 2 := by
    rw [hc]
    exact sq_add_div_four_mul_eq_sq_sqrt_ratio ha (ha.trans_le hab)
  have hk := quadForm_mul_quadForm_inv_le_of_sandwich hA ha hab hlo hhi x
  have hx : (x ⬝ᵥ x) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, sq]
  change quadForm A x * quadForm A⁻¹ x ≤ ((a + b) ^ 2 / (4 * a * b)) * (x ⬝ᵥ x) ^ 2 at hk
  rw [hconst, hx, ← pow_mul] at hk
  exact hk

/-- The sharp extreme-eigenvalue Kantorovich and Wielandt bounds, their
equivalence, and the equivalent condition-number square-root expression.
The endpoint theorem supplies the zero-dimensional extension separately.
Horn--Johnson (2013), Section 7.4.12.
atlas: kantorovich-inequality -/
theorem quadratic_inverse_and_orthogonal_bilinear_bounds {A : Matrix n n ℝ}
    (hA : A.PosDef) (hN : 0 < Fintype.card n) :
    let a := hA.isHermitian.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hN (by decide)⟩
    let b := hA.isHermitian.eigenvalues₀ ⟨0, hN⟩
    (∀ x : n → ℝ, quadForm A x * quadForm A⁻¹ x ≤
      ((a + b) ^ 2 / (4 * a * b)) * (x ⬝ᵥ x) ^ 2) ∧
    (∀ x y : n → ℝ, x ⬝ᵥ y = 0 → (x ⬝ᵥ A *ᵥ y) ^ 2 ≤
      ((b - a) / (b + a)) ^ 2 * quadForm A x * quadForm A y) ∧
    ((∀ x : n → ℝ, quadForm A x * quadForm A⁻¹ x ≤
        ((a + b) ^ 2 / (4 * a * b)) * (x ⬝ᵥ x) ^ 2) ↔
      (∀ x y : n → ℝ, x ⬝ᵥ y = 0 → (x ⬝ᵥ A *ᵥ y) ^ 2 ≤
        ((b - a) / (b + a)) ^ 2 * quadForm A x * quadForm A y)) ∧
    (∀ x : n → ℝ, quadForm A x * quadForm A⁻¹ x ≤
      (1 / 4 : ℝ) * (Real.sqrt (conditionNumber A) + (Real.sqrt (conditionNumber A))⁻¹) ^ 2 *
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 4) := by
  obtain ⟨ha, hab, hlo, hhi⟩ := posDef_extreme_eigenvalues_sandwich hA hN
  have h := quadratic_inverse_and_bilinear_bounds_of_sandwich hA ha hab hlo hhi
  exact ⟨h.1, h.2.1, h.2.2, quadForm_mul_quadForm_inv_le_conditionNumber_sqrt hA hN⟩

end NLAlib
