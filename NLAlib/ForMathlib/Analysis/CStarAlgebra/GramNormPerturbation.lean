import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Actual Gram inequalities under norm perturbations

The positive square of `ε T - E` gives the noncommutative Young inequality.
The perturbation Gram is then bounded by its actual squared operator norm.
These are native operator-order estimates, without a moment or Minkowski
assumption.
-/

noncomputable section
set_option autoImplicit false
open scoped ComplexOrder ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem realGramCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)).toContinuousFunctionalCalculus

attribute [local instance] realGramCFC

/-- The genuine Gram of a sum satisfies the sharp weighted positive-square
estimate for every positive real weight, without commutativity. -/
theorem star_mul_self_add_le_weighted (T E : A) {ε : ℝ} (hε : 0 < ε) :
    star (T + E) * (T + E) ≤
      (1 + ε) • (star T * T) + (1 + ε⁻¹) • (star E * E) := by
  have hp : 0 ≤ ε⁻¹ • (star (ε • T - E) * (ε • T - E)) :=
    smul_nonneg (inv_nonneg.mpr hε.le) (star_mul_self_nonneg _)
  have hc : ε⁻¹ * (ε * ε) = ε := by field_simp [hε.ne']
  have he : ε⁻¹ • (star (ε • T - E) * (ε • T - E)) =
      ((1 + ε) • (star T * T) + (1 + ε⁻¹) • (star E * E)) -
        star (T + E) * (T + E) := by
    simp only [star_sub, star_smul, star_trivial, star_add, sub_mul, mul_sub,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul, inv_mul_cancel₀ hε.ne', hc, one_smul]
    module
  exact sub_nonneg.mp (he ▸ hp)

/-- Every actual perturbation Gram is bounded by the square of the native
operator norm times the algebra identity, including the trivial algebra. -/
theorem star_mul_self_le_norm_sq (E : A) :
    star E * E ≤ algebraMap ℝ A (‖E‖ ^ 2) := by
  have h := (IsSelfAdjoint.star_mul_self E).le_algebraMap_norm_self
  simpa only [CStarRing.norm_star_mul_self, pow_two] using h

/-- The genuine Gram of a perturbed element is controlled by the original
Gram and the actual squared norm of their difference. -/
theorem star_mul_self_le_weighted_gram_add_norm (S T : A) {ε : ℝ} (hε : 0 < ε) :
    star S * S ≤ (1 + ε) • (star T * T) +
      algebraMap ℝ A ((1 + ε⁻¹) * ‖S - T‖ ^ 2) := by
  have h₁ := star_mul_self_add_le_weighted T (S-T) hε
  have h₂ : (1+ε) • (star T*T) + (1+ε⁻¹) • (star (S-T)*(S-T)) ≤
      (1+ε) • (star T*T) + algebraMap ℝ A ((1+ε⁻¹)*‖S-T‖^2) := by
    apply add_le_add le_rfl
    have h := smul_le_smul_of_nonneg_left (star_mul_self_le_norm_sq (S-T))
      (by positivity : 0 ≤ 1+ε⁻¹)
    simpa only [Algebra.smul_def, ← map_mul] using h
  have he : T+(S-T)=S := by abel
  simpa only [he] using h₁.trans h₂

end
