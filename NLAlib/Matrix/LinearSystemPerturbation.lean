import NLAlib.Matrix.ConditionNumber
import NLAlib.Matrix.InversePerturbationBounds
import Mathlib.Tactic.FieldSimp

/-!
# Forward and residual error for linear systems

The actual Euclidean matrix action is used, with relative error only when
the exact right-hand side is nonzero. Source: Higham, Theorem 7.2;
Golub--Van Loan, Theorem 2.6.2; operator derivations `root:linear`.
Atlas: `linear-system-perturbation`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Euclidean action of a real square matrix obeys its spectral norm.
Source: Mathlib's defining operator bound; supports `linear-system-perturbation`. -/
theorem norm_toEuclideanCLM_apply_le (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖ ≤ specNorm A * ‖x‖ := by
  exact (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).le_opNorm x

/-- The matrix inverse cancels the original Euclidean action.
Source: the nonsingular inverse identity; supports `linear-system-perturbation`. -/
theorem toEuclideanCLM_inv_apply_apply {A : Matrix n n ℝ} (hA : IsUnit A)
    (x : EuclideanSpace ℝ n) : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A⁻¹ (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x) = x := by
  have h := congrArg (fun M : Matrix n n ℝ => Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M x)
    (Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA))
  simpa only [map_mul, map_one, mul_apply_eq_comp, one_apply_eq_self] using h

/-- Every approximate solution has a relative forward error bounded by its
relative residual times the actual condition number. Higham, Theorem 7.2.
atlas: linear-system-perturbation (partial) -/
theorem norm_sub_div_norm_le_conditionNumber_mul_residual
    (A : Matrix n n ℝ) (hA : IsUnit A) (x b xhat : EuclideanSpace ℝ n)
    (hx : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x = b) (hb : b ≠ 0) :
    ‖x - xhat‖ / ‖x‖ ≤ conditionNumber A * ‖b - Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A xhat‖ / ‖b‖ := by
  have hx0 : x ≠ 0 := by intro h; rw [h, map_zero] at hx; exact hb hx.symm
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hError : x - xhat = Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A⁻¹ (b - Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A xhat) := by
    rw [← hx, map_sub, toEuclideanCLM_inv_apply_apply hA,
      toEuclideanCLM_inv_apply_apply hA]
  have hErrBound : ‖x - xhat‖ ≤ specNorm A⁻¹ * ‖b - Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A xhat‖ := by
    rw [hError]
    exact norm_toEuclideanCLM_apply_le _ _
  have hBnd : ‖b‖ ≤ specNorm A * ‖x‖ := by
    rw [← hx]
    exact norm_toEuclideanCLM_apply_le _ _
  rw [conditionNumber_eq_mul_specNorm_inv hA]
  apply (div_le_div_iff₀ hxn hbn).mpr
  have hM1 := mul_le_mul_of_nonneg_right hErrBound (norm_nonneg b)
  have hM2 := mul_le_mul_of_nonneg_left hBnd
    (mul_nonneg (specNorm_nonneg A⁻¹) (norm_nonneg (b - Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A xhat)))
  nlinarith

/-- Relative forward error under simultaneous matrix and right-hand-side
perturbations, with the exact advertised condition-number denominator.
Higham, Theorem 7.2; Golub--Van Loan, Theorem 2.6.2.
atlas: linear-system-perturbation (partial) -/
theorem norm_perturbation_div_norm_le_conditionNumber
    (A E : Matrix n n ℝ) (hA : IsUnit A) (x b h f : EuclideanSpace ℝ n)
    (hx : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x = b) (hb : b ≠ 0)
    (hPert : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (A + E) (x + h) = b + f)
    (hSmall : conditionNumber A * specNorm E / specNorm A < 1) :
    ‖h‖ / ‖x‖ ≤ conditionNumber A / (1 - conditionNumber A * specNorm E / specNorm A) *
      (specNorm E / specNorm A + ‖f‖ / ‖b‖) := by
  have hx0 : x ≠ 0 := by intro hz; rw [hz, map_zero] at hx; exact hb hx.symm
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hBnd : ‖b‖ ≤ specNorm A * ‖x‖ := by
    rw [← hx]
    exact norm_toEuclideanCLM_apply_le _ _
  have hAN : 0 < specNorm A := by
    have hNe : specNorm A ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hBnd
      exact (not_le_of_gt hbn) hBnd
    exact lt_of_le_of_ne (specNorm_nonneg A) hNe.symm
  have hScale : conditionNumber A * specNorm E / specNorm A = specNorm A⁻¹ * specNorm E := by
    rw [conditionNumber_eq_mul_specNorm_inv hA]
    field_simp [hAN.ne']
  have hProd : specNorm A⁻¹ * specNorm E < 1 := by simpa only [hScale] using hSmall
  have hBUnit := isUnit_add_of_specNorm_inv_mul_specNorm_lt_one hA hProd
  have hResidual : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (A + E) h =
      f - Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) E x := by
    calc
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (A + E) h =
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (A + E) (x + h) -
            Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (A + E) x := by
        rw [map_add (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (A + E)) x h]
        abel
      _ = (b + f) - (b + Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) E x) := by
        rw [hPert, map_add, add_apply, hx]
      _ = f - Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) E x := by abel
  have hError : h = Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (A + E)⁻¹
      (f - Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) E x) := by
    rw [← hResidual, toEuclideanCLM_inv_apply_apply hBUnit]
  have hInvBound := specNorm_inv_add_le_of_specNorm_inv_mul_specNorm_lt_one hA hProd
  have hResidualNorm : ‖f - Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) E x‖ ≤
      ‖f‖ + specNorm E * ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add (le_refl _) (norm_toEuclideanCLM_apply_le E x))
  have hCoeff : 0 ≤ specNorm A⁻¹ / (1 - specNorm A⁻¹ * specNorm E) :=
    div_nonneg (specNorm_nonneg _) (sub_pos.mpr hProd).le
  have hErrBound : ‖h‖ ≤ specNorm A⁻¹ / (1 - specNorm A⁻¹ * specNorm E) *
      (‖f‖ + specNorm E * ‖x‖) := by
    rw [hError]
    exact (norm_toEuclideanCLM_apply_le _ _).trans
      (mul_le_mul hInvBound hResidualNorm (norm_nonneg _) hCoeff)
  have hFRelative : ‖f‖ / ‖x‖ ≤ specNorm A * ‖f‖ / ‖b‖ := by
    apply (div_le_div_iff₀ hxn hbn).mpr
    have hh := mul_le_mul_of_nonneg_left hBnd (norm_nonneg f)
    nlinarith
  calc
    ‖h‖ / ‖x‖ ≤ (specNorm A⁻¹ / (1 - specNorm A⁻¹ * specNorm E) *
        (‖f‖ + specNorm E * ‖x‖)) / ‖x‖ := div_le_div_of_nonneg_right hErrBound hxn.le
    _ = specNorm A⁻¹ / (1 - specNorm A⁻¹ * specNorm E) * (‖f‖ / ‖x‖ + specNorm E) := by
      field_simp [hxn.ne']
    _ ≤ specNorm A⁻¹ / (1 - specNorm A⁻¹ * specNorm E) *
        (specNorm A * ‖f‖ / ‖b‖ + specNorm E) :=
      mul_le_mul_of_nonneg_left (add_le_add hFRelative (le_refl _)) hCoeff
    _ = conditionNumber A / (1 - conditionNumber A * specNorm E / specNorm A) *
        (specNorm E / specNorm A + ‖f‖ / ‖b‖) := by
      rw [hScale, conditionNumber_eq_mul_specNorm_inv hA]
      field_simp [hAN.ne', hbn.ne', (sub_pos.mpr hProd).ne']
      ring

/-- Complete linear-system perturbation contract: simultaneous-data relative
forward error and the a posteriori relative residual estimate, for the actual
Euclidean matrix action. Higham, Theorem 7.2; Golub--Van Loan, Theorem 2.6.2.
atlas: linear-system-perturbation -/
theorem linear_system_perturbation (A E : Matrix n n ℝ) (hA : IsUnit A)
    (x b h f : EuclideanSpace ℝ n)
    (hx : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x = b) (hb : b ≠ 0)
    (hPert : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (A + E) (x + h) = b + f)
    (hSmall : conditionNumber A * specNorm E / specNorm A < 1) :
    ‖h‖ / ‖x‖ ≤ conditionNumber A / (1 - conditionNumber A * specNorm E / specNorm A) *
      (specNorm E / specNorm A + ‖f‖ / ‖b‖) ∧
    (∀ xhat : EuclideanSpace ℝ n,
      ‖x - xhat‖ / ‖x‖ ≤ conditionNumber A *
        ‖b - Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A xhat‖ / ‖b‖) :=
  ⟨norm_perturbation_div_norm_le_conditionNumber A E hA x b h f hx hb hPert hSmall,
    fun xhat => norm_sub_div_norm_le_conditionNumber_mul_residual A hA x b xhat hx hb⟩

end NLAlib
