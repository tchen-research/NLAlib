import NLAlib.Matrix.Functions.HermitianCalculus
import NLAlib.Matrix.Norms.Core
import NLAlib.Polynomial.BestApproximation.ReciprocalExponentialUpper

/-!
# Explicit pole-free exponential approximation for PSD matrices

The scalar denominator certificate transfers through Hermitian functional
calculus over real or complex scalars, on arbitrary finite index types.
Source: focused reciprocal reroute, operator form in Section 1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem nonneg_of_mem_real_spectrum_of_posSemidef {A : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) {x : ℝ} (hx : x ∈ spectrum ℝ A) : 0 ≤ x := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hA.eigenvalues_nonneg i

/-- The actual explicit denominator is positive definite when evaluated at any
finite PSD real symmetric or complex Hermitian matrix, including the empty size.
Source: focused reciprocal reroute, operator form.
atlas: exp-rational-halfline (partial) -/
theorem posDef_aeval_reciprocalExponentialDenominator (n : ℕ) {A : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) : (aeval A (reciprocalExponentialDenominator n)).PosDef := by
  rw [← cfc_polynomial (reciprocalExponentialDenominator n) A hA.isHermitian]
  apply Matrix.IsStrictlyPositive.posDef
  apply (cfc_isStrictlyPositive_iff _ A (by fun_prop) hA.isHermitian).mpr
  intro x hx
  exact reciprocalExponentialDenominator_eval_pos n
    (nonneg_of_mem_real_spectrum_of_posSemidef hA hx)

private theorem inv_aeval_reciprocalExponentialDenominator_eq_cfc (n : ℕ)
    {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    (aeval A (reciprocalExponentialDenominator n))⁻¹ =
      cfc (fun x => ((reciprocalExponentialDenominator n).eval x)⁻¹) A := by
  rw [← cfc_polynomial (reciprocalExponentialDenominator n) A hA.isHermitian,
    Matrix.nonsing_inv_eq_ringInverse]
  symm
  exact cfc_inv (reciprocalExponentialDenominator n).eval A
    (fun x hx => (reciprocalExponentialDenominator_eval_pos n
    (nonneg_of_mem_real_spectrum_of_posSemidef hA hx)).ne')
      (by fun_prop) hA.isHermitian

/-- The explicit reciprocal polynomial gives the advertised dimension-independent
spectral error for the actual matrix exponential and inverse polynomial.
Source: focused reciprocal reroute, operator form.
atlas: exp-rational-halfline (partial) -/
theorem specNorm_matrixExp_neg_sub_inv_aeval_reciprocalExponentialDenominator_le
    (n : ℕ) {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    specNorm (matrixExp (-A) - (aeval A (reciprocalExponentialDenominator n))⁻¹) ≤
      Real.sqrt (40/21)/3^n := by
  let _ := normedAlgebraRealMatrix (𝕜 := 𝕜) (d := ι)
  have hpole : ∀ x ∈ spectrum ℝ A, (reciprocalExponentialDenominator n).eval x ≠ 0 :=
    fun x hx => (reciprocalExponentialDenominator_eval_pos n
      (nonneg_of_mem_real_spectrum_of_posSemidef hA hx)).ne'
  have hcont : ContinuousOn
      (fun x => ((reciprocalExponentialDenominator n).eval x)⁻¹) (spectrum ℝ A) :=
    (reciprocalExponentialDenominator n).continuous.continuousOn.inv₀ hpole
  rw [specNorm_eq_norm, show -A = (-1:ℝ) • A by simp,
    matrixExp_smul_eq_cfc A hA.isHermitian,
    inv_aeval_reciprocalExponentialDenominator_eq_cfc n hA,
    ← cfc_sub (fun x : ℝ => Real.exp (-1*x))
      (fun x => ((reciprocalExponentialDenominator n).eval x)⁻¹) A
      (by fun_prop) hcont]
  apply norm_cfc_le (𝕜 := ℝ) (a := A) (by positivity)
  intro x hx
  simpa only [neg_one_mul, Real.norm_eq_abs] using
    abs_exp_neg_sub_inv_reciprocalExponentialDenominator_le n
      (nonneg_of_mem_real_spectrum_of_posSemidef hA hx)

end NLAlib
