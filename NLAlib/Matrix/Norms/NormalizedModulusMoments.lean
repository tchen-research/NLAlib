import NLAlib.Matrix.Norms.SchattenMixedPowers
import NLAlib.Matrix.Basic.NormalizedTrace
import NLAlib.ForMathlib.Analysis.FiniteMomentMeans

/-!
# Normalized matrix modulus moments

Exact finite singular-value averages and Jensen comparisons retain the
dimension normalization, including the empty matrix convention.
These facts support high resolvent moments without choosing eigenvectors.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The actual normalized modulus moment is the finite singular-value
average. Degree zero and empty matrix dimensions are included. -/
theorem re_normalizedTrace_cfcAbs_pow_eq_sum_div_card (B : Matrix n n 𝕜) (L : ℕ) :
    RCLike.re (normalizedTrace (CFC.abs B ^ L)) =
      (∑ i : Fin (Fintype.card n), singularValues B i ^ L) /
        (Fintype.card n : ℝ) := by
  have hc : (Fintype.card n : 𝕜)⁻¹ =
      (((Fintype.card n : ℝ)⁻¹ : ℝ) : 𝕜) := by simp
  rw [normalizedTrace, hc]
  simp only [RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im,
    zero_mul, sub_zero, re_trace_cfcAbs_pow_eq_sum_singularValues,
    div_eq_mul_inv, mul_comm]

open scoped Matrix.Norms.L2Operator in
/-- A bounded matrix modulus's larger normalized moment is controlled by
its lower positive moment and any higher comparison moment. This is the
dimension-free scalar power-mean inequality applied to actual singular values.
Zero bounds, zero singular values and empty matrix dimensions are included. -/
theorem re_normalizedTrace_cfcAbs_pow_le_pow_mul_moment_rpow
    (B : Matrix n n 𝕜) {r : ℝ} (hr : 0 ≤ r) (hB : specNorm B ≤ r)
    {k j L : ℕ} (hk : 0 < k) (hkj : k ≤ j) (hkL : k ≤ L) :
    RCLike.re (normalizedTrace (CFC.abs B ^ L)) ≤
      r ^ (L - k) *
        RCLike.re (normalizedTrace (CFC.abs B ^ j)) ^ ((k : ℝ) / j) := by
  simp only [re_normalizedTrace_cfcAbs_pow_eq_sum_div_card]
  simpa only [Fintype.card_fin] using
    Real.sum_pow_div_card_le_pow_mul_rpow_sum_pow_div_card
      (fun i : Fin (Fintype.card n) => singularValues B i)
      (fun i => singularValues_nonneg B i) hr
      (fun i => (singularValues_le_specNorm B i).trans hB) hk hkj hkL

open scoped Matrix.Norms.L2Operator in
/-- Even powers of the actual matrix modulus are exactly column-Gram
powers, with the same native normalized trace, including degree zero. -/
theorem re_normalizedTrace_cfcAbs_pow_two_mul (B : Matrix n n 𝕜) (p : ℕ) :
    RCLike.re (normalizedTrace (CFC.abs B ^ (2 * p))) =
      RCLike.re (normalizedTrace ((Bᴴ * B) ^ p)) := by
  rw [pow_mul, CFC.abs_sq, Matrix.star_eq_conjTranspose]

end NLAlib
