import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import NLAlib.ForMathlib.MeasureTheory.Integral

/-!
# Gaussian interpolation: second-moment bookkeeping

Small facts shared by the interpolation proofs of the Gaussian comparison inequalities
(`NLAlib.Gaussian.Comparison.Slepian`, `SudakovFernique`, `GordonMinimax`). Along the path
`Z(θ) = cos θ X + sin θ Y` between two independent centred Gaussian vectors, the derivative
process is `Z'(θ) = -sin θ X + cos θ Y`, and

* `covariance_rotation_eq`: `Cov(Z'(θ)ᵢ, Z(θ)ⱼ) = sin θ cos θ (𝔼 YᵢYⱼ - 𝔼 XᵢXⱼ)`;
* `integral_sub_sq_eq`: `𝔼 (Xᵢ - Xⱼ)² = 𝔼 XᵢXᵢ + 𝔼 XⱼXⱼ - 𝔼 XᵢXⱼ - 𝔼 XⱼXᵢ`.

The integrability criterion `integrable_comp_of_abs_le_sum_abs` (`g(X)` is integrable when
`|g x| ≤ ∑ₜ |xₜ| + K`) is in `NLAlib.ForMathlib.MeasureTheory.Integral`.

Gaussian integration by parts itself is `NLAlib.integral_mul_eq_sum_covariance_mul_integral`
(`NLAlib.Gaussian.Concentration.IntegrationByParts`).

Ported from the Prove2me solutions `GaussianMatrix.slepian_tail_comparison`,
`GaussianMatrix.sudakov_fernique` and `GaussianMatrix.gordon_minimax` (identical helper
sections, deduplicated).

Atlas: helpers of `slepian`, `sudakov-fernique`, `gordon-minimax`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

section Interp

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}

/-- Covariance of the derivative process `Z'(θ) = -sin θ X + cos θ Y` with the interpolated
process `Z(θ) = cos θ X + sin θ Y`, for jointly Gaussian centred `X, Y` with vanishing cross
moments: `Cov(Z'(θ)ᵢ, Z(θ)ⱼ) = sin θ cos θ (𝔼 YᵢYⱼ - 𝔼 XᵢXⱼ)`. Standard step of the
interpolation proofs (Vershynin 2018, proof of Thm 7.2.1). Atlas: helper of `slepian`,
`sudakov-fernique`, `gordon-minimax`. Ported from Prove2me solution
`GaussianMatrix.slepian_tail_comparison` (helper `sl_cov_DZ`). -/
theorem covariance_rotation_eq (X Y : ι → Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (fun t => X t ω, fun t => Y t ω)) P)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂P = 0)
    (hcross : ∀ s t, ∫ ω, X s ω * Y t ω ∂P = 0) (θ : ℝ) (i j : ι) :
    cov[fun ω => -Real.sin θ * X i ω + Real.cos θ * Y i ω,
      fun ω => Real.cos θ * X j ω + Real.sin θ * Y j ω; P]
      = Real.sin θ * Real.cos θ *
        (∫ ω, Y i ω * Y j ω ∂P - ∫ ω, X i ω * X j ω ∂P) := by
  have hP := hXY.isProbabilityMeasure
  have hXm : ∀ t, MemLp (X t) 2 P := fun t => (hXY.fst.eval t).memLp_two
  have hYm : ∀ t, MemLp (Y t) 2 P := fun t => (hXY.snd.eval t).memLp_two
  set s := Real.sin θ
  set c := Real.cos θ
  have hD : MemLp (fun ω => -s * X i ω + c * Y i ω) 2 P :=
    ((hXm i).const_mul _).add ((hYm i).const_mul _)
  have hZ : MemLp (fun ω => c * X j ω + s * Y j ω) 2 P :=
    ((hXm j).const_mul _).add ((hYm j).const_mul _)
  rw [covariance_eq_sub hD hZ]
  have hint : ∀ t, Integrable (X t) P := fun t => (hXm t).integrable one_le_two
  have hintY : ∀ t, Integrable (Y t) P := fun t => (hYm t).integrable one_le_two
  have hD0 : ∫ ω, -s * X i ω + c * Y i ω ∂P = 0 := by
    rw [integral_add ((hint i).const_mul _) ((hintY i).const_mul _), integral_const_mul,
      integral_const_mul, hX0, hY0]; ring
  rw [hD0, zero_mul, sub_zero]
  simp only [Pi.mul_apply]
  have e : (fun ω => (-s * X i ω + c * Y i ω) * (c * X j ω + s * Y j ω))
      = fun ω => (-s * c) * (X i ω * X j ω) + (-s ^ 2) * (X i ω * Y j ω)
        + c ^ 2 * (X j ω * Y i ω) + (c * s) * (Y i ω * Y j ω) := by
    funext ω; ring
  have i1 : Integrable (fun ω => X i ω * X j ω) P := (hXm i).integrable_mul (hXm j)
  have i2 : Integrable (fun ω => X i ω * Y j ω) P := (hXm i).integrable_mul (hYm j)
  have i3 : Integrable (fun ω => X j ω * Y i ω) P := (hXm j).integrable_mul (hYm i)
  have i4 : Integrable (fun ω => Y i ω * Y j ω) P := (hYm i).integrable_mul (hYm j)
  rw [e, integral_add (((i1.const_mul _).fun_add (i2.const_mul _)).fun_add (i3.const_mul _))
    (i4.const_mul _), integral_add ((i1.const_mul _).fun_add (i2.const_mul _)) (i3.const_mul _),
    integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hcross, hcross]
  ring

omit [Fintype ι] in
/-- Expansion of the squared increment: `𝔼 (Xᵢ - Xⱼ)² = 𝔼 XᵢXᵢ + 𝔼 XⱼXⱼ - 𝔼 XᵢXⱼ - 𝔼 XⱼXᵢ` for
square-integrable `X`. Atlas: helper of `slepian`, `sudakov-fernique`, `gordon-minimax`. Ported
from Prove2me solution `GaussianMatrix.slepian_tail_comparison` (helper `sl_sq_sub`). -/
theorem integral_sub_sq_eq (X : ι → Ω → ℝ) (hXm : ∀ t, MemLp (X t) 2 P) (i j : ι) :
    ∫ ω, (X i ω - X j ω) ^ 2 ∂P = ∫ ω, X i ω * X i ω ∂P + ∫ ω, X j ω * X j ω ∂P
      - ∫ ω, X i ω * X j ω ∂P - ∫ ω, X j ω * X i ω ∂P := by
  have i1 : Integrable (fun ω => X i ω * X i ω) P := (hXm i).integrable_mul (hXm i)
  have i2 : Integrable (fun ω => X j ω * X j ω) P := (hXm j).integrable_mul (hXm j)
  have i3 : Integrable (fun ω => X i ω * X j ω) P := (hXm i).integrable_mul (hXm j)
  have i4 : Integrable (fun ω => X j ω * X i ω) P := (hXm j).integrable_mul (hXm i)
  have e : (fun ω => (X i ω - X j ω) ^ 2) = fun ω => X i ω * X i ω + X j ω * X j ω
      - X i ω * X j ω - X j ω * X i ω := by funext ω; ring
  rw [e, integral_sub ((i1.fun_add i2).sub' i3) i4, integral_sub (i1.fun_add i2) i3,
    integral_add i1 i2]

end Interp

end NLAlib
