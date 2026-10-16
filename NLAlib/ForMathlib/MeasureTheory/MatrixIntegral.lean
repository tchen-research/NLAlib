import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Adjoint and trace of actual matrix integrals

The continuous real-linear adjoint commutes with the total Bochner integral.
Hermitian matrix integrals are therefore Hermitian, with no pointwise support
restriction beyond an almost-everywhere statement.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace Matrix

variable {Ω n 𝕜 : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
  [RCLike 𝕜] {μ : Measure Ω}

private local instance : NormedSpace ℝ (Matrix n n 𝕜) where
    toModule := inferInstance
    norm_smul_le := by
      intro r A
      have he : r • A = (r : 𝕜) • A := by
        ext i j
        simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
      rw [he]
      simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using norm_smul_le (r : 𝕜) A

/-- Conjugate transpose commutes with the actual total square-matrix integral. -/
theorem integral_conjTranspose (f : Ω → Matrix n n 𝕜) :
    (∫ x, (f x)ᴴ ∂μ) = (∫ x, f x ∂μ)ᴴ := by
  let L : Matrix n n 𝕜 →ₗᵢ[ℝ] Matrix n n 𝕜 :=
    (starₗᵢ ℝ : Matrix n n 𝕜 ≃ₗᵢ[ℝ] Matrix n n 𝕜).toLinearIsometry
  simpa only [L, LinearIsometryEquiv.coe_toLinearIsometry, coe_starₗᵢ,
    Matrix.star_eq_conjTranspose] using L.integral_comp_comm (μ := μ) f

/-- An almost-everywhere Hermitian matrix-valued function has Hermitian integral. -/
theorem isHermitian_integral {f : Ω → Matrix n n 𝕜}
    (hf : ∀ᵐ x ∂μ, (f x).IsHermitian) : (∫ x, f x ∂μ).IsHermitian := by
  change (∫ x, f x ∂μ)ᴴ = ∫ x, f x ∂μ
  rw [← integral_conjTranspose]
  exact integral_congr_ae (hf.mono fun x hx => hx.eq)

/-- Ordinary trace commutes with an integrable matrix-valued function. -/
theorem trace_integral {f : Ω → Matrix n n 𝕜} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).trace = ∫ x, (f x).trace ∂μ := by
  exact ((Matrix.traceLinearMap n 𝕜 𝕜).toContinuousLinearMap.integral_comp_comm hf).symm

/-- Real part of ordinary trace commutes with an integrable matrix function. -/
theorem re_trace_integral {f : Ω → Matrix n n 𝕜} (hf : Integrable f μ) :
    RCLike.re (∫ x, f x ∂μ).trace = ∫ x, RCLike.re (f x).trace ∂μ := by
  rw [trace_integral hf]
  exact (integral_re ((Matrix.traceLinearMap n 𝕜 𝕜).toContinuousLinearMap.integrable_comp hf)).symm

end Matrix
