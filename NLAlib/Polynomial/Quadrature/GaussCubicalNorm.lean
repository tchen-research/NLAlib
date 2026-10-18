import NLAlib.Polynomial.Quadrature.GaussKernelContinuity
import NLAlib.ForMathlib.Analysis.Complex.CubicalTrace

/-! # The actual maximum-norm Gauss contour error bound

The actual rho/pi kernel is continuous on the compact contour trace, so its
maximum is finite. The length bound therefore specializes to precisely the
two actual maxima in Gautschi (2004), Theorem 2.48.
-/

noncomputable section
open Polynomial MeasureTheory Set Complex
open scoped unitInterval
namespace NLAlib

/-- The actual null-homologous-cycle Gauss error is bounded by contour length
times the two actual maximum norms, divided by `2 pi`. Compact-support kernel
continuity and finiteness of these maxima are proved rather than supplied.
Corners and vanishing parameter derivatives are permitted.
Source: Gautschi (2004), Theorem 2.48, null-homologous-cycle alternative.
atlas: gauss-remainder-contour-kernel (partial) -/
theorem norm_integral_sub_gauss_le_cubicalLength_mul_maxNorm
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω)
    (hI : ∀ x ∈ Icc a b, (x : ℂ) ∈ Ω) (Γ : Cubical.OneChain Ω)
    (hΓ : ∀ γ ∈ Γ.support, ContDiffOn ℝ 1 (cubicalPath γ).extend I)
    (hoff : ∀ γ ∈ Γ.support, ∀ r, ∀ x ∈ Icc a b, (γ r : ℂ) ≠ (x : ℂ))
    (hnull : Cubical.IsNullHomologous Γ)
    (hw : ∀ x ∈ Icc a b, cubicalWindingIntegral Γ (x : ℂ) = 1) :
    let hμ := hasPolynomialMoments_of_ae_mem_Icc hs
    ‖(∫ x : ℝ, f (x : ℂ) ∂μ) - ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) *
      f (gaussNodes μ hμ n i : ℂ)‖ ≤ cubicalLength Γ / (2 * Real.pi) *
        cubicalMaxNorm Γ (gaussRemainderKernel μ hμ n) * cubicalMaxNorm Γ f := by
  have htraceOff (z : ℂ) (hz : z ∈ cubicalTrace Γ) : ∀ x ∈ Icc a b, z ≠ (x : ℂ) := by
    obtain ⟨γ, hz⟩ := mem_iUnion.mp hz
    obtain ⟨hγ, r, rfl⟩ := mem_iUnion.mp hz
    exact hoff γ hγ r
  have hK := continuousOn_gaussRemainderKernel_of_compact_off_Icc
    (hasPolynomialMoments_of_ae_mem_Icc hs) hs hn (isCompact_cubicalTrace Γ) htraceOff
  have hF := hf.continuousOn.mono (cubicalTrace_subset Γ)
  exact norm_integral_sub_gauss_le_cubicalLength_mul_bounds hs hn hΩ hf hI Γ hΓ hoff hnull hw
    (cubicalMaxNorm_nonneg Γ hF)
    (fun γ hγ r => norm_le_cubicalMaxNorm Γ hK (mem_cubicalTrace hγ r))
    (fun γ hγ r => norm_le_cubicalMaxNorm Γ hF (mem_cubicalTrace hγ r))

end NLAlib
