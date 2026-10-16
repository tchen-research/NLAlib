import NLAlib.RandomMatrix.Chaos.Khintchine

/-!
# Matrix-chaos estimates on arbitrary probability spaces

The finite product-law estimates apply to actual independent coordinate
families through their joint laws. All dimensions and constants are preserved.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib

universe u
variable {τ ι m n : Type u} [Fintype τ] [Fintype ι] [Fintype m] [Fintype n]
  [DecidableEq τ] [DecidableEq ι] [DecidableEq m] [DecidableEq n]
  [Nonempty ι] [Nonempty m] [Nonempty n]
  (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {ξ : Ω → τ × ι → ℝ}

/-- Ordinary iterated matrix Khintchine for an actual coordinate family on
an arbitrary sample space with the specified independent subgaussian joint
law. The constant is positive and depends only on the degree.
Source: the finite matrix-chaos reroute, ordinary Theorem 2.4 upper bound.
atlas: matrix-chaos-iterated-khintchine -/
theorem integral_specNorm_decoupledMatrixChaos_le_sigma_mul_log_rpow_of_hasLaw
    (hξ : HasLaw ξ (Measure.pi (fun ti : τ × ι => ν ti.2)) μ)
    (K : ℝ) (hK : 0 < K) (hcenter : ∀ i, ∫ x, x ∂ν i = 0)
    (hpsi : ∀ i, ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν i ≤ 2)
    (A : (τ → ι) → Matrix m n ℝ) :
    (∫ ω, specNorm (decoupledMatrixChaos A (fun t i => ξ ω (t, i))) ∂μ) ≤
      chaosKhintchineConstant (Fintype.card τ) * K ^ Fintype.card τ *
        (Real.log (max (Fintype.card m : ℝ) (Fintype.card n : ℝ) + Fintype.card ι)) ^
          ((Fintype.card τ : ℝ) / 2) * chaosSigma A := by
  rw [integral_specNorm_decoupledMatrixChaos_eq_expected_of_hasLaw ν hξ A]
  exact expectedDecoupledMatrixChaosNorm_le_sigma_mul_log_rpow ν K hK hcenter hpsi A

/-- The strong matrix-chaos estimate transports through the actual joint
coordinate law, retaining its dimension-free leading term and error exponent
`(q+2)/2`. The explicit positive constant depends only on the degree.
Source: the finite Hermite reroute of the matrix-chaos Theorem 2.5.
atlas: matrix-chaos-strong-khintchine -/
theorem integral_specNorm_decoupledMatrixChaos_le_sigma_add_covariance_mul_log_rpow_of_hasLaw
    (hξ : HasLaw ξ (Measure.pi (fun ti : τ × ι => ν ti.2)) μ)
    (K : ℝ) (hK : 0 < K) (hcenter : ∀ i, ∫ x, x ∂ν i = 0)
    (hpsi : ∀ i, ∫⁻ x, ENNReal.ofReal (Real.exp ((x / K) ^ 2)) ∂ν i ≤ 2)
    (A : (τ → ι) → Matrix m n ℝ) :
    (∫ ω, specNorm (decoupledMatrixChaos A (fun t i => ξ ω (t, i))) ∂μ) ≤
      chaosStrongKhintchineConstant (Fintype.card τ) * K ^ Fintype.card τ *
        (chaosSigma A +
          (Real.log (max (Fintype.card m : ℝ) (Fintype.card n : ℝ) + Fintype.card ι)) ^
            (((Fintype.card τ : ℝ) + 2) / 2) * chaosCovariance A) := by
  rw [integral_specNorm_decoupledMatrixChaos_eq_expected_of_hasLaw ν hξ A]
  exact expectedDecoupledMatrixChaosNorm_le_sigma_add_covariance_mul_log_rpow
    ν K hK hcenter hpsi A

end NLAlib
