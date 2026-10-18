import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Gaussian uniqueness from all coordinate covariances

A finite real Gaussian law is determined by its vector mean and every mixed
coordinate covariance. The proof transports to Euclidean space and uses the
native Gaussian uniqueness theorem and covariance bilinear-form expansion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory WithLp

namespace ProbabilityTheory.IsGaussian

/-- Finite real Gaussian laws with the same mean and every mixed coordinate
covariance are equal, including singular and zero covariance. -/
theorem ext_of_pi_mean_covariance_eq
    {κ : Type*} [Fintype κ] (μ ν : Measure (κ → ℝ)) [IsGaussian μ] [IsGaussian ν]
    (hmean : (∫ x, x ∂μ) = ∫ x, x ∂ν)
    (hcov : ∀ i j, cov[fun x => x i, fun x => x j; μ] =
      cov[fun x => x i, fun x => x j; ν]) : μ = ν := by
  let L : (κ → ℝ) ≃L[ℝ] EuclideanSpace ℝ κ :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)).symm
  apply L.toHomeomorph.measurableEmbedding.map_injective
  change μ.map L = ν.map L
  apply IsGaussian.ext
  · change (∫ x, x ∂μ.map L) = ∫ x, x ∂ν.map L
    rw [L.integral_id_map, L.integral_id_map, hmean]
  · have hμ (i : κ) : MemLp (fun x : κ → ℝ => x i) 2 μ :=
      (IsGaussian.memLp_two_id (μ := μ)).eval i
    have hν (i : κ) : MemLp (fun x : κ → ℝ => x i) 2 ν :=
      (IsGaussian.memLp_two_id (μ := ν)).eval i
    ext x y
    change covarianceBilin (μ.map (fun x => toLp 2 x)) x y =
      covarianceBilin (ν.map (fun x => toLp 2 x)) x y
    rw [covarianceBilin_apply_pi hμ, covarianceBilin_apply_pi hν]
    simp_rw [hcov]

end ProbabilityTheory.IsGaussian
