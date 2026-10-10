import NLAlib.Gaussian.InverseMoments.HardEdgeEndpoint
import NLAlib.ForMathlib.MeasureTheory.WeightedWeakDensity
import NLAlib.Gaussian.InverseMoments.UnshiftedWeakInequality

/-!
# Closing the operator hard-edge argument

The scalar Gaussian weak inequality produces a genuine antitone weighted
density, and the checked Mellin endpoint argument gives the exact Edelman
constant. This module connects those two proved interfaces.

Atlas: wishart-lambda-min-tail and pinv-spectral-tail.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff Matrix

namespace NLAlib

/-- The operator weak inequality suffices for the exact integrated Edelman
bound. Source: Gaussian operator differentiation, scalar weighted density,
and Mellin endpoint rederivations; atlas wishart-lambda-min-tail.
atlas: wishart-lambda-min-tail -/
theorem gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral_of_weak_inequality
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi 0 → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x in Ioi 0, 4 * x * deriv ψ x +
        2 * (((k : ℝ) - r + 1) - x) * ψ x
        ∂((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2)))
    (t : ℝ) :
    (gaussianMatrix r k) {G | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t} ≤
      ∫⁻ y in Ioc (0 : ℝ) t, ENNReal.ofReal
        ((2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2) /
          (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))) *
          y ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-y / 2)) := by
  obtain ⟨h, hh, hanti, hnn, hdens⟩ :=
    exists_gamma_weighted_antitone_density_of_weak_inequality
      ((gaussianMatrix r k).map (fun G => sigmaMin (Matrix.of G)ᵀ ^ 2))
      ((k : ℝ) - r + 1) hweak
  have he : ((k : ℝ) - r + 1) / 2 - 1 = ((k : ℝ) - r - 1) / 2 := by ring
  simp_rw [he] at hdens
  exact gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral_of_antitone_density
    hr hrk h hh hnn hanti hdens t

/-- The exact integrated Edelman bound follows from Gaussian operator
differentiation and the scalar Mellin endpoint. Source: operator hard-edge
rederivation, with no joint eigenvalue density; atlas wishart-lambda-min-tail.
The positive threshold hypothesis matches the published statement.
atlas: wishart-lambda-min-tail -/
theorem gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral_operator
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (t : ℝ) (_ht : 0 < t) :
    (gaussianMatrix r k) {G | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ t} ≤
      ∫⁻ y in Ioc (0 : ℝ) t, ENNReal.ofReal
        ((2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2) /
          (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))) *
          y ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-y / 2)) := by
  apply gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral_of_weak_inequality hr hrk _ t
  intro ψ hψ hψc hψs hψ0
  exact integral_sigmaMin_transpose_sq_law_unshifted_weak_nonneg_gaussianMatrix
    hr hrk ψ hψ hψc hψs hψ0

end NLAlib
