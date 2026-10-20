import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteRootComparison
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeMomentEndpoints
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeNativeMomentLimit

/-! # Actual Gaussian-to-free rooted resolvent moment comparison

The finite interpolation inequality passes to the genuine native free endpoint.
No limit law or moment comparison is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Kronecker Topology
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d]
  [DecidableEq ι] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- The actual original Gaussian and native free resolvent Gram moments differ
by the dimension-free finite interpolation error.

Source: Brailovskaya--van Handel, arXiv:2108.06312v2, Theorem 6.2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem abs_gaussian_wordNative_resolventEvenMoment_rpow_sub_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) {p : ℕ} (hp : 0 < p) :
    |(∫ x : ι → ℝ, resolventEvenMoment (A₀ + ∑ i, x i • A i) ζ p
        ∂gaussianVector ι) ^ (1 / ((2 * p : ℕ) : ℝ)) -
      ((wordMatrixVacuumExpectation
        ((star (resolvent (wordNativeMatrixLinearCombination A₀ A) ζ) *
          resolvent (wordNativeMatrixLinearCombination A₀ A) ζ) ^ p)).re) ^
            (1 / ((2 * p : ℕ) : ℝ))| ≤
      ((2 * p + 1) * (2 * p + 2) ^ 2 : ℕ) *
        (specNorm (coefficientVariance A) * specNorm (coefficientCovariance A)) *
        (|ζ.im|⁻¹) ^ 5 := by
  have ht := (tendsto_const_nhds (x :=
    (∫ x : ι → ℝ, resolventEvenMoment (A₀ + ∑ i, x i • A i) ζ p
      ∂gaussianVector ι) ^ (1 / ((2 * p : ℕ) : ℝ)))).sub
      ((tendsto_integral_gaussianFreeFinite_resolventEvenMoment A₀ hA₀ A hA hζ p hp).rpow_const
        (Or.inr (by positivity : (0 : ℝ) ≤ 1 / ((2 * p : ℕ) : ℝ))))
  apply le_of_tendsto ht.abs
  apply Filter.Eventually.of_forall
  intro N
  have hb := abs_integral_gaussianFreeFinite_resolventEvenMoment_rpow_sub_le
    (n := Fin (N + 1)) A₀ hA₀ A hA ζ hζ hp
  dsimp only at hb
  rw [integral_gaussianFreeFinite_resolventEvenMoment_one A₀ hA₀ A hA ζ hζ p] at hb
  exact hb

end NLAlib
