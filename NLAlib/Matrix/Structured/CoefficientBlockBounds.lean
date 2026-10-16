import NLAlib.Matrix.Structured.CoefficientBlockCompression
import NLAlib.Matrix.Structured.CoefficientBlockCommuting

/-! # Variance and covariance bounds for the coefficient-block parameter

The largest eigenvalue is nonnegative even though the coefficient block can
be indefinite. The two actual swap compressions bound its full spectral
norm, and hence its square-root parameter, by both source parameters.
Source: Bandeira et al. (2026), §1.1, Propositions 1.3–1.4.
-/
noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

/-- Full finite bounds for the actual coefficient block and its largest-
eigenvalue parameter, with the original Hermitian hypotheses alone.
Source: Bandeira et al. (2026), §1.1, Propositions 1.3–1.4.
atlas: coefficient-block-partial-transpose (partial) -/
theorem coefficientBlock_variance_covariance_bounds [Nonempty ι] [Nonempty d]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (coefficientBlock A).IsHermitian ∧ 0 ≤ lambdaMax (coefficientBlock A) ∧
      specNorm (coefficientBlock A) ≤
        min (specNorm (coefficientVariance A)) (specNorm (coefficientCovariance A)) ∧
      coefficientBlockKappa A ≤
        min (Real.sqrt (specNorm (coefficientVariance A)))
          (Real.sqrt (specNorm (coefficientCovariance A))) := by
  have hH := isHermitian_coefficientBlock A hA
  have hV := specNorm_coefficientBlock_le_variance A hA
  have hC := specNorm_coefficientBlock_le_covariance A hA
  refine ⟨hH, lambdaMax_coefficientBlock_nonneg A hA, le_min hV hC, le_min ?_ ?_⟩
  · exact Real.sqrt_le_sqrt (hH.lambdaMax_le_specNorm.trans hV)
  · exact Real.sqrt_le_sqrt (hH.lambdaMax_le_specNorm.trans hC)

end NLAlib
