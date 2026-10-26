import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileRealUpper
import NLAlib.RandomMatrix.Gaussian.Moments.SymmetricProfileLowerMoments

/-!
# Sharp Schatten moments of heterogeneous symmetric Gaussian matrices

The actual independent lower-triangular Gaussian construction satisfies the
two-sided variance-profile estimate for every real exponent at least two.
The constants `1/100` and `512` are uniform in the dimension, the exponent,
and the coefficient profile. The Schatten norm is unnormalized.

For a nonnegative profile, the `Pi` norm `‖b i‖` is precisely the maximum
coefficient in row `i`; it is zero for an empty row. All finite Schatten
moments of this ensemble are integrable by the lower-moment module.

Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Theorem 1.1,
first estimate, pages 2--3. The proof uses the weighted graph method,
Gaussian even-moment comparison, and finite-dimensional interpolation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

namespace NLAlib

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- Sharp two-sided Schatten moments for the actual heterogeneous symmetric
Gaussian ensemble, for every real `p ≥ 2`. Both constants are universal,
and the exact row-variance and row-maximum profiles appear. Zero coefficients
and empty dimensions are included; no moment estimate is assumed.
Source: Latała--van Handel--Youssef, arXiv:1711.00807v2, Theorem 1.1,
first estimate, pages 2--3.
atlas: heterogeneous-gaussian-schatten-moments -/
theorem integral_schattenNorm_symmetricGaussianMatrix_rpow_root_bounds
    (b : Matrix n n ℝ) (hb : b.IsSymm) (hb0 : ∀ i j, 0 ≤ b i j)
    {p : ℝ} (hp : 2 ≤ p) :
    (1 / 100 : ℝ) *
        ((∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹ +
          Real.sqrt p * (∑ i, ‖b i‖ ^ p) ^ p⁻¹) ≤
      (∫ G, schattenNorm (symmetricGaussianMatrix b G) (ENNReal.ofReal p) ^ p
        ∂gaussianMatrix n n) ^ p⁻¹ ∧
    (∫ G, schattenNorm (symmetricGaussianMatrix b G) (ENNReal.ofReal p) ^ p
        ∂gaussianMatrix n n) ^ p⁻¹ ≤
      512 * ((∑ i, (∑ j, b i j ^ 2) ^ (p / 2)) ^ p⁻¹ +
        Real.sqrt p * (∑ i, ‖b i‖ ^ p) ^ p⁻¹) :=
  ⟨row_profile_le_integral_schattenNorm_symmetricGaussianMatrix_rpow_root b hb hb0 hp,
    integral_schattenNorm_symmetricGaussianMatrix_rpow_root_le b hb hb0 hp⟩

end NLAlib
