# Independent source review of moments, sensitivity, and Hankel formulas

Reviewed against the retained operator re-derivations, AQ22--AQ31 and OF4--OF6.
The revised atlas statement uses monic sensitivity formulas, which are the
formulas actually established by the proof family.

## Continuity: complete selected source contract

`MeasureContinuity` proves the conclusions from convergence of just the actual
first `2n` monomial moments of positive measures. No polynomial, coefficient,
matrix, node, weight, derivative, or nondegeneracy convergence is assumed.
`MomentTruncation` supplies exact native-data equalities for all polynomials
through order `n`, norms and alphas/betas below `n`, the native normalized
Jacobi matrix, and the canonically indexed nodes and integrated-cardinal
weights. The limiting support threshold `n ≤ support.encard` suffices; it
allows a terminal finite-support polynomial. Early approximating systems may
be singular. `eventually_posDef_hankelMomentMatrix_of_moment_convergence`
derives eventual positive definiteness from actual determinant convergence
and positive-measure semidefiniteness. Uniform polynomial convergence on
bounded real sets and spectral-distance Jacobi convergence are explicit.
The integrated-cardinal argument for weights is an equivalent finite
Vandermonde solve and does not assume continuous eigenvectors.

## Sensitivity: missing native fixed-basis bridge repaired

The original generic `MomentCoordinates` and `MomentJacobian` proofs correctly
establish finite coordinate derivatives, but their arbitrary functionals `c`
alone did not expose the source's actual prescribed polynomial basis. The
following checked modules now construct and connect that interface:

- `ForMathlib/LinearAlgebra/PolynomialDegreeLT`: canonical coefficient
  truncation and a linear projection to the native `Polynomial.degreeLT`
  submodule, equal to the identity on bounded-degree polynomials.
- `OrthogonalPolynomials/MomentBasis`: any actual native fixed basis's duals
  are constructed by composing its coordinate maps with the projection.
  The input vector is exactly `L(b_k)`; its reconstructed chart equals `L`
  on every polynomial of degree below the coordinate dimension. Arbitrary
  vectors give precisely their prescribed basis moments as well.
- `OrthogonalPolynomials/MomentBasisData`: for coordinate dimension at least
  `2n`, this chart gives exactly the original finite Hankel system, norms,
  included alphas/betas, Jacobi matrix, and native Gauss nodes and weights.
- `OrthogonalPolynomials/SensitivityDegree`: the actual alpha sensitivity has
  degree at most `2j+1` and the beta sensitivity degree at most `2j`.
- `OrthogonalPolynomials/MomentBasisSensitivity`: at the actual modified
  moment vector on the original positive Hankel domain, the recurrence map
  is the original alpha-then-mass-and-beta output and its Euclidean Jacobian
  is the fixed basis's actual expansion coefficients of the source
  sensitivity polynomials. Absolute and normwise relative condition numbers
  use the actual spectral norm and the stated input/output norm factor.

The highest alpha row has degree at most `2n-1`, so no moment of degree `2n`
or next-order norm is introduced. The mass slot is `L(1)`; the library's
zero-order recurrence beta is the boundary `0` and is not substituted into
that slot. For `n > 0`, positive definiteness proves both the moment input
and the recurrence output nonzero, so their normwise normalization is
mathematically defined. The generic total formulas still cover order zero.

`MomentDerivative`, `NormSensitivity`, and `OrthogonalitySensitivity` derive
actual polynomial coefficient derivatives and differentiated orthogonality
from finite inverse systems and the product rule. The generic smooth-family
helpers assume only actual moment derivatives; the affine coordinate map
constructs those derivatives, so the final Jacobian does not assume its
conclusion. The adjacent monic alpha form has the correct omitted previous
term at order zero, and its highest included row needs only the order-`n`
positive Hankel system. Normalized neighboring-polynomial notation is an
optional presentation requiring those norms; it is not the revised card's
source contract.

## Hankel formulas: complete selected source contract

The finite bilinear squared form is the actual Hankel quadratic form over an
arbitrary field. `MomentPositivity` connects positive-measure square forms,
support thresholds, positive definite matrices, and leading determinant
positivity. `HankelNorms` diagonalizes the actual Hankel matrix by the unit
upper triangular monic coefficient matrix and proves determinant products,
successive norm quotients, and positive-order beta determinant quotients.
`HankelDeterminants` proves the actual normalized bordered determinant and
the precisely indexed shifted determinant: columns `0,...,k-2,k`, with
`E_0=0`. The alpha sign and difference of successive shifted quotients are
correct. `SpectralMoments` supplies the actual spectral measure's Krylov
Gram and grade equivalence. Empty determinants, terminal zero beta, and
required denominator hypotheses agree with the revised card; a normalized
terminal polynomial or terminal alpha is not asserted.

All five added Lean modules were checked directly and exported without
warnings. They introduce no axioms, scaffolds, `sorry`, or `native_decide`.
