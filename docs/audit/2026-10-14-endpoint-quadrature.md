# Endpoint quadrature correspondence review

The intrinsic clauses and the actual Jacobi border route are now checked against
finite polynomials, positive measures, and constructed moment matrices:

- `integral_eval_eq_endpoint_quadrature_of_modified_orthogonality` and
  `integral_eval_eq_twoEndpoint_quadrature_of_modified_orthogonality` construct the
  integrated-cardinal rules from their modified-measure nodal orthogonality, with
  degree bounds below `2q+1` and `2q+2`, respectively.
- `exists_integral_sub_endpoint_quadrature_eq_iteratedDeriv_mul` and
  `exists_integral_sub_twoEndpoint_quadrature_eq_iteratedDeriv_mul` integrate the
  actual endpoint Hermite interpolants and prove the single-interior-point errors.
  The nodal factors are `(x-t)π(x)^2` and `(x-a)(x-b)π(x)^2`. The finite measure is
  concentrated on the closed interval; the interior nodes are distinct; all needed
  derivatives are differentiable on the open interval and the top derivative is
  continuous there. Both the one-node Radau and two-node Lobatto cases are included.
- `endpoint_quadrature_le_integral_of_iteratedDeriv_nonneg`,
  `integral_le_endpoint_quadrature_of_iteratedDeriv_nonneg`, and
  `integral_le_twoEndpoint_quadrature_of_iteratedDeriv_nonneg` preserve the source
  orientations: positive odd derivative gives left Radau lower and right Radau
  upper bounds; positive even derivative gives a Lobatto upper bound.
- `endpoint_quadrature_weight_pos_of_exact` proves all Radau weights strictly
  positive under at least `q+1` original support points. The Lobatto analogue,
  `twoEndpoint_quadrature_weight_pos_of_exact`, requires at least `q+2` support
  points and uses the nonnegative endpoint-weighted squared cardinal tests. This
  includes a terminal original atomic measure and does not assume the result.
- `integral_eval_measureT_eq_chebyshevLobattoRule` proves the actual first-kind
  Chebyshev rule with `N+1` nodes `cos(jπ/N)`, weights `π/N`, half weights at both
  endpoints, and degree `2N-1` exactness. Positivity, total mass, and complete
  discrete Chebyshev orthogonality through mode `N` are exported separately;
  modes `0,N` have squared norm `π`, and the other modes have squared norm `π/2`.

`TridiagonalPowers` proves the noncommutative power telescope and finite propagation
thresholds, without assuming symmetry. `JacobiBorders`, `RadauSchurBorders`, and
`LobattoSchurBorder` construct the actual Schur borders and prove endpoint spectrum
and matrix order. `LastResolvent`, `JacobiBorderCharpoly`, `RadauCornerFormula`, and
`LobattoCornerFormula` export the cofactor ratios, monic border recurrence, and
explicit corners and positive Lobatto coupling. `JacobiMoments` and
`EndpointJacobiMoments` give the original measure moment bridge and transfer the
moments through `2q` and `2q+1` to the constructed rules. `EndpointJacobiData` and
`EndpointJacobiWeights` prove the actual eigenvalue node sums, degree thresholds,
distinctness, positive first-coordinate weights, and total mass.

`JacobiOrder` and `EndpointJacobiLocation` derive interval location from original
measure support. `EndpointJacobiModified` identifies the actual remaining nodal
products with the canonical monic polynomials of the endpoint-modified functionals;
`PolynomialDensity` identifies those functionals with the native positive density
measures. `RadauJacobiRemainder` and `LobattoJacobiRemainder` prove the single-point
derivative errors and repaired signs for the actual matrices.
`EndpointMatrixBounds` specializes the signs to an original Hermitian operator
and starting vector, translating original support cardinality into Krylov grade.

The opposite-endpoint Radau termination branch is handled without endpoint derivative
jets. `integral_eq_radau_degree_rule_of_both_endpoints` uses its existing degree
threshold to integrate the nonnegative endpoint-weighted squared remaining nodal
polynomial to zero. The original measure is consequently concentrated on those
nodes and every function is integrated exactly. `RadauRuleRemainder` retains the
single-point formula with zero signed nodal norm in that branch.

The original blanket `q+1 <= grade` assumption is insufficient for a
nondegenerate `(q+2)`-node Lobatto construction: a measure on exactly `q+1`
atoms including both endpoints leaves only `q-1` atoms after multiplying by
`(x-a)(b-x)`. The natural condition is positive definiteness of the appropriate
modified moments, with at least `q+2` original support points as a clean
sufficient premise; smaller terminal rules need an explicit termination branch.
The precise positive-definite Schur-shift interface is exported separately from the
clean sufficient support condition. Zero measures, coincident interval endpoints,
and smaller atomic Lobatto termination use intrinsic exact rules rather than a
nondegenerate Schur construction. No theorem asserts the positive `(q+2)`-node
Lobatto construction under the false blanket `q+1 <= grade` assumption.

The monic Radau corner uses the minus sign in
`a - beta_q^2 * chi_{q-1}(a) / chi_q(a)` when
`chi_q(t) = det(tI-T_q)`. The even/odd derivative sign orientations above follow
from the source nodal factors and are independent of this realization convention.

The boundary promises also have explicit constructors. `EndpointDegenerate` exports
the two affine weights for `q=0`, their nonnegativity, exact affine integration and
total mass, including a weight zero or the zero measure. A coincident-endpoint
interval has its exact one-node mass rule. `EndpointTermination` constructs the
actual canonical terminal Gauss fallback from the original support cardinality; it
integrates arbitrary functions without smoothness or assumed output exactness.
`EndpointJacobiSigns` exports all three reversed bounds for nonpositive derivatives.
`EndpointJacobiOrthogonality` gives the general polynomial pairing identity whenever
the degree sum lies within the Lobatto exactness threshold.
