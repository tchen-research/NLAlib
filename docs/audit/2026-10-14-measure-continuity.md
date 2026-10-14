# Actual-measure continuity under finite moment convergence

`Polynomial/OrthogonalPolynomials/MeasureContinuity.lean` proves every conclusion
of `recurrence-coefficient-continuity` for the existing native measure objects.
Only the first `2n` monomial moments must converge. The actual limiting measure
has at least `n` support points; the original stronger hypothesis of more than
`n` points is therefore included. Measures have `HasPolynomialMoments`, which
follows from finite mass and support in a compact interval. Finite mass must be
explicit in the informal compact-support statement: compact support alone does
not make an infinite positive measure's moment integrals finite.

The bridge puts each measure's first `2n` moments in the finite coordinate vector.
All canonical quantities are unchanged by truncation, including early singular
systems. The finite coordinate functional is smooth for every fixed polynomial,
so the checked inversion, norm-quotient, Jacobi eigenvalue, and cardinal-weight
continuity theorems can be composed with moment-vector convergence. These proofs
derive the requested convergence; none assumes convergent coefficients, nodes,
weights, or an arbitrary smooth family of representing measures.

The endpoints give each monic polynomial coefficient through order `n`, included
squared norms and monic recurrence coefficients, uniform polynomial convergence
on any bounded set and on each fixed compact interval, spectral-norm Jacobi
matrix convergence, and canonically ordered actual Gauss node and weight
convergence. The native order-zero recurrence coefficient is the constant zero
boundary convention. The source's optional convention assigning the zeroth
moment to a coefficient is covered by the moment hypothesis separately.

Convergence of the actual Hankel determinant also makes the approximating
measure Hankel systems eventually positive definite. Their positive
semidefiniteness is supplied by the actual positive measures, so a positive
determinant suffices; no positivity certificate for nearby arbitrary moments is
assumed. This permits early measures with too few support points and includes
the limiting terminal atomic case. At order zero the determinant is one,
polynomial convergence is the constant polynomial one, and all coefficient,
node, and weight assertions with index below zero are empty.

The direct Lean check passed without warnings. Repository-wide build, trusted
audit, declaration extraction, and atlas synchronization remain the integrating
parent's checks before its PR. The full reviewed proof inventory is in
`2026-10-14-measure-continuity-proof-family.json`.
