# Retained approximation contracts

The reciprocal exponential clauses are complete. The best error is the infimum
of actual attainable uniform bounds for the canonical `RatFunc ℝ` class with
native numerator degree at most zero, denominator degree at most `n`, and no
denominator zero on the positive half-line. The finite weighted-minimax lower
certificate and the explicit two-resolvent upper denominator give the exact
`n`th-root limit `1/3`. The type-`(n,n)` Halphen equivalent remains outside the
user's requested formalization scope.

The explicit denominator is the source's rational finite derivative sum. Its
degree, positivity, positive derivative, and uniform bound are all proved for
the actual polynomial. The tail proof uses a simpler finite algebraic route:
the Rodrigues commutator proves the classical monic Laguerre recurrence, and
coefficient induction after translation by `4n` proves the signs of all
derivatives. This establishes the whole half-line and does not assume a
positivity certificate. The operator corollaries use the actual matrix
exponential, inverse polynomial, positive definiteness, and spectral norm over
arbitrary `RCLike` scalars and arbitrary finite matrix labels, including empty
dimensions.

The original atlas describes `exp(x)` on the negative half-line; the supplied
reroute uses `exp(-t)` on the positive half-line. The checked rational reflection
leaf proves exact equality of their native attainable-error sets and infima,
and exposes the geometric bounds and root limit directly in the atlas's
negative-half-line orientation. The affine bijection preserves the canonical
rational degree budgets and absence of poles. The polynomial best-error clause
also has a direct negative-half-line endpoint: the least attainable bound is
one half at every degree.

The polynomial Bernstein route now proves the actual finite degree-transfer
inequality and full convergence of `n * absoluteMinimaxError n` to the real
constant defined by its even-degree liminf. The checked finite Fejér dual lower
certificate proves strict positivity and encloses the constant between
`1/(18π)` and `2/π`. The finite parity reduction `E_(2m+1)=E_(2m)` is also
proved by polynomial symmetrization, independently of the sequence convergence
argument. No numerical value of the Bernstein constant is formally claimed.
The user-excluded Stahl rational equivalent is outside scope.

Every completed endpoint and dependency has passed an individual Lean check.
Fresh endpoint checks on 2026-10-14 include the actual rational root limit,
negative-half-line reflection, positive Bernstein enclosure, parity reduction,
half-line polynomial least error, and PSD operator bound. The fresh positivity
check exposed a final lambda-reduction rewrite issue in the limit-to-lower-bound
bridge; it was repaired without changing the theorem statement.
An independent direct theorem-contract review confirmed actual canonical
rational numerator normalization, the zero-numerator branch, nonempty bounded
infima, degree-zero behavior, source/target scaling exclusions, and the empty
matrix case. The repository-wide build and audit remain the integrating parent
task's required checks before creating and merging its pull request.

The proof inventory in `2026-10-14-reciprocal-proof-family.json` records complete
coverage of the retained clauses only. It must not be installed as a complete
atlas proof family for either composite card: both cards retain user-excluded
sharp rational asymptotics, and their Lean endpoint tags accurately remain
partial.
