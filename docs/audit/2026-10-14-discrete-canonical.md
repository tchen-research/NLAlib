# Canonical finite discrete Jacobi construction

`Krylov/Quadrature/DiscreteCanonical.lean` constructs the actual square
evaluation matrix from the canonical normalized moment polynomials of the
diagonal spectral measure. Its entry is exactly
`sqrt(w r) * p_j(t r)`. The existing diagonal spectral-measure identity identifies
that measure with the supplied finite atomic measure.

Distinct real nodes and positive weights give full Krylov grade through the
existing weighted Vandermonde theorem. The actual spectral Hankel matrix is
therefore positive definite at the full order. Canonical normalized polynomial
orthogonality proves orthonormal columns of the evaluation matrix; square
dimension gives orthonormal rows. These hypotheses are derived from the atomic
data and do not assume a Lanczos decomposition or an arbitrary polynomial frame.

Direct finite moment pairing proves `Qᴴ diag(t) Q = J`, where `J` is the actual
canonical normalized multiplication matrix. This equality needs only
nonnegative weights, because it is a termwise identity for the total definitions.
Under the distinct-node positive-weight hypotheses and positive dimension, the
weight vector transforms to `sqrt(h_0) e_0`. Row orthogonality gives the exact
dual sum `sum_j p_j(t_r) p_j(t_s) = delta_rs / w_r`.

The empty measure has empty matrices and full grade zero. The first-coordinate
statement explicitly requires positive dimension. The reciprocal-weight dual
identity handles off-diagonal terms through a positive square-root product,
then uses `sqrt(w_r)^2=w_r` only on the diagonal.

These are the mathematical OF20–OF21 construction clauses. They carry no
procedural Stieltjes-algorithm or operation-count claim. The composite atlas
card must remain partial where it retains those algorithm clauses.

The completed leaf passed direct Lean checking and olean export without
warnings. The integrating parent runs the full repository checks and metadata
extraction before its PR.
