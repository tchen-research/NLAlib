# Status sanity check outside the matrix catalogue

This review searches every nonproved atlas entry outside the matrix areas for
an existing sorry-free, partial NLAlib formalization, then compares the human
whole contract with the actual Lean signatures. It records existing proofs and
remaining gaps; it adds no theorem and does not weaken a Lean statement.

The inventory contains **15 entries**: **13 candidates** and **2 scaffolds**.
One candidate, `slq-error`, has complete collective coverage. The other twelve
candidates have concrete remaining clauses or generality gaps. Both scaffolds
have indexed sorry-dependent declarations for essential parts of their contracts.
The two deliberately excluded sharp rational-asymptotic problems are untouched
and are outside this partial-proof inventory.

## Complete collective coverage

### `slq-error`

The human contract already describes supplied orthonormal compression frames
containing each probe's Krylov space; it does not assert a construction algorithm
or matvec count. The existing family covers that exact contract:

- `abs_compressionQuadratureEstimate_sub_hutchinsonEstimate_le` gives the
  deterministic polynomial quadrature comparison.
- The `SLQAnalytic` and `SLQLipschitz` tails use the actual joint Rademacher law,
  the advertised additive constants `4nM ρ^(1−2q)/(ρ−1)` and
  `πLn(c−a)/(4q)`, and the Hanson–Wright coefficient `1/(256e²)`.
- `SLQRademacher` and `SLQAnalytic` supply the relative `1024e²` sample budget,
  under positive semidefiniteness and positive trace of the matrix function.
- `SLQAnalyticSteps`, `SLQLipschitz`, and `SLQPositiveLowerBound` supply the
  logarithmic analytic order, absolute and Lipschitz order variants, and the
  positive scalar lower-bound replacement for the trace-dependent order.
- The separate inverse quadrature comparison gives its specific Chebyshev
  endpoint-ratio rate without replacing general analytic parameters by a
  condition number.

Every selected declaration is already tagged for `slq-error` and indexed
sorry-free. Main tails permit empty ambient indices; positive-trace variants
necessarily exclude them. There is no upper bound on `q` or assumed relation
between `q` and compression-frame width, so saturation and approximation orders
above the ambient dimension are included whenever the supplied frame contains
the Krylov space. The old note that general analytic functions await
`bernstein-ellipse-approx` is stale: that approximation dependency and the actual
analytic SLQ consumers are proved.

## Candidates with actual remaining gaps

| Atlas id | Existing coverage | Remaining whole-contract gap |
| --- | --- | --- |
| `nystrom-randomized` | Gaussian expected trace error for `A = FᵀF`, bounded by the factor's optimal squared Frobenius tail | The final advertised nuclear-error theorem and identification of the factor tail with the PSD matrix's optimal nuclear tail are absent. The PSD trace/nuclear helper exists, but the complete bridge is not exposed. |
| `xtrace-unbiased` | Conditional unbiasedness of abstract held-out deflation statistics | Independence of the concrete measurable leave-one-out construction from the held-out iid probe, product-law integrability, and the individual-estimate contract still need discharge from the advertised assumptions. |
| `hutchpp-unbiased` | Fixed orthonormal deflation is fully unbiased; independent random deflation is unbiased given product-law integrability | The random-basis theorem assumes integrability of the full estimator under the product of the sketch and probe laws; this is not yet derived from measurable orthonormal construction and isotropic second moments. |
| `krylov-grade` | Real grade by power dependence, dimension, saturation, invariance, zero criterion, and finite termination | General-field vector-relative monic minimal polynomial and its divisibility into the matrix minimal polynomial remain absent. A degree bound is not the stated polynomial-divisibility claim. |
| `residual-polynomial` | Real residual and error polynomial algebra, realizability, and invertible-matrix iff | The set-dependent minimax quantity's monotonicity and attainment remain unformalized. Its advertised arbitrary-matrix iff also needs correction, as explained below. |
| `gmres-def` | Real variational existence, uniqueness, polynomial form, monotonicity, and finite termination | The advertised complex form is missing. The real reduced Arnoldi least-squares clause exists under the separately proved `gmres-arnoldi-form` entry, so the note calling that clause open is stale. |
| `gmres-diagonalizable` | Real diagonalization with a real eigenvector matrix and real spectrum | The stated complex diagonalization of a real nonsymmetric matrix and its complex-spectrum condition-number bound are missing. |
| `minres-bound` | Hermitian spectral polynomial bound and definite Chebyshev rate | The explicit equal-width indefinite two-interval MINRES rate is not exposed. The polynomial `two-interval-minimax` prerequisite is now proved, but that does not by itself make the consumer's missing bound a declared theorem. |
| `fom-def` | FOM Galerkin condition is the small square system; for SPD matrices it gives a CG iterate | Unique existence iff the small matrix is invertible, the explicit inverse formula, and the stated last-basis-vector residual formula are not exposed. |
| `chebyshev-iteration` | Polynomially defined iterate, residual and energy rates, first step, and an equivalent three-term recurrence | The supplied two-term `ρ_k,d_k` algorithm is not formally connected to that polynomial iterate, and the sharper reciprocal-Chebyshev residual bound is not exposed under this entry. The note saying no three-term recurrence exists is stale. |
| `richardson-iteration` | Unpreconditioned polynomial iteration, weighted norm bounds and optimal step | General SPD preconditioner, both energy norms, and the corresponding preconditioned recursion bridge remain absent. |
| `jacobi-matrix-identities` | Golub–Welsch, polynomial quadrature, Christoffel–Darboux, non-strict interlacing, and real above-spectrum continued fraction | Strict Jacobi interlacing and the unrestricted resolvent/continued-fraction domain are not established by the current family. |

### Residual-polynomial metadata correction

The current informal statement advertises
`x − x₀ ∈ K_q(A,r₀) ↔ ∃ p, residual = p(A)r₀` without assuming that `A` is
injective. This is false: with `A = 0`, zero right-hand side, `x₀ = 0`, and
`x ≠ 0`, the residual condition holds for `p = 1`, while the Krylov space is
zero. The Lean theorem `sub_mem_krylovSpace_iff_exists_sub_mulVec_eq` correctly
assumes `IsUnit A`.

The corrected human contract distinguishes the always-valid forward implication and
existence of an affine-Krylov representative for every residual polynomial from
the iff for a specified `x` under invertibility. This corrects the statement
rather than weakening a Lean theorem. The item remains candidate because its
minimax-quantity clauses remain open.

The stale SLQ, GMRES, Chebyshev recurrence and MINRES prerequisite notes are also
updated in this change; these note corrections do not discharge the genuine gaps
listed above.

## Genuine scaffolds

- `partial-cholesky-nystrom`: recursion, residual PSD and pivot zero conditions
  are proved, but the factor/Nyström and residual/Nyström identification
  declarations still depend on `sorry`.
- `cg-recurrence`: nonbreakdown before the real grade is proved, but mutual
  residual orthogonality, direction conjugacy, span descriptions, and algorithm
  realization as `IsCGIterate` remain sorry-dependent.

