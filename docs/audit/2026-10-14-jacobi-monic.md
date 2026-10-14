# Jacobi and monic recurrence correspondence review

The finite Jacobi and monic recurrence routes now use the actual matrix and
measure objects. The reviewed families are recorded in the adjacent JSON file.
Direct Lean checks passed for the new algebra, normalized coefficient, kernel,
complex fraction, second-kind resolvent and actual signed Lanczos bridges.
Repository-wide trust and integration checks are the separate final verification.

`JacobiAlgebra` owns the shared field-generic matrix, finite fraction, coefficient
shifts and determinant recurrence at matrix layer zero. The real positivity and
Lanczos consumers retain their old public names and imports. The generic complex
fraction algebra lives beside it at matrix layer zero. `JacobiContinuants`
constructs the actual polynomial denominators and identifies them with matrix
characteristic polynomials; no equivalence is assumed.

The complex literal fraction requires a nonreal argument. Every real symmetric
trailing block then has nonzero determinant, and each scalar Schur denominator
is proved nonzero. The trailing/full determinant quotient covers every final
pole-free complex argument, including real intermediate fraction poles. The
original mass times the canonical complex Jacobi resolvent is the actual
second-kind ratio at every point off its actual node spectrum. A proved matrix
realization identifies the canonical compression with its alpha/square-root-beta
coefficient matrix and derives its ordinary nonreal continued fraction. Canonical
rooted moment identities prove its finite moment matching. Squared first
eigenvector coordinates are the weights for the normalized measure
μ_b/‖b‖²; multiplying by ‖b‖² restores the original-measure weights and
Stieltjes approximant. The actual Lanczos polynomials are orthonormal for
μ_b itself. These finite results make no claim of infinite continued-fraction
convergence or a general Jordan-contour analytic interface.

The monic recurrence coefficient beta is a norm ratio; the normalized positive
Jacobi off-diagonal is its square root. An arbitrary signed Lanczos off-diagonal
need not be positive: its square is the same monic beta. Generic norm products,
actual signed matrix norm products, normalized recurrence and both monic and
normalized confluent kernels preserve this distinction.

Two index and boundary corrections are essential for the informal cards:

- A size-q decomposition stores beta_j only for 0 < j < q, and its total beta_q
  is zero. The monic norm quotient formula at a nonterminal order q needs the
  next decomposition/coupling. For example, diag(0,1), seed (1,1), q=1 has
  characteristic polynomial t-1/2 and squared norm 1/2; using the absent total
  beta_1=0 would incorrectly give zero. The exported norm and coefficient
  identities use stored indices; exact-grade termination is a separate zero
  norm and zero beta branch. The characteristic recurrence through the final
  polynomial only uses the preceding stored coefficients and is fully included.
- At zero top monic norm, use the confluent Wronskian divided by the preceding
  positive norm. A normalized terminal polynomial does not exist. The fully
  normalized formula requires the displayed top norm to be positive. The
  recurrence boundary beta_0 is zero; the norm-product initial factor h_0 is the
  original mass and must not be confused with that boundary coefficient.

The alpha quotient requires a positive monic norm, so the actual size-q
identification is stated at j<q. There is no quotient at the zero-norm
terminal polynomial. Multiplied Christoffel–Darboux holds for every x,y;
division requires x≠y, and the positive confluent kernel requires a nonempty
prefix. The actual signed normalized formula uses 1≤m<q.

Actual consecutive leading Lanczos compressions strictly interlace whenever
the larger valid decomposition exists. The larger order may be exactly the
Krylov grade. With descending eigenvalues, the precise order is
θ_i(T_(q+1)) > θ_i(T_q) > θ_(i+1)(T_(q+1)), for 0≤i<q. No strict
interior-support-location assertion is made at termination.

The review helper installs these measure, coefficient, denominator and boundary
conventions in the human atlas statements as well as the proved family. Order
zero has scalar fraction zero and characteristic denominator one, with no
first-coordinate expression.
