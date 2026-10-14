# Christoffel kernel and graded conjugate-direction audit

The corrected `kernel-polynomials-christoffel` contract is covered by exact
finite algebra and native spectral-measure consumers. The polynomial quotient
is the canonical monic polynomial of the `X-z` weighted functional; its norm is
`q_n h_n`; the reproducing-kernel identity includes evaluation at `z`. The
original quotient/elimination identities and the transformed recurrence
identities preserve the monic convention.

The initial coefficient and matrix factorization interfaces required global
quasi-definiteness and nonvanishing in every degree. Those assumptions cannot
be instantiated for finite spectral measures. The added finite-order interfaces
need only Hankel systems and evaluations through the actual requested order.
The transformed diagonal is proved directly from
`(X-z) hatP_n = P_(n+1) + q_n P_n`: its numerator is
`h_(n+1) + q_n^2 h_n + z q_n h_n`. This proves `z+q_n+e_n` even when the next
original squared norm is zero at finite-support termination. The original
global factorization names remain as corollaries of the finite interfaces.

The finite reversed-factor formula includes the exact last-coordinate
correction. Its equal-size uncorrected version is false. The zero size is
handled by empty matrices. No native finite factorization theorem requires an
infinite extension of an atomic moment functional.

For real positive measures the diagonal kernel is strictly positive, since its
sum consists of nonnegative squared terms and the constant term is positive.
Consequently the real transformed value at `z` is nonzero whenever the original
denominator is nonzero. Exterior real support intervals derive that denominator
condition, including terminal atomic polynomials. The arbitrary complex
transformed nonvanishing assertion remains false and is not formalized.

The actual spectral `X`-weighted functional equals the matrix energy pairing
of polynomial Krylov vectors. An SPD matrix makes it positive definite through
the vector's Krylov grade and derives every original zero-shift denominator.
The actual Christoffel vector before termination is nonzero, lies in the next
Krylov space, and is `A`-orthogonal to the preceding space. The vectors are
mutually `A`-conjugate, and every nonzero direction satisfying those graded
conditions is a nonzero scalar multiple of the actual kernel vector. This
establishes the mathematical CG direction interpretation up to individual
normalization. It does not identify the still-experimental Hestenes–Stiefel
recursion's normalization or certify its procedural coefficient recovery.

The symmetric Jacobi LDL clause has an actual recursive scalar pivot,
`d_0=alpha_0`, `d_(j+1)=alpha_(j+1)-a_(j+1)^2/d_j`, and unit lower bidiagonal
factor. Matrix positive definiteness derives positivity of every pivot. The
actual Lanczos compression has the corresponding positive pivots and exact
LDL transpose factorization, supplied by the integrating parent's checked leaf.

The standalone spectral-moment/grade helpers were moved into `SpectralMoments`
without changing declaration names. Pure Christoffel spectral consumers import
that smaller leaf, independently of a procedural Lanczos or CG scaffold. The
existing `MomentOrthogonality` consumer imports the shared helpers.

The new and revised Christoffel leaves passed direct Lean checks and exports
without warnings. Existing Christoffel kernel and finite bidiagonal consumers
also passed fresh checks. Repository-wide checks and the post-split Lanczos
consumer build remain the integrating parent's checks.
