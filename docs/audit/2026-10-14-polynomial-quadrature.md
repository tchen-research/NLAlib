# Final polynomial and Krylov quadrature correspondence audit

This is the final statement readback for all 83 cards in the accompanying
2026-10-14-polynomial-quadrature.json. Its primary records are marked
audit_phase: final, with actual declaration names, current source signatures,
exact scope, reviewed clause inventories and current open clauses. Each
original record is preserved verbatim under baseline_audit; the original report
metadata and prose below are historical evidence. Earlier “no theorem”
findings are not current completion judgments.

The final outcomes are 72 matching primary contracts, 3 corrected matching
contracts, 5 partial composite contracts, 1 user-deferred target and 2 cards
outside the selected work.
These are audit outcomes for this report's 83 cards, not a count of all library
cards or an assertion that every original variant is formalized. The parent
task owns the repository-wide build, trusted-axiom audit, dependency-layer and
generated-index checks. This readback does not replace those checks.

## Final mathematical readback

General finite-moment mathematics remains in the layer-zero
Polynomial/OrthogonalPolynomials and Polynomial/Quadrature APIs; spectral and
signed-Lanczos consumers remain in Krylov/Quadrature. The final proofs derive
the canonical polynomials, matrix realizations, eigenvalue rules and
nondegeneracy they need rather than accepting their conclusions as certificates.

| Previously incomplete card | Final actual readback |
| --- | --- |
| chebyshev-extremal | Absolute iterated-derivative bounds hold for every order at x≥1; sharp scaled leading and degree-budget coefficient bounds include degree zero. Value extrapolation remains valid at both exterior sides. |
| jacobi-matrix-identities | First-coordinate squares integrate μ_b/M; original weights and finite second-kind resolvents multiply by M. Descending strict interlacing requires q+1≤grade. Signed normalized CD uses 1≤m<q; terminal monic kernels use preceding positive norms. Ordinary nested fractions need nonzero intermediate denominators; final pole-free determinant quotients cover real tail poles. |
| hankel-moment-positivity | The actual bordered polynomial determinant, precisely indexed shifted determinant, norm/alpha/beta ratios, Krylov Gram and grade equivalence complete the finite determinant contract. |
| gauss-quadrature-derivative-remainder | Actual Hermite interpolation and multiplicity Rolle yield single-interior-point integrated derivative errors and actual matrix quadratic-form remainders, with derived zero-norm terminal exactness. |
| gauss-radau-lobatto | Actual Schur borders, endpoint roots, monic ratio corners, moment matching, original-measure positive rules, modified nodal polynomials, derivative errors, sign bounds, degeneracies, discrete orthogonality and Chebyshev Lobatto rules are proved. |
| kernel-polynomials-christoffel | Finite quotient/norm/recurrence and real nonvanishing results, forward LU and boundary-corrected reversed UL, actual SPD graded-direction uniqueness and positive-pivot Jacobi/Lanczos LDL complete the corrected mathematical primary. |
| jacobi-fraction-second-kind | Actual complex divided-difference integrals, associated sequences, residues, exact Stieltjes cancellations, quantitative infinity bounds, locally uniform Markov convergence and exact atomic termination are proved. |
| symmetric-measure-even-odd-reduction | Native square and weighted-square pushforwards and actual rectangular-dilation spectral measures complete both normal-matrix reductions and augmented Lanczos even/odd characteristic-polynomial identities. |
| monic-orthogonal-recurrence | Characteristic recurrence and continuants include leading j≤q. Stored coupling squares and norm products use j<q; alpha quotients require positive norms. Exact-grade zero norms and beta are separate. Fully normalized top kernels require h_m>0; monic norm-divided kernels allow terminal top polynomials. |
| recurrence-coefficient-continuity | Actual first-2n-moment convergence gives determinant convergence even for singular limiting systems, and at limiting support size at least n gives coefficients, included norms/recurrence data, uniform polynomial convergence, spectral Jacobi and canonically indexed node/weight convergence; eventual positivity is derived. |
| recurrence-coefficient-moment-sensitivity | Constructed native basis duals at actual L(b_k) inputs reconstruct original finite data and give the actual basis sensitivity Jacobian, its representation coefficients and absolute/relative condition numbers. |
| christoffel-uvarov-modification | The corrected CU1–CU8 coefficient/remainder primary is complete. Native measure specialization uses finite mass and divided moments; the generic field determinant branch uses nonsingular finite Hankel systems without requiring a measure or positivity. Full/compressed systems, normalized determinants and actual modified recurrence coefficients are proved. |
| rational-gauss-quadrature | Finite positive measure, positive denominator, n≥1 and at least n support points give the actual divided-measure rule and converse. Generic repeated-pole decomposition, exact degree bounds and scalar conversion to 1+ζX complete the fixed-denominator primary. |

The JSON names all supporting declarations. Representative actual endpoints
are NLAlib.exists_integral_sub_gaussRule_eq_iteratedDeriv_mul_norm,
NLAlib.monicOrthogonalPolynomial_eq_inv_smul_det_borderedHankelMatrix,
NLAlib.tendstoUniformlyOn_secondKindPolynomial_div_stieltjesTransform,
NLAlib.euclideanJacobian_momentRecurrenceMap_polynomialBasis_eq,
NLAlib.monicOrthogonalPolynomial_eq_rationalModification_small_det_div and
NLAlib.rational_gauss_rule_of_positive_denominator. The actual generic
NLAlib.inv_smul_one_sub_map_apply_eq_sum covers all-complex off-spectrum
real-Hermitian spectral fractions; literal nested complex Jacobi fractions are
not equated with full resolvents at real intermediate tail poles.

The mathematical repairs remain explicit. Chebyshev aliasing uses frequency
fibers instead of double-counting endpoint branches. Original-measure weights
include starting-vector mass. Recurrence boundary β₀=0 is distinct from output
mass L(1). Monic beta is a norm ratio; the symmetric adjacent coefficient is its
square root, and an actual signed Lanczos basis can change its sign. Arbitrary
complex transformed Christoffel nonvanishing is false and is not asserted.
Positive reciprocal density needs denominator positivity, not just no poles.

Finite mass is explicit in the CU and rational-Gauss measure specializations:
compact support alone does not imply it. The generic CU coefficient/determinant
branch instead uses its actual finite nonsingular modified Hankel system over a
field, and the compressed original-basis branch needs its original finite prefix.
It does not require a representing measure or positivity on that generic branch.

For M=‖b‖²>0, squared first eigenvector coordinates are Gauss weights for
μ_b/M; multiplying by M restores the original measure. Actual Lanczos
polynomials remain orthonormal for μ_b. Consecutive descending spectra satisfy
θ_i(T_(q+1))>θ_i(T_q)>θ_(i+1)(T_(q+1)), requiring q+1≤grade; equality
of the larger order with the grade is allowed.

A size-q decomposition stores signed couplings a_j only for 0<j<q. Its total
absent a_q=0 cannot compute a nonterminal h_q. For diag(0,1), seed (1,1),
q=1, h_1=1/2 although D.beta 1=0. Stored norm products use j<q; the
characteristic recurrence still reaches j+1≤q using preceding coefficients.
Alpha quotients require h_j>0, and no terminal zero-norm alpha is asserted.
Signed normalized CD uses 1≤m<q. Monic norm-divided confluent kernels need
m>0 and preceding positive norms; fully normalized top-polynomial kernels
additionally require h_m>0.

These readbacks follow the corrected human atlas and current owning sources.
Final declaration extraction and atlas synchronization are still pending;
this update does not claim a fresh whole-index verification.

Radau corners use χ_j(t)=det(tI−T_j). Nonnegative odd derivatives give left
Radau lower and right Radau upper bounds; nonnegative even derivatives give
Lobatto upper bounds. Exact strict Schur shifts are explicit; support q+1 is
sufficient for Radau and q+2 for Lobatto. A blanket q+1 condition does not prove
positive Lobatto weights. Terminal and zero/singleton data have separate exact
branches. Derivative witnesses require positive order and a strict interval.

Sensitivity uses an actual prescribed native polynomial basis. Its highest
alpha row has degree at most 2n−1, requiring no next norm or degree-2n moment.
On a nonempty positive finite Hankel system, both actual input and output
vectors are nonzero, so relative normalization is defined. The affine chart
constructs its moment derivatives; no Jacobian, output convergence or nearby
representing-measure family is assumed.

The continuity record now cites
NLAlib.tendsto_hankelMomentDet_of_moment_convergence explicitly. Determinant
convergence needs no limiting support nondegeneracy and includes the empty
determinant. Eventual positive definiteness and the other finite-data endpoints
use the stated support threshold; early approximating systems may be singular.

## Exact open and excluded clauses

The CU primary is the focused re-derivation's corrected coefficient/remainder
formulation, including m>n and repeated roots. The full monomial construction
does not require unavailable original polynomials beyond support termination;
the compressed presentation states its original nonsingular finite prefix.
Traditional separate simple-root value rows and individual Cauchy-transform
rows remain **unproved optional determinant presentations**. Procedural
linear/quadratic modification algorithms, normalization, costs and numerical
stability remain **unproved optional variants**. Their original wording is
preserved in the baseline; completing the primary does not certify them.

The user **deferred the entire Gauss contour target AQ24–AQ25**. Its source
files, proof inventories and complete pre-deferral audit record are preserved
in the [local archive](E:/NLAlib-local/DeferredJordanContour-2026-10-14), outside
this PR. The current gauss-remainder-contour-kernel record cites only the shared
pointwise Stieltjes error identities and support-distance kernel estimate used
by the complete second-kind family. It makes no new contour-integrated Gauss
remainder, contour Fubini, winding or curve-length claim. The other 30 retained
source targets and their theorem evidence are unchanged by this deferral.

The scalar hermite-integral-formula card retains its preexisting baseline
circle interpolation and remainder theorems. Its broader arbitrary-contour
variant remains open; the deferred work supplies no extension in this PR.

The discrete-measure mathematical construction now uses the actual canonical
evaluation matrix, Jacobi conjugation, mass normalization and dual
orthogonality. Its composite card remains partial because **the Stieltjes
procedure returns the same coefficients** has no named algorithm/realization
theorem. Clenshaw proves its total finite algebraic recursion, but the exact
matrix-vector product count remains an open implementation/cost clause.
Procedural CG normalization is separate from the complete SPD mathematical
graded-direction interpretation.

All retained reciprocal exponential and polynomial Bernstein clauses are
complete. Actual canonical type-(0,n) reciprocal errors have the 1/3 root limit,
negative-half-line reflection, explicit denominators and actual PSD operator
bounds. Actual polynomial absolute-value errors have the full positive
Bernstein limit, parity, finite degree transfer and enclosure [1/(18π),2/π].
The printed decimal digits of the Bernstein constant are not certified.

The user-excluded **Stahl sharp type-(n,n) rational equivalent** and **Halphen
strong type-(n,n) equivalent** remain explicitly unproved. Thus the composite
abs-best-approx-asymptotics and exp-rational-halfline cards remain partial;
their retained-scope inventories must not become full composite proof families.

The Crouzeix–Palencia analytic dependency and full nonnormal Arnoldi bound
remain excluded. The procedural modified-Chebyshev algorithm is outside the
supplied mathematical target list. The user's LRA exclusion applies only to
Chen–Persson items, not independent low-rank mathematics.

## Preserved baseline audit

# Polynomial and Krylov quadrature correspondence audit

The accompanying JSON contains individual readbacks for all 83 polynomial-area,
orthogonal-polynomial, Krylov matrix-function, and quadrature-linked atlas cards.
Each record gives the actual Lean claim, exact declaration evidence, mathematical
findings, and any remaining clauses. This audit does not equate a compiled helper
with proof of an entire source card.

The newly checked finite-moment API is organized under
`Polynomial/OrthogonalPolynomials`. It proves the monic existence/uniqueness,
support positivity, finite support termination and formal three-term recurrence
contracts. The spectral bridge belongs under `Krylov/Quadrature`, respecting the
dependency layers. Existing read-only proof work was reused only after inspecting
its statements and checking each integrated module with Lean.

The Christoffel-number contract is covered by the actual Lanczos polynomial
evaluation vector, its eigenvector normalization, reciprocal kernel weights and
discrete orthogonality. Reflection parity and zero diagonal coefficients are
proved for symmetric measures; the even/odd square-map bridge remains separate.
The general-measure strict diagonal bounds and positive-order monic subdiagonal
bounds are proved with explicit support counts and squared-coefficient conventions.

The audit found concrete human-statement repairs: endpoint aliasing coefficients
were double counted, Radau's bound orientation was reversed,
unscaled Jacobi weights were attributed to the original rather than normalized
measure, a transformed polynomial was incorrectly claimed nonzero at every
complex modification point, and a nonvanishing rational denominator was treated
as automatically positive. The JSON includes counterexamples and exact corrections.
It also distinguishes the proved circle-integral interface from arbitrary
contours and algebraic Clenshaw identities from an unproved operation count.

Sharp Stahl/Halphen equivalents and the Crouzeix–Palencia analytic dependency
retain the user's exclusions. Open derivative-remainder, endpoint quadrature,
second-kind, continuity, sensitivity, modification and rational-space clauses
are listed explicitly. Their original mathematical statements are retained;
none is advertised as complete merely because its finite algebraic prerequisites
are now available.
