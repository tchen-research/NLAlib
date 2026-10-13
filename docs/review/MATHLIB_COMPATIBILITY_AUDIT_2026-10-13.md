# Mathlib compatibility and downstream usability audit — 2026-10-13

The findings below record the pre-fix snapshot. The implementation follow-up at the end
records the authorized changes and their completed validation. Original source
locations and counts are retained as audit evidence, not a description of the revised API.

The subsequent [public contract review](PUBLIC_CONTRACT_REVIEW_2026-10-13.md) found additional
families of missed restrictions, including real-only factorization and least-squares contracts.
The validation recorded here establishes compilation and proof status for the checkpoint;
it does not establish completion of the mathematical interface audit.

## Verdict

The library interoperates with its pinned Mathlib, and much of its mathematical core is a
reasonable foundation for other authors. It is **not yet ready to present the entire default
import as a finished, trusted starting point**. The main obstacles are a reproduced semantic
error, an unclear boundary around unfinished proofs, incomplete bridges from some algorithm
and probability interfaces, and contradictory local contribution rules.

Do not restart the library or remove every custom definition. Preserve the substantial proved
core and its Mathlib adapters. Correct the public contracts, define the trusted import surface,
and simplify the standards before doing further mechanical renaming or file consolidation.

“Compatible with Mathlib” and “ready to upstream to Mathlib” are different bars. A domain library
can appropriately define randomized numerical linear algebra objects that Mathlib does not
provide. The test is whether their meaning is faithful, their edge cases are clear, and their
API connects to ordinary Mathlib objects without asking users to rebuild those connections.

## Scope and evidence

This reviews the working tree after the F4 compilation recovery, on branch `nlalib-f4`, based
on commit `089abd4` plus substantial uncommitted changes. It is not a review of that commit
alone. Lean is `v4.33.1`; Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`.

The preceding [recovery report](../F4_RECOVERY_2026-10-13.md) records a successful full build
(5,012 jobs), 6,687 audited theorem declarations, and **39 theorem names depending on
`sorryAx`**. There are 16 direct `sorry` occurrences in source. The 39 is a transitive theorem
count, not a count of source holes or evidence that unrelated theorems are tainted. The
completed-proof subset audit also passed. This audit did not repeat the full build: it read
the current sources, fresh declaration index, local pinned Mathlib, standards and CI, and ran
targeted Lean checks described in the specialist reports.

The current generated index has 6,796 public declarations. The tree contains 953 content Lean
files and 105 generated aggregators; 357 content files have fewer than 100 lines. These are
navigation/maintenance observations, not quality scores or reasons to delete mathematics.

Specialist reviews:

- [Matrix core, norms, subspaces and upstream adapters](MATHLIB_AUDIT_MATRIX_2026-10-13.md).
- [Probability, random matrices, sketches and probabilistic consumers](MATHLIB_AUDIT_PROBABILITY_2026-10-13.md).
- [Krylov, polynomial approximation and estimators](MATHLIB_AUDIT_ALGORITHMS_2026-10-13.md).

No Lean source, theorem statement, build configuration, or existing standards document was
changed during the initial audit. The subsequent implementation is recorded separately below.
It is a risk-based review, not an exhaustive semantic verification of
every declaration. Source locations below refer to this working-tree snapshot.

## Findings in priority order

### 1. High: the largest Ritz value has an incorrect general-domain meaning

`Krylov/Spectral/MeasurableRitz.lean:43–49` includes the zero vector in the supremum of Rayleigh
quotients. Its quotient is zero. Consequently, for the one-dimensional example `A = [-1]`,
`b = [1]`, `q = 1`, the definition returns **0**, whereas the largest Ritz value is **−1**.
The algorithms report includes a compiled, reproducible Lean counterexample.

Mathlib's Rayleigh API in `Analysis/InnerProductSpace/Rayleigh.lean:84–103` uses nonzero vectors
or a positive-radius sphere for the corresponding optimization. Adopt that domain, choose an
explicit convention for a trivial Krylov space, and prove equality with the largest eigenvalue
of a Hermitian compression. Add negative-definite and trivial-space examples.

The existing random-start expectation applications assume PSD matrices; the counterexample
does **not** refute those bounds. It does invalidate the advertised unrestricted interpretation
and prevents natural reuse for shifted or indefinite matrices.

### 2. High: users cannot rely on the advertised proof-completeness boundary

`NLAlib.lean:1–10` imports every area, including unfinished recurrence and factorization
results. `scripts/Audit.lean:25–35` explicitly permits `sorryAx` and records its descendants.
However:

- `README.md:39` describes the audit as establishing only the three standard axioms.
- `.github/workflows/ci.yml:18` calls it an audit with “no sorry”.
- `scripts/check_atlas.py:74–78` only prints a note for uncatalogued sorry-dependent names, or
  for a missing audit output. The latest run lists **23 uncatalogued descendants**.

This is a trust/documentation defect, not a failure of Lean's kernel. In particular, proved CG
variational existence/uniqueness is distinct from `isCGIterate_cgRecurrence`, whose axioms
include `sorryAx`. The latter can be encountered through normal imports with no `sorry` in its
own proof body.

Before release, either finish these proofs or put unfinished developments behind explicit
experimental imports. Check the **transitive axioms of every declaration in the intended
trusted surface**, including definitions and helpers that can carry proofs. Fail CI when that
surface depends on `sorryAx`. Maintain a separate inventory for experimental work and expose
derived trust status in documentation. An import of an unfinished theorem does not by itself
make an independent theorem depend on it; audit dependencies rather than treating all imported
mathematics as unusable.

### 3. Medium: some algorithm theorems are specifications, without a constructed algorithm bridge

SLQ accepts a supplied orthonormal matrix containing the Krylov space. Its approximation
theorems are useful and substantive, but do not relate the supplied compression dimension to
the stated number of Lanczos steps. A full ambient basis satisfies containment for every
step count. See `Estimation/Quadrature/SLQ.lean:43,60–66,107–113` and
`SLQAnalyticSteps.lean:26–35`.

Similarly, Hutch++ and XTrace unbiasedness theorems accept supplied bases/statistics,
independence and integrability. They are general unbiasedness kernels, not yet complete
constructions of the named sampling procedures. See `Estimation/Trace/Unbiased.lean:103–205`.

Keep the generic theorems. Add separate concrete constructors and realization corollaries,
including early breakdown, zero probes, dimension bounds, and the independence/integrability
facts needed to apply them. Label approximation-order statements separately from certified
operation-count statements. Do not add a certificate that merely restates the conclusion.

### 4. Medium: probability interoperability is uneven outside the Gaussian core

Gaussian and Rademacher laws use good Mathlib-native foundations. Several remaining APIs still
require callers to reconstruct the connection between a finite expression and a random object:

- The general directional sub-Gaussian norm-tail route is restricted to finite PMFs or
  finite-support laws, rather than directly admitting continuous distributions.
- Some Cholesky, real volume-sampling, and sketch-and-project “expectations” remain finite
  weighted sums/recurrences without the corresponding PMF/measure/law identification.
- Sparse-law transport uses strict measurability and raw push-forward equalities where a
  `HasLaw` interface would accommodate the standard almost-everywhere semantics.
- Limited-independence/moment predicates need practical constructors from native marginal
  laws, not only implications out of the custom predicate.

These are bridge gaps, not reasons to prohibit finite sums, PMFs, moment predicates, or
specialized measures. Preserve the finite formulas as computational lemmas, identify them with
the expectation under an actual law, and expose measure/`HasLaw` corollaries. The probability
report gives declaration-level evidence and existing successful patterns to copy.

### 5. Medium: totalized subspace quantities need a more precise public contract

The matrix review identifies tangent quantities that return zero at orthogonality because
real division/inversion is total, and a real supremum formulation whose unbounded case also
collapses to zero. Such values cannot be read as a small geometric error outside the intended
transversality domain. It also distinguishes the directed gap implemented by unequal-width
`sinThetaMax` from a conventional list of principal angles.

Concretely, for the identity frame `Q = I₂` and the one-column frame `X = e₁`, Lean checks
`sinThetaMax Q X = 0` but `sinThetaMax X Q = 1`. Both frames have orthonormal columns. This is
a useful directional residual, but the documentation currently calls it the largest angle
between unequal-dimensional spaces without declaring that direction. See
`Matrix/Subspaces/PrincipalAngles.lean:49–64`, `PrincipalAngleDefinitions.lean:22`, and
`GraphTangent.lean:23,73`.

A total real-valued definition is not automatically wrong; Mathlib itself uses total
operations. State the valid geometric domain clearly and provide its bridge lemmas. If users
need comparisons including orthogonality/infinite tangent, add an appropriately extended-valued
quantity or restricted-domain interface. Do not silently change the existing totalization
without tracing its consumers. Correct the unequal-dimension documentation or provide separate
names for directed gap and principal-angle quantities.

### 6. Medium: some elementary APIs are less general or less discoverable than their objects

There are still genuine duplicate interfaces to consolidate. Generic `columnSpace` and
`rangeProjector` coexist with `complexColumnSpace` and `complexColumnProjector`
(`Matrix/Subspaces/RangeProjector.lean:31–37`, `ComplexVolumeProjection.lean:20–25`), with no
public equality bridge found for the two projector constructions. Real and complex
principal-angle definitions also remain separate despite generic singular values. Migrate
these consumers to the generic objects, using explicit equivalence lemmas during the move.

Conversely, keep `HasOrthonormalCols`, but publish its basic equivalence with Mathlib's
`Orthonormal` family of Euclidean columns: the direct conversion is currently private in
`Subspaces/Projections.lean:305–308`. Likewise, connect coordinate subspaces and Euclidean
subspaces at the basis-matrix API. These are missing bridges, not reasons for new vector or
frame types.

`krylovSpace` is field-generic, while even generator membership and polynomial characterization
remain real-only (`Krylov/Spaces/Polynomial.lean:33,48`). A complex consumer has already needed
to repeat the generator proof. Generalize the algebraic lemmas at their existing API rather
than producing real/complex parallel files. Generality should follow the mathematics: a
recurrence over `Fin n` or an intrinsically real probability law need not be forced into a
more abstract form just to satisfy a global rule.

Some upstream-oriented facts also sit in artificial namespaces. For example,
`ForMathlib/Analysis/Convex/Integral.lean:22` declares
`NLAlib.ConcaveOn.le_map_integral_of_integral_mem` rather than extending the root `ConcaveOn`
namespace. This inhibits the usual dot-notation discovery. Of 211 indexed `ForMathlib`
declarations, 141 are under `NLAlib`; that count is a review queue, not proof that all 141 are
misplaced. General facts about Mathlib objects should normally use their owning namespaces;
genuinely library-specific objects can retain `NLAlib`.

### 7. Medium: the standards themselves contain unnecessary and contradictory constraints

Mathlib's [style guide](https://leanprover-community.github.io/contribute/style.html) explicitly
presents guidelines rather than rigid rules. The following local restrictions should be
revised before another contributor is asked to follow them:

| Current rule or conflict | Evidence | Recommended replacement |
|---|---|---|
| Substantive theorems cannot be in `Basic.lean` | `STANDARDS.md:94–98`; `check_names.py:39–42` decides eligibility by name suffix or the word “simp” in a docstring | Let `Basic` contain definitions and foundational API, as in Mathlib. Remove this heuristic lint. |
| Never state `∃ C`; derive a numeric constant even if the source does not | `CONTRIBUTING.md:59–60`; `TARGETING.md:72–74` | Prefer useful explicit refinements when available; allow natural existential/asymptotic theorems. |
| Delete `schattenSeminorm` and `schattenInvariantNorm` to enforce one spelling | `F4_CONSISTENCY_BRIEF.md:57–58` | Keep one scalar formula and useful bundled adapters, with evaluation/bridge lemmas. Bundling supports reuse. |
| Everything another file might conceivably want must be public | `STANDARDS.md:103–104` | Export an intentional, documented API; keep proof implementation details private until needed. |
| Namespace `NLAlib` everywhere versus methods in owning namespaces | `CONTRIBUTING.md:27–29`, `TARGETING.md:79–82` versus `STANDARDS.md:87–90` | Use Mathlib namespaces for extensions of Mathlib objects and local namespaces for new domain objects. |
| Direct pre-v0.1 renames versus mandatory deprecated aliases | `STANDARDS.md:38–39` versus `CONTRIBUTING.md:88–90` | State one release-aware compatibility policy in one place. |
| Krylov methods never defined by recurrences | `STANDARDS.md:56–59`, despite recurrence implementations | Keep specifications and algorithms, and require realization theorems to connect them. |
| Targeting guide prescribes old Fin-only Gaussian bundles and says the general pseudoinverse does not exist | `TARGETING.md:50–64` | Replace stale setup instructions with links to current API examples. |

The `Basic` rule has already created pointless work: the `rfl` theorem
`relativeEntropy_complex` (`Matrix/OperatorTheory/Basic.lean:29–32`) needed an exemption in
`scripts/name_exemptions.txt:22–23`. Pinned Mathlib's own
`LinearAlgebra/Matrix/Determinant/Basic.lean:19–31` includes `det_mul` and block-determinant
theory, not merely definitions.

Keep useful conventions: Mathlib naming, source attribution, checking Mathlib before defining,
standard PSD/order/CFC objects, explicit hypotheses, sensible import layering, and preferring
separate upper/lower lemmas. Mathlib also recommends splitting conjunctions where useful; that
is not a local oddity. Prefer `RCLike` and finite index types when naturally applicable, without
blanket bans on convenience corollaries or finite algorithm indices.

Make one short contributor guide authoritative. Treat historical briefs as migration history,
not additional live sources of law. Atlas maintenance can remain valuable tooling without
requiring every small helper contribution to begin with a bespoke cataloguing workflow.

### 8. Medium before release: packaging proves a build, but not a good downstream starting experience

The README explains building this repository but lacks a dependency-installation example and
a minimal checked user proof. There is no dedicated downstream examples/test target;
`lakefile.lean` configures `autoImplicit := false` but no lint/test driver, and CI explicitly
sets `lint: false`, `test: false` (`ci.yml:16–17`) while running custom checks separately.

Provide a small checked examples suite under ordinary downstream options: a norm/pseudoinverse
result, a Gaussian `HasLaw` application on an abstract probability space, a subspace embedding,
and one concrete estimator/solver. Include representative complex matrices and non-`Fin`
indices. Use focused semantic regression examples for the bugs above, rather than tests that
only restate implementations. Document minimal imports and provide searchable API documentation.
Introduce suitable standard Mathlib/Batteries lint checks incrementally; custom atlas/name
checks are not substitutes for them.

Consolidate files by mathematical topic and import needs, not solely by a line-count target.
The old port manifest lists 1,003 content files and mechanically marks all solvers for rebuild;
it predates the current tree and improvements. Regenerate it after API decisions instead of
executing it blindly (`docs/port/MANIFEST.md:9,46–52`). Modern Mathlib module/public-import style
and file headers are useful upstream preparation, but the existing old-style imports already
compile and are not the immediate compatibility problem.

## Definitions and adapters to preserve

| Interface | Why it belongs |
|---|---|
| `specNorm`, `frobNorm`, `frobSq` | Named matrix norms disambiguate Mathlib's scoped norm instances; retain norm bridges. |
| `singularValues` | Anchored to the singular values of Mathlib's Euclidean linear map, rather than a competing SVD theory. |
| `HasOrthonormalCols` | The familiar Gram identity, connected to a Mathlib `LinearIsometry`. |
| General Moore–Penrose inverse, SVD and subspace interfaces | Legitimate domain API where the pinned dependency lacks the full desired matrix interface; preserve standard identities and bridges. |
| Bundled seminorms and invariant norms | Package structure needed by generic theorems; they need not duplicate the underlying scalar definition. |
| Krylov spaces, Arnoldi decompositions, minimizer predicates | Standard span/Gram–Schmidt/optimization objects; keep proved existence and realization bridges. |
| Gaussian/Rademacher measures and `HasLaw` aliases | Specialize standard probability theory without inventing a second framework. |
| Matrix measurable-space adapter | Uses the ordinary product σ-algebra and Borel structure (`ForMathlib/MeasureTheory/Matrix.lean:36–44`); a legitimate upstream candidate, not an exotic instance. |
| Spectral measures, trace-estimator kernels, Chebyshev/Joukowski objects | Recognizable mathematical concepts built on Mathlib measures, `cfc`, and polynomials. |

The decision rule for a new definition should be: does Mathlib already have this object; if
not, is the new object mathematically recognizable, are its degenerate cases intentional, and
can downstream users enter and leave its API through standard equivalences, constructors and
elimination lemmas? Merely counting custom definitions does not answer those questions.

## Recommended next checkpoint

1. Correct the Ritz domain and settle the subspace-angle contracts, with edge-case checks.
2. Establish a trusted import boundary and a failing transitive `sorryAx` gate for it. Correct
   README/CI trust claims and make experimental descendants visible.
3. Replace conflicting standards with the short policy above; explicitly retain useful bundled
   adapters. Do this before continuing deletion/rename work prescribed by older briefs.
4. Complete the highest-value native probability and algorithm realization bridges, generalize
   elementary Krylov lemmas, and demonstrate their use in checked downstream examples.
5. Refresh the port manifest and documentation against that settled API, then move the reviewed
   surface to the new library. Carry unfinished developments only with explicit status/imports.

The release criterion should be that an independent user can import the advertised trusted
surface, apply recognizable theorems through ordinary Mathlib objects, and see exactly which
algorithmic guarantees are proved. A green build, a low count of custom names, or strict
compliance with the current local lint rules is not sufficient by itself.

## Implementation follow-up

The user authorized corrections to the contracts, with the mathematical statement settled
before proof convenience. The following changes implement that direction in the working tree.

| Finding | Revised interface |
|---|---|
| Ritz values clipped negative spectra | `ritzValues` is the sorted spectrum of an orthonormal compression. `lanczosRitzValue` uses the actual Krylov-space dimension, with explicit empty-space/non-Hermitian conventions. Nonzero-vector variational and measurability bridges are theorems. |
| Directed gap presented as a largest principal angle | `directedSubspaceGap` states its orientation and unequal-dimension behavior. The equal-width angle bridge is proved. Real/complex angle definitions share the conjugate-transpose overlap. |
| Singular inverse/division presented as a finite tangent | `overlapTangentNorm` and `overlapTangentSq` name the total algebraic helpers; finite geometric interfaces carry domain certificates. The extended vector tangent is infinite at nonzero orthogonality. |
| Duplicate subspace/projector interfaces and missing standard bridges | Generic `columnSpace` and `rangeProjector` replace the complex copies. Public Euclidean `Orthonormal`, linear-isometry, coordinate/Hilbert-subspace, and basis-matrix bridges compose directly. Jensen extends the root `ConcaveOn` namespace. |
| Finite sums serving as the only algorithm expectations | Cholesky histories and real volume samples have native PMF/measure laws, integral identities, integral bounds, and `HasLaw` transports. Sketch-and-project accepts a native PMF, constructs iid paths, and states row-space convergence as an actual expectation. |
| Finite-support restriction on directional subgaussian tails | The primary MGF and tail bounds now accept arbitrary probability measures. Tonelli precedes the integrability argument; PMF results are corollaries. SRHT uses the general theorem directly. |
| Bespoke probability interfaces without native entry points | Gaussian coordinate laws plus joint independence construct the matrix law. Sparse finite laws round-trip to PMFs, and local-observable matching is equivalent to equality of restricted-coordinate laws. Conditional expectations of integrable Hermitian squares construct the local second-moment predicate. |
| Algorithm names attached only to supplied certificates | Supplied-frame formulas are `compressionQuadratureEstimate`, `deflatedTraceEstimate`, and `leaveOneOutDeflatedTraceEstimate`. Constructed SLQ uses stopped Arnoldi frames with exact range and width at most the requested order. Hutch++ constructs its sketch-image basis; a basic XTrace construction removes each probe in turn. Generic guarantees are marked partial where they do not establish the advertised algorithm result. |
| Fragmented Schatten exponent interface | `schattenNorm` accepts extended nonnegative exponents, including infinity. `schattenNormReal` is the finite formula, with coercion and endpoint bridges. Seminorm and invariant-norm bundles remain available. |
| Analytic-only entry point for Chebyshev coefficients | `chebyshevCoeff` uses Mathlib's arcsine measure; weighted and cosine integral formulas agree with the existing real/complex contour coefficients under a continuous real restriction, without an analyticity premise for identification. |
| Contradictory contributor rules | Current standards allow foundational theory in `Basic`, appropriate existential constants, finite algorithm indices, private helpers, and useful bundled adapters. Helpers need meaningful documentation, not fabricated source citations. Historical briefs no longer override current policy. |
| Unclear trust and release surface | Generated `import NLAlib` excludes explicitly experimental roots and their module dependants. A strict axiom audit checks every reachable declaration, including private helpers and definitions. Experimental proofs remain separately indexed. Direct unfinished proofs require catalogued scaffold tags. |
| Misleading publication metadata | Derived unfinished-proof status is preserved in atlas formalizations, dependency links, and book coverage. The port inventory records current modules and trust status instead of mechanically directing all solvers or finite probability proofs to be rebuilt. |

The focused checks cover a negative one-dimensional Ritz spectrum at every positive order,
zero starts, breakdown, unequal-width nested subspaces, nonzero orthogonality, standard
Mathlib interoperability, and a continuous Gaussian sample space. They live in
`scripts/AuditRitz.lean`, `scripts/AuditSubspaces.lean`, and `Examples/Probability.lean`;
`Examples/Downstream.lean` exercises the default import. Standard Batteries declaration and
instance linters supplement the custom checks. Rename maps are in `docs/renames/`.

Validation completed:

- Default build: 4,940 jobs; complete experimental build: 5,018 jobs, both successful.
- Strict default-import audit: 11,508 declarations, no `sorryAx` or nonstandard axioms.
- Complete audit: 12,537 declarations, including 6,830 public theorems; the same 16 direct
  unfinished proofs and 39 dependent theorems are indexed and excluded from the default import.
- Standard Batteries checks: three linters, zero errors. Ritz/subspace regressions, both
  downstream example files, Gaussian inverse audit, and the 6,283-theorem completion audit pass.
- Fresh index: 6,942 public declarations; atlas: 354 results, synchronized. Import-surface,
  layer, naming, schema/atlas, eight Python regression tests, and whitespace checks pass.
- Book coverage references validate; 109 conservative candidate-versus-topic-status warnings
  remain for source-by-source review. They were not automatically promoted to proved coverage.
- Port inventory: 957 content modules. Both site artifacts build; viewer JavaScript syntax
  checks pass. Obsolete handwritten recipes for 98 changed formalizations were preserved in
  `docs/f4/formalization_metadata_pending.json` instead of reused against changed contracts.

Remaining mathematical scope is explicit. The existing recurrence/factorization scaffolds
are still unfinished. Constructed SLQ does not yet certify a short Lanczos recurrence or
matvec cost. Random-sketch Hutch++ and the full published XTrace analysis still need their
measurability, independence, and performance arguments; fixed-sketch unbiasedness and generic
kernels are not labelled as those full results. Some inverse-based tangent and Schatten
inequality/bundle theory remains real-specialized. The module-level default boundary is
conservative and can exclude otherwise independent proved declarations sharing experimental
imports. None of these limitations is silently represented as a completed guarantee.
