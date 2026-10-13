# Public contract review after the F4 checkpoint

Baseline: commit `58085f5`. This review supersedes the earlier assessment that passing the
build and proof audits was enough to recommend merging the library as a reusable foundation.
The default import's proof audit remains valid for that checkpoint. The broader API review is
unfinished. QR was a concrete counterexample to the previous review's coverage.

## What was examined

The declaration index at the checkpoint contains 6,942 public declarations. We scanned its
signatures by area and inspected representative definitions and their neighboring theorems
in source. Sol reviewed QR and the non-Matrix areas; Luna reviewed Matrix families; the
coordinator checked cross-cutting standards, documentation and downstream examples.

| Area | Indexed declarations at checkpoint |
|---|---:|
| Matrix | 2,734 |
| Polynomial | 247 |
| Probability | 518 |
| RandomMatrix | 403 |
| Krylov | 470 |
| Sketching | 1,873 |
| LowRank | 315 |
| Estimation | 101 |
| Solvers | 69 |

The remainder belongs to ForMathlib. These counts describe the search population, **not**
the number of reviewed or defective statements. Finding `ℝ` in a signature is not evidence
of a defect: singular values, probabilities, tolerances, real derivatives and majorization
sequences remain real even when the underlying matrices are complex. Source inspection was
by family, not an exhaustive theorem-by-theorem review or comparison with every cited paper.

## Confirmed families needing work

Paths below are relative to `NLAlib/`. Each row gives an entry point into a family, not a
promise that changing one definition is sufficient.

| Family | Evidence and user impact | Intended contract and acceptance check |
|---|---|---|
| QR specifications | `Matrix/Factorizations/QR.lean`: `IsQR`, `IsFullQR` and adjoint identities were real-only. | **Changed in this follow-up:** RCLike predicates, full-to-thin transport, Gram/pseudoinverse identities and spectral consequences. Check genuinely complex phases and arbitrary finite labels. Real existence and positive-diagonal uniqueness proofs remain specialized. |
| Triangular, LU and Schur algebra | `Matrix/Factorizations/Triangular.lean`: unit triangular predicates; `LU.lean`: `IsLU`, `IsPLU`; `Matrix/Basic/SchurComplement.lean`: `pivotSchur` all fix real scalars. | Use algebraic assumptions appropriate to each identity (often rings/fields), independent of pivot-selection routines. Verify on a non-real field; keep block-matrix bridges. |
| Cholesky specifications | `Matrix/Factorizations/Cholesky.lean`: `IsCholesky`, `IsPivotedCholesky` use real matrices and transpose. | Hermitian factorization `A = L * Lᴴ` over RCLike, with **real positive diagonal**, including its reality condition. Positive real part alone is insufficient. Validate complex off-diagonal entries and uniqueness; migrate real recursion witnesses separately. |
| Hessenberg and reflectors | `Matrix/Structured/Hessenberg.lean` fixes real scalars even for zero patterns; `Matrix/Factorizations/Hessenberg.lean` and `Householder.lean` restrict unitary similarity/reflector identities. | Separate scalar-independent sparsity patterns and unitary specifications from the implemented real reflector-selection routine. Test an actual complex unitary similarity. |
| Least squares | `Matrix/Basic/LeastSquares.lean`: `IsLeastSquaresSolution` and normal equations are real-only, despite a generic Moore–Penrose inverse. | Euclidean minimization over RCLike with adjoint normal equations and minimum-norm characterization. Test complex, rectangular, rank-deficient and zero matrices through the default import. |
| Embedding and JL norm interface | `Sketching/Properties/SubspaceEmbedding/Basic.lean`: real-only `IsSubspaceEmbedding`, dot products used as squared norms. `Sketching/Properties/JL/JL.lean`: same representation in probability events. | Generic deterministic embedding predicate using Euclidean squared norms; retain appropriately real distribution theorems with explicit norm bridges. Test basis changes and a complex embedding. |
| Krylov grade | `Krylov/Spaces/Basic.lean` is field-generic but `Spaces/Grade.lean` explicitly restricts grade to reals, unlike its atlas statement. | Make algebraic grade/termination compose with generic Krylov spaces. Complex iterative solver specifications are a separate scope review: current standards explicitly specialize Krylov methods to reals, so their scalar alone is not a confirmed implementation defect. |
| Deterministic low-rank interfaces | `LowRank/Structural/RangeFinder.lean`, `LowRank/Nystrom/SketchedRegression.lean`: real-only deterministic algebra, adjoints written as transposes. | Share RCLike structural bounds over the generic SVD/projector API, with real Gaussian specializations downstream. Test complex deterministic inputs without introducing a complex random law merely to use an algebraic theorem. |
| Spectral frames and projectors | `Matrix/Spectral/Eigenframes.lean`, `Matrix/Perturbation/EigenspaceProjector.lean`, `EigenvaluePerturbation.lean` specialize Hermitian constructions/bounds to reals. | Generic eigenframes, spectral projectors and Hermitian eigenvalue perturbation bounds; use real ordered eigenvalues without forcing real matrix entries. Test repeated eigenvalues and basis independence. |
| Norm bundles | `Matrix/Norms/InvariantNorm.lean`: generic `UnitarilyInvariantNorm`, but real-only `SymmetricGauge.matrixValue`, `matrixSeminorm` and its constructor. `NuclearNorm.lean`, `Inequalities/KyFanNorms.lean` and Schatten bundles also restrict entries to reals. | Make bundled norm interfaces compose with the already generic scalar norm functions. Distinguish real scalars of a seminorm from real entries of its matrix domain. Check evaluation and generic Mathlib seminorm operations on complex matrices. |
| Elementary constructors/helpers | `Matrix/Basic/Selection.lean`, `Gram.lean`, `DeterminantDiagonalUpdate.lean`, `Matrix/Structured/StructuredMatrices.lean`: real-only selection, rank/determinant, diagonal update, Toeplitz/Hankel/Cauchy APIs. | Use the weakest useful algebraic domain and search Mathlib before adding another definition. Selection and zero-pattern constructors should not require RCLike; Hankel/Toeplitz need no scalar operations. |
| Inertia | `Matrix/Spectral/Inertia.lean` encodes real quadratic-form inertia. | Review a Hermitian inertia contract and spectral counts over RCLike. This requires a mathematical representation decision, not replacing `ℝ` textually; dimension must remain dimension over the matrix scalar field. |
| Relative errors and angle ratios | `Matrix/Perturbation/LeastSquaresCoordinateBounds.lean`: `leastSquaresTan` is zero at zero projection; relative solution bounds include `x = 0` by total division. The conventions are documented, but the geometric interpretation has a smaller domain. | Use native Euclidean norms; expose the nonzero denominator/domain in geometric and relative-error claims, or expose an extended-valued object. Distinguish a valid total algebraic inequality from a meaningful relative error at zero. |

These are open work items except for the QR interfaces specifically listed as changed. A
real-only theorem is not logically false. The issue is that a natural downstream use cannot
be expressed through the advertised reusable interface, or that its meaning requires more
care than its name suggests.

The QR changes supply generic specifications and conditional identities. The downstream checks
exercise an explicit complex `2 × 1` factorization with an imaginary unitary phase and
conditional full-to-thin transport; they do not supply general complex QR existence or
normalized uniqueness.

The downstream default-import check also exposed that QR's proved spectral consequences
shared an experimental Cholesky dependency through `QRConsequences.lean`. They now live in
`Matrix/Factorizations/QRSpectral.lean`, available through `import NLAlib`, with no ordered
column-type assumption. The real existence/uniqueness development imports this shared API.

## Matrix-function consolidation

The user requested one deterministic `Matrix/Functions` group. This follow-up moves the 19
`Matrix/OperatorTheory` content modules and seven trace-function modules from `Inequalities`
and `Spectral` into it, for 45 content modules in total. Declaration names are unchanged; the
module migration map is `docs/renames/2026-10-13-matrix-functions-modules.json`.

This group contains functional calculus, exp/log, operator convexity, perspectives, entropy,
Lieb/Golden–Thompson and trace-function inequalities. The probability-specific integral,
matrix-MGF, independence and concentration results retain their probability-layer home. In
particular, `Probability/Concentration/Basic/MatrixCalculus.lean` actually states integral/MGF
identities and is not a misplaced deterministic calculus file. The empty `LiebJensen.lean`
compatibility shell was removed; its consumer imports the native convex-integral bridge.

Log-determinant and inverse-trace convexity use definite-pair congruence, whose inertia import
previously brought in an unrelated unfinished Sturm count. That one scaffold is now in
`Matrix/Spectral/InertiaSturm.lean`, registered as experimental. The proved inertia API stays
in `Inertia.lean`; `Matrix/Functions` and all 45 function modules are in the default surface.
The Sturm statement and its unfinished proof status are unchanged.

General norm/majorization inequalities remain in `Matrix/Inequalities`, and spectral
decomposition/eigenvalue structure remains in `Matrix/Spectral`. Classification follows the
mathematical subject, not merely the occurrence of `trace`, `exp` or `log` in a formula.
The directory changes do not resolve the open scalar/domain contracts in the table above.

## Other findings and exclusions

- `scripts/check_norms.py` reports **221 heuristic hits in 1,063 files** at this checkpoint;
  it is not in the current CI workflow. This is neither 221 established defects nor a clean
  standards result. The embedding/JL and least-squares cases above were checked in source.
  Reconcile the actual policy and script before using this as a release gate; do not suppress
  hits by broadening exemptions just to obtain green output.
- The algorithm guide described CG/Lanczos realization theorems without making their current
  experimental status explicit. The index already marks their transitive unfinished proofs.
  The guide now distinguishes intended contracts from completed recurrence proofs.
- Sparse `FiniteLaw` has PMF equivalence, measure/integral identities and `HasLaw` bridges.
  Its existence alone is not a defect. Check whether an adapter has a useful computational
  purpose and interoperates with native objects before removing it.
- Real Gaussian, Rademacher and orthogonal-Haar laws have genuine real content. Real Schur
  normal forms and real majorization sequences are legitimate. An explicit real construction
  is not automatically justification for making the underlying generic specification real-only.
- RSVD's certificate-based assembly lemma has downstream law-based theorems supplying the
  relevant certificates. It is not evidence that the whole RSVD guarantee is merely assumed.
- SLQ currently documents its stopped-Arnoldi compression interpretation and missing recurrence/
  cost guarantee. Full randomized Hutch++/XTrace analysis and the known experimental recurrence
  proofs remain separate unfinished work, as recorded in the earlier audit.

## Repair order and release evidence

1. Settle scalar domains and representations for elementary constructors, triangular/Schur
   algebra, least squares, embeddings and Krylov grade. Reuse Mathlib or write explicit bridges.
2. Generalize factorization specifications and their basic APIs. Keep specialized construction
   proofs under honest scope; a generic predicate without usable characterizations is not enough.
3. Migrate spectral/projector and norm-bundle families, then deterministic low-rank and solver
   consumers. Consolidate real/complex duplicates where they express the same mathematics.
4. Review probability laws, geometric domains and algorithm claims through those interfaces.
   Preserve valid distribution-specific assumptions and document genuinely unfinished analysis.
5. Check representative downstream uses for each family over `ℝ` and `ℂ` (or a general field
   for algebraic APIs), including degenerate cases. Record remaining specializations explicitly.

For each family, acceptance requires a source-reviewed mathematical contract, a native-object
bridge where appropriate, and a downstream application that exercises the intended domain.
Then run the build, proof audit and metadata checks. Passing these mechanical checks is
necessary evidence about the implementation, not a substitute for the contract review.

This review is a dependency-ordered work inventory, not a declaration that the library is
ready to serve as a stable reusable foundation or that all contract issues have been found.

## Validation of this follow-up

- `lake build NLAlib NLAlib.Experimental`: passed, 5020 jobs.
- Default-import audit: 11738 declarations; no unfinished proofs or nonstandard axioms.
- Full audit: 12538 declarations, including 6830 public theorems; the existing 39
  sorry-dependent theorems remain excluded from the default import.
- Completed-proof audit: 6282 public/private theorem declarations passed.
- Lean lint: zero errors in 7316 declarations and 4422 generated declarations.
- The standalone `Matrix.Functions` import, complex QR downstream examples, and probability
  examples all compile. Import-surface and layer checks and all eight Python tests passed.
- Final declaration-index extraction and dependent metadata checks were stopped at the user's
  request to commit without waiting for metadata regeneration.
