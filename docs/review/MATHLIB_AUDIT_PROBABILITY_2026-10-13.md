# Probability interfaces: Mathlib compatibility and usability audit

Date: 2026-10-13. Scope: Probability, RandomMatrix, and random interfaces in Sketching, LowRank, and Solvers. Read-only source review; this report is the only repository edit for this task.

Compared against the checked-out Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, with Lean `v4.33.1`. References below use repository-relative paths and current line numbers. Priorities rank obstacles to using the proposed library, not proof-unsoundness severity.

**Assessment:** the canonical Gaussian, Rademacher, and Haar foundations already fit Mathlib well. The largest remaining problem is inconsistent access to those foundations: some algorithm results stop at valid finite-sum formulas, some require rebuilding elementary law adapters, and one general-looking concentration interface admits only finitely supported randomness. No new false theorem or circular headline certificate was established by this review. The findings below do not claim an exhaustive soundness audit.

## 1. High: directional sub-Gaussian norm concentration unnecessarily requires finite support

Evidence: `NLAlib/Probability/ChiSquare/DirectionalSquaredNorm.lean:73` requires `[Fintype Ω]` and `p : PMF Ω` for the squared-norm MGF comparison. The additive tail at line 183 has the same restriction. The continuation wrapper at line 232 replaces finite ambient type with a **finite-support assumption on the ambient measure**, not an arbitrary probability measure.

This excludes a continuous Gaussian sample space even when all the stated directional `HasSubgaussianMGF` inequalities hold. It also excludes a discrete-valued vector represented on a continuous sample space: finite support of the *image law* is not finite support of the ambient measure. Finite dimension of the random vector is unrelated to either restriction.

There is a concrete downstream cost already in-tree. `NLAlib/Sketching/Structured/SRHTFlattening.lean:121` constructs the finite set of all sign vectors, proves its finiteness and almost-sure support, then calls the wrapper at line 128. Those lines are valid, but proof infrastructure about the sampling space has leaked into a row-norm concentration application.

Fix: make the primary MGF and tail statements accept `(μ : Measure Ω) [IsProbabilityMeasure μ]` and directional Mathlib `HasSubgaussianMGF`. Use nonnegative Gaussian linearization/Tonelli and obtain exponential integrability from the finite MGF bound, rather than interchanging a finite sum. Directional measurability can be obtained from the coordinate directions, or made explicit initially. Keep PMF statements as corollaries. A smaller intermediate repair would transport a finite-support **image law** through `HasLaw`, covering discrete vectors on arbitrary sample spaces, but would still not cover continuous vectors.

This needs a genuinely more general proof, unlike most adapter findings below.

## 2. High: several algorithm expectations have no native law identification

The finite sums below are legitimate formulas, with substantive normalization and positivity proofs where required. The missing piece is an identification with the expectation of an actual random output, not a claim that the formulas are mathematically wrong.

| Interface | Evidence | Missing connection |
|---|---|---|
| Adaptive real RPCholesky | `NLAlib/LowRank/Cholesky/CholeskyHistories.lean:22` defines history weights; line 29 defines the expected trace sum; lines 34 and 66 prove nonnegativity and normalization. | No `PMF`/`Measure` history law or integral identity in the Cholesky subtree. |
| Adaptive complex RPCholesky | `NLAlib/LowRank/Cholesky/ComplexCholeskyHistories.lean:28` and line 35 repeat the history-weight/expectation interface. | Same missing law and transport API. |
| Real volume sampling | `NLAlib/LowRank/Sampling/VolumeSampling.lean:39` defines `volumeSamplingExpectedFrobSq` as normalized determinant weights times residual errors; line 76 proves positivity of the normalizer in the feasible range. | No real volume-sampling law or integral identification in this file. |
| Sketch-and-project | `NLAlib/Solvers/SketchAndProject/Core.lean:45` defines `expErr` recursively; line 53 defines the expected projector sum; line 176 states convergence using that recurrence. | No path law, random run map, or integral identity in this subtree. |

Example of the practical boundary: a user has a random adaptive history `H : Ω → Fin t → n` and wants to apply `choleskyExpectedTrace_le_mul_spectralTraceTail` (`RandomPivotedCholesky.lean:81`) to an integral on `Ω`. There is no native law to put in `HasLaw H ... μ`, so the user must reconstruct the probability model before transporting the theorem. A concentration or conditional-expectation argument has the same problem.

Real volume sampling has an additional naming hazard outside the feasible range. A checked scratch example proves

```lean
volumeSamplingExpectedFrobSq (1 : Matrix (Fin 1) (Fin 1) ℝ) 2 = 0
```

while every subset of `Fin 1` has cardinality different from two. This is ordinary totalization of a finite sum, not a counterexample to a theorem with `k ≤ rank A`. The unqualified definition is nevertheless not an expectation under a probability law for all its arguments.

Fix: retain the useful sums and recurrences as computational/proof formulas. Construct canonical PMFs under their actual feasibility assumptions, prove singleton masses and integral identities, and publish `HasLaw` corollaries. Cholesky already has almost all data for `PMF.ofFintype`; `[Nonempty n]` is the existing normalization condition. For successive adaptive choices, use `PMF.bind` or a Markov kernel when a process interface is needed. For volume sampling require `k ≤ A.rank` in the law constructor; a generic real/complex implementation would avoid the present asymmetry. For sketch-and-project add the finite path law/run identity analogous to Kaczmarz.

These are achievable bridges, not reasons to discard the existing algorithm proofs. In-tree models to copy are:

- `NLAlib/Solvers/Kaczmarz/KaczmarzProbability.lean:50`: actual path PMF; line 65: integral/recurrence identity; line 84: convergence in the actual integral.
- `NLAlib/LowRank/Sampling/ComplexVolumeSamplingLaw.lean:278`: feasible PMF; line 284: probability measure; line 307: integral equals the weighted sum.

Pinned Mathlib supplies `PMF.ofFintype` (`Probability/ProbabilityMassFunction/Constructions.lean:204`), `PMF.bind` (`Monad.lean:105`), and `PMF.integral_eq_sum` (`Integrals.lean:47`).

## 3. Medium: sparse law transport requires stronger measurability than Mathlib's law interface

Evidence: `NLAlib/Sketching/Sparse/SparseEmbeddingTransport.lean:21` and line 53 require a separate `Measurable Z`/`Measurable X`, a raw `μ.map Z = law` equality, and `[IsProbabilityMeasure μ]`. Their shared bridge is `NLAlib/Sketching/Sparse/FiniteLaw/ToMeasure.lean:66`.

Mathlib `HasLaw` deliberately requires only **almost-everywhere** measurability (`Mathlib/Probability/HasLaw.lean:39`). Its `.congr` at line 68 supports changing a random variable on a null set; `.measureReal_eq` at line 50 transports event probabilities; `.isProbabilityMeasure` at line 104 derives source normalization from a probability target.

Thus an arbitrary representative supplied by `HasLaw` cannot directly use these sparse embedding results. This matters on noncomplete source spaces, where an almost-everywhere modification need not be measurable everywhere. The finite target does not fix that source-space issue.

Fix: use `HasLaw Z law μ` as the primary transport premise, use `.measureReal_eq` for the measurable target event, and derive the probability-measure instance locally. Keep the stronger measurable/map form as a convenience corollary if wanted. The existing general lemma `NLAlib/ForMathlib/Probability/HasLaw.lean:15` already proves that map equality to a nonzero target implies `HasLaw`; it also correctly avoids the zero-map degeneracy.

This is an ergonomic restriction, not an invalid probability calculation.

## 4. Medium: limited-independence consumers cannot enter through ordinary marginal laws

Evidence: `NLAlib/Sketching/Sparse/FiniteLaw/LocalMoments.lean:49` defines `FiniteLaw.MatchesUpTo` by equality of expectations of **all** observables depending on at most `k` coordinates. Line 77 proves `MatchesUpTo.prob_cylinder_eq`; line 244 transfers bounded-local-degree expectations. The existing direction is from the custom predicate to cylinder probabilities. The file does not provide the converse advertised by its mathematical discussion, or a constructor from native joint marginal laws.

This predicate is legitimate: quantifying over every local observable is a distributional condition, not assuming the target Gram-moment estimate. The local-degree proof is useful structure and should remain. However, a user verifying a limited-independent generator normally proves equality of its restricted-coordinate laws or the corresponding independence conditions. They currently have to reprove finite observable decomposition to discharge `MatchesUpTo`.

The surrounding finite-law representation at `FiniteLaw/Expectation.lean:34` is also properly normalized. `FiniteLaw/ToMeasure.lean:24`, line 49, and line 59 prove its PMF, integral, and event-probability bridges. It is therefore inaccurate to call sparse probabilities fake. The missing interoperability goes in the other direction and through products/maps: there is no public conversion from a native finite PMF with round-trip laws, nor a native marginal-law constructor for `MatchesUpTo` in the inspected finite-law files.

Fix: first prove an iff with equality of every restricted-coordinate PMF/measure for sets of size at most `k`; derive a constructor from restricted `iIndepFun` and coordinate `HasLaw` facts. Add native PMF round-trip and product/map identification lemmas. Keep the finite weighted-sum backend internal if it keeps the sparse proof manageable. Replacing every finite-sum proof is unnecessary.

## 5. Medium, low implementation cost: the Gaussian matrix API lacks the entrywise law constructor

Evidence: `NLAlib/RandomMatrix/Gaussian/Basic/GaussianMatrix.lean:96` gives canonical entry laws, line 132 gives flattening, line 157 gives currying, and line 168 gives canonical entry independence. These are enough to prove that arbitrary jointly independent standard Gaussian entries define a matrix with law `gaussianMatrix m n`, but the constructor itself is absent from the inspected RandomMatrix API. By contrast the vector constructor is already present at `NLAlib/Probability/Gaussian/Basic/StandardGaussian.lean:55`.

This is a common entry point into consumers such as `NLAlib/LowRank/RandomizedSVD/GaussianSketch.lean:45`, which takes the whole-matrix `HasLaw` premise. Users with entrywise `HasLaw` and `iIndepFun` must discover the flatten/curry machinery and its measurable equivalences first.

Fix: add `hasLaw_gaussianMatrix_of_iIndepFun` over arbitrary finite row/column index types, with independence indexed by `m × n` (pairwise independence is insufficient). Also provide coordinate-law and joint-independence projections for an arbitrary matrix `HasLaw`. A scratch proof of the constructor compiled using only the existing vector constructor, `gaussianMatrix_eq_map_curry`, and `HasLaw.comp`. This is a small adapter, not a new Gaussian theory.

## 6. Medium: the extended local-variance predicate needs native constructors

Evidence: `NLAlib/Probability/Concentration/Martingales/LocalSecondMoment.lean:62` defines `HasLocalMatrixSecondMoment` through predictable measurability, a.e. PSD, and equality of nonnegative extended set integrals for all deterministic vectors and conditioning-measurable sets. `LocalSecondMomentIntegral.lean:76` proves that this yields the ordinary conditional-square equality when integrability holds. The inspected local-moment files expose the forward conversion, indicator stability, and integrability consequences, but no converse constructor from an actual conditional expectation.

The predicate is defensible and should not be replaced by an unconditional Bochner conditional expectation: it intentionally handles increments without globally integrable squares. Mathlib totalizes conditional expectation to zero outside its integrability domain (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:171`), so simply weakening away those conditions would lose the intended meaning.

Usability problem: a user already working with `V = μ[X² | m]`, or an a.e. equality to that matrix together with square integrability, must manually prove all the extended quadratic-form identities to call `matrix_freedman` (`Freedman.lean:32`). The global intermediate in `FreedmanGlobal.lean:69` partly mitigates this but exposes the exponential parameter rather than the optimized headline interface.

Fix: add a constructor for the canonical `condExp` representative under `m ≤ mΩ`, square integrability and Hermitian hypotheses, then a variant for an a.e.-equal predictable PSD representative. Use Mathlib `setIntegral_condExp` (Basic.lean:231), the existing PSD conditional-expectation lemma, and finite-dimensional quadratic-form integration. Retain the extended predicate for the genuinely local case.

## Native choices to retain

- `gaussianVector` is an abbreviation of `Measure.pi` (`StandardGaussian.lean:41`); scalar and vector laws use `HasLaw`, with independence constructors and projections. `StandardVector.lean:33` identifies the Euclidean pushforward with Mathlib `stdGaussian`. This makes the distinction between the function-space norm and Euclidean norm explicit.
- `rademacherMeasure` is an actual two-point probability measure (`Rademacher/Core.lean:36`), and `rademacherVector` is its product law (line 55). Support and MGF facts are proved from it. A finite sign datatype is also reasonable for combinatorial internal proofs; what matters is identifying its pushed-forward law, not forcing every internal sign representation to be `ℝ`.
- `gaussianMatrix` has an actual product law (Basic/GaussianMatrix.lean:59), a proved `IsGaussian` instance (line 233), and standard `HasGaussianLaw` interoperability. Exact standard law and general Gaussianity remain correctly distinct.
- `Gaussian/Basic/CovarianceRepresentation.lean:49` identifies a centered Gaussian with Mathlib's covariance law, including singular covariance. There is no nonsingularity certificate hiding that case.
- `RandomMatrix/Haar/HaarFrameMeasure.lean:20` builds normalized Mathlib Haar measure; line 46 pushes it to frames; line 87 proves invariant-law uniqueness. This is an actual law construction, not a record containing invariance and the desired consequences as assumptions.
- `Sketching/Structured/SRHT.lean:24` now uses an actual independent product of the shared Rademacher-vector law and the uniform subset law.
- The custom `HasHansonWrightMGF` at `Probability/Concentration/QuadraticForms/CutAverages.lean:329` is an intermediate analytic condition with exponential integrability, not evidence of a circular headline theorem: `HansonWright.lean:179` derives its headline from independent coordinate sub-Gaussian hypotheses.
- Bochner-totalized second-moment definitions (`Probability/Concentration/Basic/MatrixStatistics.lean:25`, line 35) need domain conditions, but the inspected Bernstein consumers derive `MemLp` from boundedness or explicitly require `MemLp 2` (`IntrinsicHermitianBernstein.lean:329`). I did not find the nonintegrable-zero-default being used to bypass those assumptions in these inspected headlines.

## Verification and recommended order

The scratch file `/tmp/f4-probability-compat-audit.lean` compiled with exit code 0 under the shared build lock; final log `/tmp/f4-probability-compat-audit2.log`. It checked native `HasLaw` transport under a.e. changes, derivation of source normalization, the infeasible real-volume totalization example, and the missing entrywise Gaussian matrix constructor. No full build or source modification was performed for this audit.

Do the small law adapters first: Gaussian entrywise constructor, sparse `HasLaw` transport, and PMF/integral identifications for algorithm histories. Add marginal-law constructors for limited independence and the global-to-local variance bridge next. Generalizing directional norm concentration to arbitrary measures is the one larger proof task identified here. These changes would make the existing proofs substantially easier to use without rebuilding the underlying probability theory.
