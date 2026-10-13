# Port manifest (draft)

Generated 2026-10-13 for `docs/FOUNDATIONS_BRIEF.md` §5. Machine-readable: `docs/port/manifest.json` (one entry per Lean content file; aggregators and the declaration-free shim `Probability/Concentration/Matrix/LiebJensen.lean` are excluded). Inputs: `atlas/declarations.json` (signatures, sorry flags, atlas tags), the `import` graph (resolved through aggregators), file sizes and names, `docs/dedup/*.md`, `docs/rclike/*.md`, `docs/DEDUP_FOLLOWUP.md`, `docs/SPARSE_INTEGRATION.md`. No Lean file was edited and no Lean/lake process was run.

Entry schema: `{"module","lines","action","target"(merge/drop),"field","index","sorry","note"}`. For a `keep` that absorbs merges the note starts with `topic file: absorbs …`.

## Totals

- Content files: **1003** (157591 lines).
- `keep` **357**, `merge` **432**, `drop` **68**, `rebuild` **146**.
- Files ported as files (keep, each absorbing its merges): **357** = 35% of today's count. Median topic-file size 316 lines (before ℝ/ℂ dedup); 9 exceed 600 lines, seven are single files already over 600 lines, two are `LogSobolevHerbst` (+58-line `LipschitzConcentration`) and `ProjectionGaps` (+ the ℂ projection files).
- Rebuild set: 146 files (115 Sketching/Sparse, 5 Solvers, 26 F2 law/measurability files), rewritten in the new repository rather than copied.

## Per top-level directory

| directory | files | lines | keep | merge | drop | rebuild | files after port |
|---|---:|---:|---:|---:|---:|---:|---:|
| Estimation | 13 | 2231 | 7 | 6 | 0 | 0 | 7 (+0 rebuild) |
| ForMathlib | 91 | 7585 | 29 | 62 | 0 | 0 | 29 (+0 rebuild) |
| Krylov | 31 | 7750 | 23 | 7 | 1 | 0 | 23 (+0 rebuild) |
| LowRank | 34 | 6753 | 12 | 12 | 3 | 7 | 12 (+7 rebuild) |
| Matrix | 510 | 63549 | 178 | 265 | 63 | 4 | 178 (+4 rebuild) |
| Polynomial | 28 | 4822 | 15 | 13 | 0 | 0 | 15 (+0 rebuild) |
| Probability | 114 | 22569 | 62 | 49 | 0 | 3 | 62 (+3 rebuild) |
| RandomMatrix | 45 | 10792 | 23 | 11 | 0 | 11 | 23 (+11 rebuild) |
| Sketching | 132 | 30441 | 8 | 7 | 1 | 116 | 8 (+116 rebuild) |
| Solvers | 5 | 1099 | 0 | 0 | 0 | 5 | 0 (+5 rebuild) |
| **total** | 1003 | 157591 | 357 | 432 | 68 | 146 | 357 (+146) |

Matrix by subdirectory:

| Matrix/… | files | keep | merge | drop | rebuild |
|---|---:|---:|---:|---:|---:|
| Basic | 31 | 13 | 17 | 1 | 0 |
| Calculus | 11 | 9 | 1 | 1 | 0 |
| Factorizations | 37 | 17 | 17 | 3 | 0 |
| Functions | 21 | 9 | 10 | 2 | 0 |
| Inequalities | 81 | 24 | 45 | 12 | 0 |
| Norms | 36 | 14 | 17 | 5 | 0 |
| OperatorTheory | 19 | 6 | 12 | 1 | 0 |
| Perturbation | 65 | 24 | 34 | 7 | 0 |
| Spectral | 139 | 45 | 73 | 21 | 0 |
| Structured | 15 | 4 | 6 | 3 | 2 |
| Subspaces | 55 | 13 | 33 | 7 | 2 |

## Method

1. **rebuild** (mechanical): every file under `Sketching/Sparse/` (F3); every file under `Solvers/` (expectations are finite weighted path sums, `expErr`); every file that `grep` finds using `Matrix.of.symm`, stating a law as `….map … = gaussianMatrix …`, or defining an `_of_map_eq` wrapper (F2); plus the three definition files F2 rewrites (`IsStandardGaussian`, `IsRademacher`, and the `Matrix ℂ` measurable-space instances in `MatrixStatistics`).
2. **drop** (mechanical candidates, then reviewed by hand): single-theorem `*Toolkit` bundles (the target is the file holding most of the bundled components, computed from the theorem names the bundle cites); the ℂ/ℝ twins of the F1 spectral core and of the Norms/Subspaces/Functions vocabulary that F1 or the RCLike round makes generic; Fin→Fintype transport files; two leaves with no importer that duplicate another file. Every drop names the file that makes it redundant (`target`), and if that file is itself merged, the note says where it ends up.
3. **merge**: the remaining files are clustered per directory (ForMathlib per second-level area; Estimation and the non-Sparse Sketching per top level), within hand-written topic groups for the large Matrix directories (`Interlacing*`, `Gershgorin*`/diagonal dominance, real Schur, `Sylvester*`, `Schatten*`, CS/oblique, `LeastSquares*`, `Pseudoinverse*`, `SimpleEigenvalue*`, `DavisKahan*`, `Wedin*`, `Hadamard*`, `Majorization*`, Cholesky/QR/rank-revealing/polar, …). Clusters grow by joining a cluster under 200 lines to a neighbour (import edge first, then same topic) while the result stays ≤ 500 lines; leftovers under 120 lines join an import neighbour up to 700. Every join is checked against the import graph so that no merged file creates an import cycle (the final quotient graph is acyclic). The target of a cluster is its largest file (×1.5 if it carries an atlas tag; `Basic`/`Core` files win; toolkits/transports never). ℝ/ℂ twin pairs that are merged rather than dropped are pre-joined and counted at half size.
4. **keep**: the cluster targets, which absorb their merges.
5. `field` from the declaration signatures (`RCLike`/`𝕜` → 𝕜; ℂ in ≥ 40% of signatures, or more often than ℝ → ℂ; else ℝ; none). `index`: `Fin` if signatures use `Matrix (Fin …)`/`(Fin n) →` and no `Fintype` binder, `Fintype` for the converse, `mixed` for both. `sorry`: the file itself contains `sorry` (11 files, all catalogued scaffolds).

## Rebuild list

### F2 (random matrices on `Matrix`, one `HasLaw` interface): 26 files

| file | lines | what changes |
|---|---:|---|
| `LowRank.Nystrom.GaussianNystrom` | 154 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `LowRank.Nystrom.RawGaussianNystrom` | 340 | F2: uses Matrix.of.symm, states laws as μ.map X = gaussianMatrix; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ |
| `LowRank.Nystrom.Structural` | 209 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `LowRank.RandomizedSVD.GaussianSketch` | 310 | F2: uses Matrix.of.symm, states laws as μ.map X = gaussianMatrix; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ |
| `LowRank.RandomizedSVD.OptimalError` | 316 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `LowRank.RangeFinding.ExpectedPower` | 166 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `LowRank.RangeFinding.SpectralRangeFinder` | 427 | F2: uses Matrix.of.symm, states laws as μ.map X = gaussianMatrix; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ |
| `Matrix.Structured.Measurable` | 195 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance; F2 moves its entrywise-measurability bridge into ForMathlib/MeasureTheory/Matrix.lean and this file shrinks to corollaries |
| `Matrix.Structured.SpectralMeasurable` | 40 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `Matrix.Subspaces.CanonicalQR` | 252 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `Matrix.Subspaces.Stiefel` | 194 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance; F2 deletes its orthogonalGroup Borel instance |
| `Probability.Concentration.Basic.MatrixStatistics` | 72 | F2 deletes matrixMeasurableSpace/matrixBorelSpace; the concentration layer rebuilds on the global Matrix instance |
| `Probability.Gaussian.Basic.StandardGaussian` | 150 | IsStandardGaussian becomes HasLaw/abbrev (F2) |
| `Probability.Rademacher.Core` | 152 | IsRademacher becomes HasLaw/abbrev (F2) |
| `RandomMatrix.Gaussian.Basic.GaussianMatrix` | 242 | F2: uses Matrix.of.symm, states laws as μ.map X = gaussianMatrix; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ |
| `RandomMatrix.Gaussian.Invariance.Invariance` | 307 | F2: uses Matrix.of.symm, states laws as μ.map X = gaussianMatrix; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ |
| `RandomMatrix.Gaussian.Invariance.LinearImage` | 191 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `RandomMatrix.Gaussian.InverseMoments.Mean` | 250 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `RandomMatrix.Gaussian.InverseMoments.OffDiagonal` | 435 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `RandomMatrix.Gaussian.InverseMoments.Probe` | 347 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `RandomMatrix.Gaussian.InverseMoments.Residual` | 157 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |
| `RandomMatrix.Gaussian.Moments.Conditioning` | 287 | F2: uses Matrix.of.symm, states laws as μ.map X = gaussianMatrix, has _of_map_eq wrappers; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ |
| `RandomMatrix.Gaussian.Moments.LogOverlap` | 215 | F2: states laws as μ.map X = gaussianMatrix; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ |
| `RandomMatrix.Gaussian.Spectral.SketchRank` | 305 | F2: uses Matrix.of.symm, states laws as μ.map X = gaussianMatrix, has _of_map_eq wrappers; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ |
| `RandomMatrix.Haar.HaarQR` | 122 | F2: uses Matrix.of.symm, states laws as μ.map X = gaussianMatrix; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ |
| `Sketching.Gaussian.GaussianEmbedding` | 188 | F2: uses Matrix.of.symm; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance |

### Solvers finite-sum probability: 5 files

| file | lines | what changes |
|---|---:|---|
| `Solvers.Kaczmarz.Core` | 262 | Solvers finite-sum probability (expErr as weighted path sums): rebuild on Measure/PMF |
| `Solvers.Kaczmarz.KaczmarzExtensions` | 320 | Solvers finite-sum probability (expErr as weighted path sums): rebuild on Measure/PMF |
| `Solvers.Kaczmarz.KaczmarzProbability` | 96 | Solvers finite-sum probability (expErr as weighted path sums): rebuild on Measure/PMF |
| `Solvers.Kaczmarz.KaczmarzRowSpace` | 198 | Solvers finite-sum probability (expErr as weighted path sums): rebuild on Measure/PMF |
| `Solvers.SketchAndProject.Core` | 223 | Solvers finite-sum probability (expErr as weighted path sums): rebuild on Measure/PMF |

### F3 (Sketching/Sparse): 115 files, 27615 lines

All marked `rebuild`; `docs/SKETCH_INTERFACE.md` (F3) will split them into rebuild vs drop and name the 3–4 reusable lemmas. By subdirectory:

| Sparse/… | files | lines |
|---|---:|---:|
| Bands (top) | 9 | 2053 |
| Bands/Directional | 8 | 2706 |
| Bands/Heavy | 13 | 2631 |
| Bands/Light | 20 | 5531 |
| Bands/Mixed | 3 | 1011 |
| CountSketch (top) | 1 | 112 |
| CountSketchExpectation (top) | 1 | 106 |
| CountSketchMoments (top) | 1 | 113 |
| CountSketchTail (top) | 1 | 96 |
| FiniteLaw (top) | 6 | 1049 |
| FockModel (top) | 10 | 2675 |
| IIDComparison (top) | 18 | 4738 |
| MomentMethod (top) | 17 | 3488 |
| SparseEmbedding (top) | 1 | 147 |
| SparseEmbeddingTransport (top) | 1 | 79 |
| SparseFiniteIndex (top) | 1 | 114 |
| SparseLaws (top) | 1 | 64 |
| SparseStack (top) | 1 | 424 |
| SparseStackLaw (top) | 1 | 159 |
| UniformSparse (top) | 1 | 319 |

Non-Sparse files whose only importers are in Sparse (kept, flagged in their notes): `ForMathlib.Algebra.OffDiagonalSums`, `ForMathlib.Analysis.NormSumSq`, `ForMathlib.Probability.UniformCollision`, `Matrix.Functions.TracePowerConvexity`, `Matrix.Norms.EntryBounds`, `Matrix.Spectral.TracePowerBounds`, `Matrix.Subspaces.FrameFourthContractions`.

Files that mention `gaussianMatrix` but integrate against it directly are `keep` with the F2 note "primary statement kept, add `_of_hasLaw` corollary" (brief §2): `HutchinsonLaws`, `LinearForms`, `Lipschitz`, `LipschitzConcentration`, `PolynomialGrowth`, `CutoffDerivativeIntegrability`, `CutoffIntegrability`, `DiagonalLaw`, `FrobeniusMoments`, `GaussianWeakInequality`, `HardEdgeEndpoint`, `LambdaMinTail`, `OperatorHardEdge`, `RegularizedApproximation`, `RegularizedIntegrability`, `ResolventLimit`, `SpectralProbe`, `SpectralTail`, `UnshiftedWeakInequality`, `ApproxMultiplication`, `FourthMoment`, `SecondMoment`, `Chevet`, `Deviation`, `Gordon`, `SmallBall`, `SpectralSecondMoment`, `SimpleSpectrum`, `JL`.

## Drops (all reviewed by hand)

| file | lines | redundant because of | reason |
|---|---:|---|---|
| `Krylov.Spaces.ComplexBlock` | 59 | `Krylov/Spaces/Block.lean` | rclike D8: `blockKrylovSpace` already over any field; delete `complexBlockKrylovSpace` |
| `LowRank.Cholesky.CholeskyHistories` | 198 | `LowRank/Cholesky/ComplexCholeskyHistories.lean` | ℝ twin (P_randnla, rclike D12): RPCholesky keeper built over 𝕜 from the ℂ stack; ~45 real copies deleted |
| `LowRank.Cholesky.RandomPivotedCholesky` | 160 | `LowRank/Cholesky/ComplexRandomPivotedCholesky.lean` | ℝ twin (rclike D12): keeper over 𝕜 from the ℂ stack; move tag rpcholesky |
| `LowRank.Sampling.VolumeSampling` | 237 | `LowRank/Sampling/ComplexVolumeSamplingLaw.lean` | ℝ twin (randnla#6, rclike D12): keeper over 𝕜 from the ℂ stack; move tag volume-sampling |
| `Matrix.Basic.ComplexFullRowInverse` | 35 | `Matrix/Basic/Pseudoinverse.lean` | `pinvR` over 𝕜 (rclike §1.1) is the full-row-rank right inverse |
| `Matrix.Calculus.DeterminantDerivativeFinite` | 73 | `Matrix/Calculus/DeterminantDerivative.lean` | Fin→Fintype transport; state DeterminantDerivative over Fintype (move tag determinant-derivative) |
| `Matrix.Factorizations.CholeskyToolkit` | 40 | `Matrix/Factorizations/CholeskyStep.lean` | bundle of `@NLAlib.*` components (brief §4); components are in CholeskyDefinite, CholeskyCharacterization, CholeskySemidefinite; move atlas tag cholesky-decomposition to the main theorem; (redundant via CholeskyDefinite, folded into CholeskyStep) |
| `Matrix.Factorizations.PolarToolkit` | 54 | `Matrix/Factorizations/PolarDecomposition.lean` | bundle of `@NLAlib.*` components (brief §4); components are in PolarDecomposition, NearestPolar; move atlas tag polar-decomposition to the main theorem |
| `Matrix.Factorizations.ProcrustesToolkit` | 52 | `Matrix/Factorizations/ProcrustesRotations.lean` | bundle of `@NLAlib.*` components (brief §4); components are in ProcrustesRotations, ScaledOrthogonal, Procrustes; move atlas tag orthogonal-procrustes to the main theorem |
| `Matrix.Functions.ComplexDiagonalFilter` | 122 | `Matrix/Functions/PolynomialCalculus.lean` | ℝ/ℂ twin (DEDUP_FOLLOWUP); `map ofReal` bridges vanish over 𝕜; (redundant via DiagonalFilter, folded into PolynomialCalculus) |
| `Matrix.Functions.RealComplexCFC` | 96 | `Matrix/Functions/HermitianCalculus.lean` | F1 twin list: ℝ→ℂ CFC complexification; with 𝕜-generic statements (LoewnerHeinz, HermitianPartConverse) real users need no embedding |
| `Matrix.Inequalities.BlockContractionToolkit` | 64 | `Matrix/Inequalities/BlockOrderConsequences.lean` | bundle of `@NLAlib.*` components (brief §4); components are in BlockOrderConsequences, BlockStrictContraction, BlockQuadratic, BlockContraction; move atlas tag psd-block-contraction to the main theorem |
| `Matrix.Inequalities.ComplexDiagonalMajorization` | 81 | `Matrix/Inequalities/SchurHornProjection.lean` | ℂ Schur diagonal majorization; Schur over 𝕜; (redundant via Schur, folded into SchurHornProjection) |
| `Matrix.Inequalities.ComplexTraceTail` | 52 | `Matrix/Inequalities/TraceTail.lean` | ℝ/ℂ twin (DEDUP_FOLLOWUP): TraceTail wrappers collapse to the 𝕜 core once Courant–Fischer is generic |
| `Matrix.Inequalities.DeterminantConvexityToolkit` | 54 | `Matrix/Inequalities/FiniteExponentialGram.lean` | bundle of `@NLAlib.*` components (brief §4); components are in TraceInverseConvexity, MinkowskiDeterminant, LogDetConcavity; move atlas tag log-det-concavity to the main theorem; (redundant via TraceInverseConvexity, folded into FiniteExponentialGram) |
| `Matrix.Inequalities.DeterminantInequalityToolkit` | 65 | `Matrix/Inequalities/PrincipalMinorProductBounds.lean` | bundle of `@NLAlib.*` components (brief §4); components are in SzaszDeterminant, PrincipalOverlapDeterminant, FischerDeterminant, HadamardDeterminant; move atlas tag hadamard-fischer-inequalities to the main theorem; (redundant via SzaszDeterminant, folded into PrincipalMinorProductBounds) |
| `Matrix.Inequalities.HadamardToolkit` | 68 | `Matrix/Inequalities/HadamardPowerSeries.lean` | bundle of `@NLAlib.*` components (brief §4); components are in HadamardPowerSeries, HadamardOrder, HadamardInverse, HadamardMinimumSpectrum; move atlas tag schur-product-inequalities to the main theorem |
| `Matrix.Inequalities.HornProductToolkit` | 39 | `Matrix/Inequalities/Mirsky.lean` | bundle of `@NLAlib.*` components (brief §4); components are in HornPowerSums, ProductSingularValues; move atlas tag horn-product-inequality to the main theorem; (redundant via HornPowerSums, folded into Mirsky) |
| `Matrix.Inequalities.KyFanNormToolkit` | 94 | `Matrix/Inequalities/KyFanNorms.lean` | bundle of `@NLAlib.*` components (brief §4); components are in KyFanNorms, NuclearNorm, NuclearPSD; move atlas tag ky-fan-norms-def to the main theorem |
| `Matrix.Inequalities.KyFanToolkit` | 78 | `Matrix/Inequalities/KyFan.lean` | bundle of `@NLAlib.*` components (brief §4); components are in KyFan, KyFanAttainment, KyFanSums, Projections; move atlas tag ky-fan-maximum-principle to the main theorem |
| `Matrix.Inequalities.LidskiiToolkit` | 62 | `Matrix/Inequalities/Mirsky.lean` | bundle of `@NLAlib.*` components (brief §4); components are in Lidskii, MirskyPadded, Mirsky, FanDominance; move atlas tag lidskii to the main theorem; (redundant via Lidskii, folded into Mirsky) |
| `Matrix.Inequalities.MajorizationToolkit` | 35 | `Matrix/Inequalities/MajorizationConvex.lean` | bundle of `@NLAlib.*` components (brief §4); components are in MajorizationConvex, MajorizationHLP; move atlas tag majorization-def to the main theorem |
| `Matrix.Inequalities.PlaneRotationCoordinates` | 91 | `Matrix/Inequalities/PlaneRotationDerivative.lean` | no importer, no tag: Schur–Horn stationarity goes through PlaneRotationDerivative |
| `Matrix.Norms.ComplexFrobenius` | 46 | `Matrix/Norms/Frobenius.lean` | F1: deleted; generic bridge `frobNorm_eq_norm` to Mathlib Frobenius norm in Norms/Frobenius |
| `Matrix.Norms.ComplexFrobeniusTrace` | 40 | `Matrix/Norms/Frobenius.lean` | ℂ copy of `frobSq_eq_trace`/column sums; `frobSq` over 𝕜 + `frobNorm_eq_norm` cover it |
| `Matrix.Norms.InvariantNormToolkit` | 44 | `Matrix/Norms/InvariantNormRepresentation.lean` | bundle of `@NLAlib.*` components (brief §4); components are in FanDominance, InvariantNormRepresentation; move atlas tag unitarily-invariant-norm-def to the main theorem; (redundant via FanDominance, folded into InvariantNormRepresentation) |
| `Matrix.Norms.RealComplexNorm` | 45 | `Matrix/Norms/Core.lean` | F1 twin list: specNorm over 𝕜 makes the ℝ→ℂ operator-norm bridge unnecessary (users MatrixPowerReal, SRHT repoint) |
| `Matrix.Norms.SchattenToolkit` | 91 | `Matrix/Norms/SchattenEndpoints.lean` | bundle of `@NLAlib.*` components (brief §4); components are in SchattenInvariant, Schatten, SchattenComparison, SchattenEndpoints; move atlas tag schatten-norms-def to the main theorem; (redundant via SchattenInvariant, folded into SchattenEndpoints) |
| `Matrix.OperatorTheory.JensenReflectionAlgebra` | 53 | `Matrix/OperatorTheory/LoewnerHeinz.lean` | no importer: public copy of the private `isometry_reflection_identities` there; (redundant via JensenIsometricCompression, folded into LoewnerHeinz) |
| `Matrix.Perturbation.ComplexEmbedding` | 63 | `Matrix/Basic/QuadForm.lean` | F1 twin list: `|re x*Hx| ≤ ‖H‖‖x‖²` and Gram-error norm bounds are `quadForm`/specNorm lemmas over 𝕜 |
| `Matrix.Perturbation.ConditionNumberToolkit` | 52 | `Matrix/Perturbation/ConditionNumber.lean` | bundle of `@NLAlib.*` components (brief §4); components are in ConditionNumber, DistanceToSingularity; move atlas tag condition-number-def to the main theorem |
| `Matrix.Perturbation.DavisKahanToolkit` | 158 | `Matrix/Perturbation/EigenspaceProjector.lean` | bundle of `@NLAlib.*` components (brief §4); components are in DavisKahanFrames, DavisKahanBounds, DavisKahan; move atlas tag davis-kahan-sin-theta to the main theorem; (redundant via DavisKahanFrames, folded into EigenspaceProjector) |
| `Matrix.Perturbation.EigenvaluePerturbationToolkit` | 51 | `Matrix/Perturbation/EigenvalueTrace.lean` | bundle of `@NLAlib.*` components (brief §4); components are in EigenvaluePerturbation, EigenvalueTrace; move atlas tag eigenvalue-perturbation-symmetric to the main theorem; (redundant via EigenvaluePerturbation, folded into EigenvalueTrace) |
| `Matrix.Perturbation.EigenvalueResidualToolkit` | 55 | `Matrix/Perturbation/ResidualBounds.lean` | bundle of `@NLAlib.*` components (brief §4); components are in ResidualBounds, EigenspaceProjector, RayleighDerivative; move atlas tag eigenvalue-residual-bounds to the main theorem |
| `Matrix.Perturbation.SimpleEigenvalueToolkit` | 57 | `Matrix/Perturbation/SimpleEigenvaluePersistence.lean` | bundle of `@NLAlib.*` components (brief §4); components are in SimpleEigenvalueReal, SimpleEigenvaluePerturbation, GeneralizedEigenPairing, EigenvectorDeflationSpectrum; move atlas tag simple-eigenvalue-perturbation to the main theorem; (redundant via SimpleEigenvalueReal, folded into SimpleEigenvaluePersistence) |
| `Matrix.Perturbation.WedinFiniteIndex` | 148 | `Matrix/Perturbation/Wedin.lean` | Fin→Fintype transport of Wedin; state WedinBounds over Fintype after F1 (move tag wedin-sin-theta); (redundant via WedinBounds, folded into Wedin) |
| `Matrix.Spectral.ComplexBestRankApproximation` | 59 | `Matrix/Spectral/EckartYoung.lean` | F1 ℂ twin: `complexBestRankFrobSq` absorbed by `bestRankFrobSq` over 𝕜 (rclike C6); move tag volume-sampling |
| `Matrix.Spectral.ComplexEckartYoung` | 133 | `Matrix/Spectral/EckartYoung.lean` | F1 ℂ twin: one Eckart–Young over 𝕜 |
| `Matrix.Spectral.ComplexGramTruncation` | 149 | `Matrix/Spectral/EckartYoung.lean` | F1 ℂ twin: `complexTruncatedSVD`/`complexGramTail` absorbed by `truncatedSVD`/`singularValueTailSq` over 𝕜 (rclike C6) |
| `Matrix.Spectral.ComplexRayleigh` | 67 | `Matrix/Basic/QuadForm.lean` | ℂ Rayleigh expansions; `quadForm`/`rayleighQuotient` over 𝕜 (rclike D3) make them redundant; only user ComplexVariationalPrinciple is dropped |
| `Matrix.Spectral.ComplexRectangularSVD` | 83 | `Matrix/Spectral/SVD.lean` | F1: `exists_complex_rectangular_svd` deleted; `exists_isSVD` over 𝕜 and Fintype |
| `Matrix.Spectral.ComplexSingularTransport` | 124 | `Matrix/Spectral/SvdBlocks.lean` | F1 ℂ twin: `complex_singularValues_{isometry_mul,mul_unitary}` merge into `singularValues_isometry_mul`/`_mul_orthogonal`, `_zero_eq_norm` into `singularValues_zero_eq_specNorm` (SpectralBounds); (redundant via SingularValueInvariance, folded into SvdBlocks) |
| `Matrix.Spectral.ComplexSquareSingularBasis` | 77 | `Matrix/Spectral/SVD.lean` | F1 ℂ twin of SquareSingularBasis; subsumed by `exists_isSVD` over 𝕜 (rclike DESIGN §1.1) |
| `Matrix.Spectral.ComplexVariationalExtrema` | 255 | `Matrix/Spectral/CourantFischer.lean` | F1 ℂ twin: attained extrema are the 𝕜 Courant–Fischer equational form (`eigenvalues₀ k = ⨆ … ⨅ …`); move tag courant-fischer |
| `Matrix.Spectral.ComplexVariationalPrinciple` | 177 | `Matrix/Spectral/CourantFischer.lean` | F1 ℂ twin: Courant–Fischer stated once over 𝕜 in CourantFischer (plus the equational form); ComplexTraceTail/ComplexVariationalExtrema users repoint |
| `Matrix.Spectral.CongruenceToolkit` | 52 | `Matrix/Spectral/SemidefiniteCongruence.lean` | bundle of `@NLAlib.*` components (brief §4); components are in SemidefiniteCongruence, DefiniteCongruence, IndefiniteCongruence; move atlas tag simultaneous-diagonalization-congruence to the main theorem |
| `Matrix.Spectral.DiagonalizableToolkit` | 55 | `Matrix/Spectral/Diagonalizable.lean` | bundle of `@NLAlib.*` components (brief §4); components are in Diagonalizable, DiagonalizableBlocks, DiagonalizablePrincipal; move atlas tag diagonalizable-def to the main theorem |
| `Matrix.Spectral.FiniteIndexTransport` | 133 | `Matrix/Spectral/SVD.lean` | F1 deletes FiniteIndexTransport: IsSVD/rectDiag Fintype-indexed; `moorePenroseInverse_reindex` and best-rank transports become the core statements (SVD, EckartYoung, RankNorm) |
| `Matrix.Spectral.GershgorinToolkit` | 80 | `Matrix/Spectral/DiagonalDominanceStability.lean` | bundle of `@NLAlib.*` components (brief §4); components are in DiagonalDominanceCorollaries, GershgorinCounting, GershgorinBasic, DiagonalDominanceStability; move atlas tag gershgorin-diagonal-dominance to the main theorem; (redundant via DiagonalDominanceCorollaries, folded into DiagonalDominanceStability) |
| `Matrix.Spectral.InterlacingConverseToolkit` | 49 | `Matrix/Spectral/InterlacingSymmetricConverse.lean` | bundle of `@NLAlib.*` components (brief §4); components are in InterlacingSymmetricConverse; move atlas tag interlacing-converse to the main theorem |
| `Matrix.Spectral.LeftRightEigenvectorToolkit` | 61 | `Matrix/Spectral/EigenvectorPairing.lean` | bundle of `@NLAlib.*` components (brief §4); components are in EigenvectorPairing, EigenvectorDeflationConverse, GeneralizedEigenPairing, EigenvectorDeflation; move atlas tag left-right-eigenvectors to the main theorem |
| `Matrix.Spectral.MatrixPowerToolkit` | 43 | `Matrix/Spectral/MatrixPowerBounds.lean` | bundle of `@NLAlib.*` components (brief §4); components are in MatrixPowerReal, MatrixPowerBounded; move atlas tag matrix-power-convergence to the main theorem; (redundant via MatrixPowerReal, folded into MatrixPowerBounds) |
| `Matrix.Spectral.SchurToolkit` | 84 | `Matrix/Spectral/SchurFrobenius.lean` | bundle of `@NLAlib.*` components (brief §4); components are in SchurFrobenius, RealSpectrumSchur, SchurDensity, ComplexQZ; move atlas tag schur-triangularization to the main theorem |
| `Matrix.Spectral.SigmaMinTransport` | 38 | `Matrix/Spectral/SpectralBounds.lean` | Fin→Fintype transport (dedup F1 #8): restate `sigmaMin_eq_singularValues_last` over Fintype in SpectralBounds |
| `Matrix.Spectral.SimultaneousToolkit` | 84 | `Matrix/Spectral/SimultaneousNormal.lean` | bundle of `@NLAlib.*` components (brief §4); components are in SimultaneousNormal, SimultaneousDiagonalization, SimultaneousTriangularization, CommutingSpectra; move atlas tag simultaneous-diagonalization to the main theorem |
| `Matrix.Spectral.SylvesterCriterionToolkit` | 38 | `Matrix/Spectral/SylvesterCriterion.lean` | bundle of `@NLAlib.*` components (brief §4); components are in SylvesterCriterion, PrincipalMinorPSD; move atlas tag sylvester-criterion to the main theorem |
| `Matrix.Spectral.SylvesterToolkit` | 63 | `Matrix/Spectral/SylvesterQualitative.lean` | bundle of `@NLAlib.*` components (brief §4); components are in SylvesterQualitative, SylvesterBlocks, SylvesterSimilarity, PrimaryTriangularization; move atlas tag sylvester-equation to the main theorem |
| `Matrix.Structured.CauchyDeterminantFinite` | 35 | `Matrix/Structured/StructuredMatrices.lean` | Fin→Fintype transport of the Cauchy determinant; state it over Fintype |
| `Matrix.Structured.KroneckerToolkit` | 88 | `Matrix/Structured/KroneckerSpectrum.lean` | bundle of `@NLAlib.*` components (brief §4); components are in KroneckerSpectrum, KroneckerSingularValues, KroneckerNormRank, KroneckerIdentities; move atlas tag kronecker-spectral to the main theorem |
| `Matrix.Structured.StructuredToolkit` | 43 | `Matrix/Structured/StructuredMatrices.lean` | bundle of `@NLAlib.*` components (brief §4); components are in StructuredMatrices, CirculantCharacterization; move atlas tag structured-matrices-def to the main theorem |
| `Matrix.Subspaces.CSToolkit` | 75 | `Matrix/Subspaces/ObliqueProjectionNorms.lean` | bundle of `@NLAlib.*` components (brief §4); components are in ObliqueProjectionNorms, CSRank, CSDecomposition, ObliqueProjectionSecant; move atlas tag cs-decomposition to the main theorem |
| `Matrix.Subspaces.ComplexCSToolkit` | 73 | `Matrix/Subspaces/CSRank.lean` | bundle of `@NLAlib.*` components (brief §4); components are in ComplexCSRank, ComplexObliqueSpectrum, ComplexObliqueSecant, ComplexCSDecomposition; move atlas tag cs-decomposition to the main theorem; (redundant via ComplexCSRank, folded into CSRank) |
| `Matrix.Subspaces.ComplexFrameTransport` | 85 | `Matrix/Subspaces/PrincipalAngles.lean` | ℝ→ℂ frame transport; principal angles over 𝕜 (rclike C7) |
| `Matrix.Subspaces.ComplexIdempotentRealForm` | 84 | `Matrix/Subspaces/ObliqueProjectionSpectrum.lean` | reduction of ℂ idempotents to ℝ ones; unnecessary once oblique theory is over 𝕜; (redundant via ObliqueProjectionCanonical, folded into ObliqueProjectionSpectrum) |
| `Matrix.Subspaces.ComplexVolumeProjection` | 115 | `Matrix/Basic/MoorePenroseTransformations.lean` | rclike D11: `complexColumnProjector = B * moorePenroseInverse B`; delete; (redundant via MoorePenroseProjector, folded into MoorePenroseTransformations) |
| `Matrix.Subspaces.ComplexVolumeProjectorTrace` | 47 | `Matrix/Subspaces/ProjectorTrace.lean` | ℂ twin of ProjectorTrace (projector trace = rank) over 𝕜 |
| `Matrix.Subspaces.PrincipalAngleToolkit` | 78 | `Matrix/Subspaces/PrincipalAngleDefinitions.lean` | bundle of `@NLAlib.*` components (brief §4); components are in PrincipalAngleDefinitions, PrincipalAngleTangent, PrincipalAngleInvariance, PrincipalAngleMaximum; move atlas tag principal-angles-def to the main theorem |
| `Sketching.Properties.SubspaceEmbedding.FiniteIndexTransport` | 37 | `Sketching/Properties/SubspaceEmbedding/Basic.lean` | relabelling transport; only consumer is Sparse (rebuild); (redundant via SingularValueEmbedding, folded into Basic); only consumers are in Sketching/Sparse (rebuild) |

Not dropped although the mechanical rules flagged them:

- `Matrix.Spectral.InterlacingReindex`: reindex transport, but `InterlacingSymmetricConverse` consumes it: merged into that topic file, to disappear when the construction is stated over Fintype (the brief's own example).
- `Matrix.Spectral.NormalToolkit`: three genuine normal-matrix characterizations besides the bundle.
- `Matrix.Spectral.SingularInterlacingToolkit`: delete-row/column corollaries, not a bundle.
- `Matrix.Inequalities.HermitianPartToolkit`: genuine characterization besides the bundle.
- `Matrix.Inequalities.MajorizationProperties`: six genuine `sumLargest`/majorization lemmas despite the name; six importers.
- `Matrix.Perturbation.LeastSquaresToolkit`: genuine relative-error corollaries besides the bundle.
- `Matrix.Norms.Reindex`: reindex *invariance* lemmas (`specNorm_reindex`, …) are API, not transport.
- `Matrix.Structured.WalshFin`: Fin-label Walsh transform that SRHT uses.
- `Matrix.Spectral.RealSchur*, RealNormal*, RealQZ, RealSimilarityDescent, ComplexQZ`: genuinely real (or complex) theory, not twins of a generic theorem.
- `Matrix.Subspaces.Complex{CS,Oblique,Gram}* , LowRank complex stacks`: ℝ/ℂ twin families whose ℂ file carries content the ℝ file lacks: `merge` into the ℝ sibling (CS, oblique, Gram isometry, subspace iteration, polynomial filter) or kept as the 𝕜 keeper with the ℝ file dropped (RPCholesky, volume sampling, rclike D12).
- `proof scaffolding consumed only inside its directory`: folded into its topic file (merge), never dropped: dropping it would orphan the theorem it proves.

## Twenty largest `keep` files

| file | own lines | after merges | absorbs | note |
|---|---:|---:|---:|---|
| `Probability.ChiSquare.ChiSquare` | 771 | 771 | 0 |  |
| `Matrix.Spectral.Core` | 695 | 695 | 0 | F1 spectral core: generic over 𝕜 and Fintype after F1 |
| `Matrix.Subspaces.Projections` | 692 | 692 | 0 | F1 spectral core: generic over 𝕜 and Fintype after F1 |
| `Probability.Gaussian.Comparison.GordonMinimax` | 691 | 691 | 0 |  |
| `RandomMatrix.Gaussian.Spectral.SpectralSecondMoment` | 679 | 679 | 0 | F2: gaussianMatrix becomes a Measure on Matrix; primary statement kept, add `_of_hasLaw` corollary |
| `Matrix.Spectral.SVD` | 660 | 660 | 0 | F1 spectral core: generic over 𝕜 and Fintype after F1 |
| `RandomMatrix.Gaussian.Spectral.Gordon` | 618 | 618 | 0 | F2: gaussianMatrix becomes a Measure on Matrix; primary statement kept, add `_of_hasLaw` corollary |
| `Probability.Gaussian.Concentration.LogSobolevHerbst` | 586 | 644 | 1 |  |
| `Matrix.Factorizations.LU` | 569 | 569 | 0 |  |
| `Matrix.Factorizations.GramSchmidt` | 564 | 564 | 0 | contains catalogued sorry scaffold |
| `Probability.Gaussian.Calculus.OrnsteinUhlenbeckEntropy` | 542 | 542 | 0 |  |
| `Probability.SubGaussian.CenteredSquare` | 523 | 523 | 0 |  |
| `Probability.SubGaussian.EvenMoments` | 516 | 516 | 0 |  |
| `Probability.Gaussian.Concentration.LogSobolevOneDim` | 512 | 512 | 0 |  |
| `Matrix.Norms.Frobenius` | 491 | 491 | 0 | F1 spectral core: generic over 𝕜 and Fintype after F1 |
| `Matrix.Calculus.InversePowerLimit` | 469 | 469 | 0 |  |
| `Matrix.Factorizations.QR` | 467 | 467 | 0 |  |
| `Krylov.Spectral.Ritz` | 465 | 465 | 0 |  |
| `Polynomial.Chebyshev.Markov` | 461 | 461 | 0 |  |
| `Matrix.Calculus.UnshiftedGramSoftMin` | 459 | 459 | 0 |  |

## Items for the port (brief §4), noticed while drafting

- Bundle theorems inside non-toolkit files: `CauchyBinet`, `JacobiMinor`, `LULeadingRank`, `BauerFike`, `NormalToolkit`, `RealOrthogonalDescent`, `ComplexObliqueSpectrum`. Delete at port; move their full atlas tags to the main theorem (DEDUP_FOLLOWUP, "atlas-tag policy").
- Atlas tags carried by dropped files must move: every drop note that says "move tag …" lists the id.
- Sorry scaffolds (11 files): `Krylov.Processes.Bidiagonalization`, `Krylov.Processes.LanczosRecurrence`, `Krylov.Solvers.CGRecurrence`, `Krylov.Spectral.PowerMethod`, `Krylov.Spectral.QRAlgorithm`, `LowRank.Cholesky.PartialCholesky`, `Matrix.Factorizations.Cholesky`, `Matrix.Factorizations.Givens`, `Matrix.Factorizations.GramSchmidt`, `Matrix.Factorizations.Hessenberg`, `Matrix.Spectral.Inertia`.
- The real `CholeskyHistories`/`RandomPivotedCholesky`/`VolumeSampling` drops assume the 𝕜 keeper is built from the ℂ stacks (rclike D12); the ℂ files then lose their `Complex` prefix.
- `ForMathlib/*` clusters follow Mathlib areas; upstreaming candidates named in DEDUP_FOLLOWUP (GramSchmidt, Fourier*, InterlacingInterpolation, NonnegativeSupermartingale, BoundedDifferences, Matrix/Order) should be checked against Mathlib before porting.
- The Schur-triangularisation re-derivations in `ForMathlib/Analysis/*` (OrderedSchur, SchurTriangularization, PencilTriangularization, SimultaneousTriangularization, OrderedSimultaneousSchur) and `Matrix/Spectral` (SchurTriangularization, OrderedSchur, PrimaryTriangularization) should come from one induction (DEDUP_FOLLOWUP); the manifest keeps them as separate topic files.

## Caveats

- Merge targets are mechanical: topic files are named after their largest member, so several targets want a rename at port time (for example `ComplexVolumeSamplingError` absorbs `VolumeCounting`; `RealDilation` absorbs `Eigenframes`). The rename ledger seed is the `target` column.
- Acyclicity was checked on today's import graph. F1/F2 will move a few lemmas between core files; re-run the acyclicity check on the quotient graph (keep/merge/rebuild targets) after F1 and F2 land.
- `field`/`index` are signature heuristics. Files that state ℂ results with ℝ eigenvalues may show ℝ; files in the F1 core show their *current* field and index, which F1 changes to 𝕜/Fintype.
- The drop rationale for each ℝ/ℂ twin is taken from the dedup/rclike reports; the complex and real statements were not compared lemma by lemma. Where a twin might carry a statement the generic file lacks, it was made a `merge` instead.

## Topic files (keep targets and what they absorb)


**Estimation/QuadraticForms/**

- `HutchinsonLaws` (351): DiagonalEstimator (136)

**Estimation/Quadrature/**

- `SLQPositiveLowerBound` (241): SLQLipschitz (119)
- `SLQRademacher` (349): SLQAnalyticSteps (95), SLQAnalytic (83)

**Estimation/Spectral/**

- `RandomStartLanczos` (254)
- `RandomStartPower` (269): RandomStartEndpoints (93)

**Estimation/Trace/**

- `HutchinsonTail` (316)
- `Unbiased` (451): SLQ (199)

**ForMathlib/Algebra/**

- `InterlacingWeights` (342): InterlacingInterpolation (68), SignedCoefficients (52), OffDiagonalSums (41), Polynomial (40), Intervals (33), DiagonalSums (26)

**ForMathlib/Analysis/**

- `DerivativeLimit` (192): OneSidedVariation (59), MeanValue (26), Lipschitz (26)
- `ExpBounds` (281)
- `FourierCircle` (230): FourierConvolution (104)

**ForMathlib/Analysis/InnerProductSpace/**

- `BlockCauchySchwarz` (235)
- `GramSchmidt` (262): OrthonormalEigenline (75), OrthonormalCons (49)

**ForMathlib/Analysis/**

- `LipschitzApprox` (330): CompactTestSupport (39), ImplicitFunction (39), Integral (38), IteratedDeriv (35)

**ForMathlib/Analysis/Matrix/**

- `Order` (345): QuadraticForm (80), OrthonormalSum (53), RangeIsometry (44), FinitePairNorm (38), NormSumSq (29)

**ForMathlib/Analysis/**

- `PowerBoundedEigen` (234): OrderedSchur (90), TriangularBasis (40)
- `PowerInequalities` (404): LogPowerMean (98), Gamma (82), BinomialRootComparison (56), InverseConvexity (46)
- `Real` (300): FinitePowerSums (80), GeometricRate (42), BernsteinParameter (38)
- `SchurTriangularization` (205): PencilTriangularization (102)
- `SimultaneousTriangularization` (256): OrderedSimultaneousSchur (104), InvariantCompression (45)

**ForMathlib/Combinatorics/**

- `SubsetDeletionProduct` (70)

**ForMathlib/Data/**

- `MultisetPermutation` (57): ExactRowSubset (28)

**ForMathlib/LinearAlgebra/**

- `IsolatedCharpoly` (202): CommonEigenvector (60), OrderedCommonEigenvector (44)

**ForMathlib/LinearAlgebra/Matrix/**

- `Triangular` (289): PencilLine (46), SeparatingRows (44), Mul (42), ComapDimension (29), PosSemidef (27), Adjugate (26)

**ForMathlib/Logic/**

- `Equiv` (31)

**ForMathlib/MeasureTheory/**

- `ConditionalParameterJensen` (355): MomentInterpolation (97), TailComparison (72), ConditionalJensen (49), ConditionalComparison (36)
- `IntegrableSup` (236): MatrixConditionalExpectation (59), IntegralSqrt (46), MapProd (45), IntegralUpdate (26)
- `Integral` (305): IntegralConvergence (142)
- `LocalWeakDensity` (313): WeightedWeakDensity (152)
- `MonotoneDensity` (350)
- `WeakDensity` (364): SmoothMeasureComparison (114)

**ForMathlib/Order/**

- `InterlacingDeletion` (86)

**ForMathlib/Probability/**

- `ExponentialTailMoments` (396): NonnegativeSupermartingale (103), BoundedDifferences (81), FiniteProductEvents (59), IndepExpSum (39)
- `SampleAverage` (274): UniformCollision (69), UniformProduct (63), Independence (61)
- `UniformSamplingCounts` (311): UniformSamplingJensen (97)
- `UniformSamplingCoupling` (330): UniformSamplingMarginals (160)

**Krylov/MatrixFunctions/**

- `FunctionApprox` (249)

**Krylov/Processes/**

- `Arnoldi` (411)
- `ArnoldiProcess` (340)
- `Bidiagonalization` (284)
- `Lanczos` (343)
- `LanczosRecurrence` (300)

**Krylov/Quadrature/**

- `GaussQuadrature` (451): SpectralMeasure (118), LipschitzQuadrature (44)
- `Jacobi` (378)
- `JacobiFraction` (370): ExponentialQuadrature (73), AnalyticQuadrature (69)

**Krylov/Solvers/**

- `CG` (259)
- `CGRecurrence` (372)
- `GMRES` (320)
- `GMRESArnoldi` (225)
- `Minimiser` (240)
- `PolynomialMethods` (382)
- `Preconditioned` (321)

**Krylov/Spaces/**

- `Basic` (200): Polynomial (170)
- `Block` (249)
- `Grade` (301)

**Krylov/Spectral/**

- `PowerMethod` (400)
- `QRAlgorithm` (333)
- `Ritz` (465)
- `SubspaceIteration` (498): CharacteristicPolynomial (172), MeasurableRitz (139)

**LowRank/Cholesky/**

- `ComplexCholeskyHistories` (421): PartialCholesky (193)
- `ComplexRandomPivotedCholesky` (372): TracePotential (125), TraceDrift (68)

**LowRank/Nystrom/**

- `GeneralizedNystrom` (207)
- `SketchedRegression` (314): RawNystromBridge (109)

**LowRank/PolynomialMethods/**

- `ComplexPolynomialFilterBounds` (228)
- `PolynomialFilter` (593): ComplexPolynomialFilter (276)

**LowRank/RandomizedSVD/**

- `RSVD` (306): Assembly (127)

**LowRank/RangeFinding/**

- `ComplexSubspaceAngles` (234)
- `SubspaceConvergence` (418): ComplexSubspaceConvergence (209)

**LowRank/Sampling/**

- `ComplexVolumeSamplingError` (444): VolumeCounting (148), ComplexVolumeSamplingEndpoints (102), ComplexVolumeSampling (47)
- `ComplexVolumeSamplingLaw` (176)

**LowRank/Structural/**

- `RangeFinder` (416): PowerIteration (183)

**Matrix/Basic/**

- `CauchyBinet` (235): CauchyBinetAdjoint (98)
- `GeneralizedSchurComplement` (305)
- `Gram` (241): GramVanishing (55), Selection (44), CoordinateUpdates (36), RankBounds (30)
- `JacobiMinor` (281): JacobiBlockMinor (92), SchurRank (92)
- `LeastSquares` (360)
- `MoorePenrose` (477): SingletonInverse (40)
- `MoorePenroseTransformations` (220): MoorePenroseProjector (87), MoorePenroseRank (21)
- `PSDDuality` (299): PositiveSemidefiniteSeries (59), ComplexPosSemidefTrace (50), PositiveDefiniteClosure (39), Dilation (36)
- `PenroseIdentities` (295)
- `Pseudoinverse` (335)
- `QuadForm` (262)
- `RankInequalities` (317): ComplementaryNullities (137), ComplementaryRank (31)
- `SchurComplement` (287): DeterminantDiagonalUpdate (66)

**Matrix/Calculus/**

- `DeterminantDerivative` (90)
- `GramCutoffCalculus` (193)
- `GramSoftMin` (424)
- `GramSoftMinSpectral` (417)
- `GramTrace` (157)
- `InversePowerConcavity` (291)
- `InversePowerGrowth` (482): InversePowerLaplacianLimit (121)
- `InversePowerLimit` (469)
- `UnshiftedGramSoftMin` (459)

**Matrix/Factorizations/**

- `Cholesky` (403)
- `CholeskyStep` (408): CholeskyCharacterization (85), CholeskyDefinite (64), CholeskySemidefinite (42)
- `ComplexCholeskyPivot` (403): CholeskyPivot (107)
- `Givens` (393)
- `GramSchmidt` (564)
- `Hessenberg` (222)
- `Householder` (402): GramColumnExchange (75)
- `LU` (569)
- `LULeadingRank` (247): LURowInclusion (114)
- `MaximumVolumeQR` (279): MaximumVolumeColumns (81), MaximumVolumeBudget (76)
- `NearestPolar` (221)
- `PolarDecomposition` (277): PolarIntertwining (58)
- `ProcrustesRotations` (393): ScaledOrthogonal (116), Procrustes (115)
- `QR` (467)
- `QRConsequences` (332): QRCompletion (85), QRExistence (67), QRDecomposition (63)
- `StrongRankRevealingQR` (395): RankRevealingTrailing (105), RankRevealingLeading (72), MaximumVolumeTriangularQR (58), MaximumVolumeRankAdapted (57)
- `Triangular` (410)

**Matrix/Functions/**

- `CFCQuadratic` (419): ExtremeEigenvalues (117), FunctionalCalculusEigenvalues (70), CFCTrace (63)
- `HermitianCalculus` (453): DilationIdentities (122)
- `IntrinsicDimension` (301): JensenBlockCalculus (70), PerspectiveSqrtNormalization (50)
- `InverseCalculus` (254): ExpLog (56), ExpLogPosDef (31)
- `PolynomialCalculus` (355): DiagonalFilter (73)
- `PolynomialSeries` (231): PolynomialIntertwining (60)
- `TraceExpBounds` (246)
- `TracePowerConvexity` (392)
- `UnitaryCalculus` (361)

**Matrix/Inequalities/**

- `BlockOrderConsequences` (227): BlockStrictContraction (111)
- `BlockQuadratic` (311): BlockContraction (117)
- `FiniteExponentialGram` (277): TraceInverseConvexity (93), QuadraticConditionBounds (89)
- `HadamardDeterminant` (197): HadamardExponential (74)
- `HadamardOrder` (372): HadamardDeterminantLower (98), HadamardMinimumSpectrum (68), HadamardInverse (58), HadamardDominanceCounterexample (38)
- `HadamardPowerSeries` (166): HadamardPowerOrder (59)
- `HermitianPart` (253): HermitianPartConverse (84), HermitianPartToolkit (65)
- `KyFan` (270): KyFanAttainment (129)
- `KyFanNorms` (234): KyFanSums (88)
- `Majorization` (261): MajorizationWeights (117)
- `MajorizationConvex` (405): MajorizationSupport (108), MajorizationHLP (100), MajorizationWeakSupport (71)
- `MajorizationHinges` (306): MajorizationProperties (102), MajorizationStochastic (82)
- `MinkowskiDeterminant` (301): LogDetConcavity (114), DeterminantRoot (44)
- `Mirsky` (422): HornPowerSums (118), Lidskii (94), MirskyPadded (88)
- `PlaneRotationDerivative` (373): SchurHornDescent (89), PlaneRotation (82), PlaneRotationSpectrum (59)
- `PrincipalMinorProductBounds` (362): PrincipalMinorProducts (98), InverseDiagonalMinor (87), SzaszDeterminant (63)
- `PrincipalOverlapDeterminant` (437): FischerDeterminant (104), CompressionDeterminant (76), OverlappingBlockDeterminant (73), ColumnDeterminantBound (57)
- `RelativeSpectrum` (430): StrictRelativeSpectrum (82), PositiveSpectralEndpoints (55)
- `SchurHorn` (375): SchurHornWeights (104), SchurHornResidual (97)
- `SchurHornProjection` (311): Schur (69)
- `TraceTail` (308): Kantorovich (74), TraceExpMonotone (48)
- `TraceYoung` (444): TracePowers (148), TraceMeanValue (121)
- `VonNeumann` (280)
- `Wielandt` (164): SeparatingPSDVector (68)

**Matrix/Norms/**

- `BlockNormBounds` (193): RayleighNorm (59), EuclideanOperatorBounds (55)
- `Core` (495): EntryBounds (40), ColumnNorms (15)
- `Frobenius` (491)
- `InvariantNormRepresentation` (223): FanDominance (87)
- `Net` (371)
- `NuclearNorm` (370): NuclearHermitian (92), NuclearGram (60), NuclearPSD (33)
- `RankNorm` (215): KyFanNorm (41)
- `RectangularDiagonal` (212): RectangularDiagonalPermutation (100)
- `SchattenComparison` (224): SchattenSingularCoefficients (82)
- `SchattenDuality` (338)
- `SchattenEndpoints` (235): SchattenInvariant (97)
- `SchattenNorms` (401): Schatten (126), SchattenProducts (72), SchattenTrace (72)
- `SpectralNormBounds` (241): Reindex (76)
- `SymmetricGauge` (212): InvariantNorm (105)

**Matrix/OperatorTheory/**

- `Basic` (199): CoordinatePinching (115), LogOperatorConcave (37)
- `GoldenThompson` (201)
- `JointTensorRepresentation` (438): GeneralizedKlein (77), EntropyNonnegative (59), JointTensor (38)
- `LoewnerHeinz` (313): JensenIsometricCompression (145), OperatorJensen (47)
- `PerspectiveConvex` (337): LiebConcavity (89), EntropyJointConvex (82), LiebTraceFunction (41)
- `TraceExpConvex` (136): VariationalTraceExp (47), VariationalTrace (33)

**Matrix/Perturbation/**

- `BauerFike` (299): BauerFikeAbsolute (137)
- `ConditionNumber` (331): DistanceToSingularity (128), InversePerturbationBounds (60)
- `Conditioning` (327)
- `DavisKahanPopulation` (220): DavisKahanBounds (100)
- `DavisKahanTop` (275): DavisKahan (136)
- `EigenspaceProjector` (389): DavisKahanFrames (211)
- `EigenvalueTrace` (268): EigenvaluePerturbation (113)
- `EigenvalueVariation` (260): GoldenRatioBlock (91)
- `HoffmanWielandtNormal` (306): EigenvaluePencil (73), SpectralContinuity (58), RayleighDerivative (43)
- `InversePerturbation` (336)
- `LeastSquaresGeometry` (292): LeastSquaresAngle (87)
- `LeastSquaresPerturbation` (216)
- `LeastSquaresPurePerturbation` (307): LeastSquaresCoordinateBounds (109)
- `LeastSquaresScalar` (330): LeastSquaresToolkit (181), LeastSquaresEuclidean (60)
- `MapConditioning` (377): OptimalErrorContinuity (106)
- `PopulationTraceGap` (320): SpectralFrameWeights (137), SpectralWeightGap (87)
- `PseudoinverseFrobeniusPerturbation` (283): PseudoinverseNormControl (62), PseudoinversePerturbation (55)
- `PseudoinverseSpectralPerturbation` (450): PseudoinverseBlocks (103), PseudoinverseProjectors (99), PseudoinverseDifference (89)
- `ResidualBounds` (225)
- `SimpleEigenvaluePersistence` (209): SimpleEigenvalueReal (103)
- `SimpleEigenvaluePerturbation` (440): SimpleEigenvalueSchurFunction (96), SimpleEigenvalueSchurSpectrum (78), SimpleEigenvalueImplicitBranch (67), SimpleEigenvalueContinuousBranch (59)
- `Sylvester` (235)
- `Wedin` (310): WedinBounds (81), GramSingularBounds (74)
- `WedinResidual` (497): SingularFrames (143), WedinCoupled (105), SingularFrameTails (56), CoupledNormBounds (49)

**Matrix/Spectral/**

- `Core` (695)
- `CourantFischer` (390)
- `DefiniteCongruence` (281): DefinitePairCalculus (85)
- `DiagonalDominanceStability` (212): DiagonalDominanceCorollaries (79)
- `Diagonalizable` (406): SimultaneousDiagonalization (119), SimultaneousOrthogonal (75)
- `DiagonalizableBlocks` (387): OrderedSimultaneousTriangularization (91), SimultaneousTriangularBasis (88), DiagonalizablePrincipal (86)
- `EckartYoung` (391)
- `EigenframeDecomposition` (136)
- `EigenvalueOrder` (153)
- `EigenvectorDeflation` (288): EigenvectorDeflationBlocks (110), EigenvectorDeflationSpectrum (71)
- `EigenvectorPairing` (446): AdjugateRankOne (123), RankOneEigenvalue (115), EigenvectorDeflationConverse (75)
- `GershgorinBounds` (402): IrreducibleDiagonalDominance (105), GershgorinCounting (95), GershgorinBasic (93)
- `HaynsworthInertia` (248)
- `Inertia` (331): IndefiniteCongruence (104)
- `InterlacingDeterminants` (405): InterlacingStrictConstruction (101), InterlacingConverse (81), InterlacingTrace (68)
- `InterlacingInduction` (174): InterlacingRestoration (82)
- `InterlacingSymmetricConverse` (270): InterlacingOrthogonalTransport (104), InterlacingReindex (43)
- `LowRankInterlacing` (375): SingularInterlacing (152), SingularInterlacingToolkit (38)
- `MatrixPowerBounds` (339): MatrixPowerReal (105), MatrixPowerConvergence (99)
- `NormalSimilarity` (264): NormalToolkit (110), NormalBlocks (48)
- `NormalSpectral` (204): NormalIntertwining (40), NormalRectangularIntertwining (35)
- `OstrowskiCongruence` (232)
- `PowerRayleigh` (302): PowerBoundedOrbits (100), MatrixPowerBounded (93)
- `PrimaryTriangularization` (361): SchurTriangularization (96), SeparableCharpolyDensity (86), SchurDensity (58)
- `ProductSingularValues` (228): ProductWeyl (58)
- `QuadraticProbe` (254): GeneralizedEigenPairing (90), GeneralizedEigenDecay (65)
- `RealDilation` (442): RealDilationSpectrum (109), Eigenframes (95), OrderedSymmetricDiagonalization (53)
- `RealNormalForm` (333): RealNormalSpecializations (115), RealNormalBlocks (102)
- `RealQZ` (271): RealPencilTriangularization (99), QuasiPencilBasis (87)
- `RealSchur` (310): RealInvariantPlane (104), RealInvariantSubspace (95)
- `RealSchurCanonical` (389): RealSchurPlane (117), RealSchurSimilarity (61), RealPlaneSchur (60)
- `RealSimilarityDescent` (291): RealOrthogonalDescent (84), ComplexQZ (82)
- `SVD` (660)
- `SchurFrobenius` (409): QuasiTriangular (105), CharpolySimplicity (92), EigenvalueSimplicity (89)
- `SemidefiniteCongruence` (292)
- `SimultaneousNormal` (288): SimultaneousTriangularization (91), CommutingSpectra (64)
- `SingularValueSpectrum` (118): GramSingularValues (45)
- `SmallTriangularSimilarity` (287): RealSpectrumSchur (91), OrderedSchur (66)
- `SpectralBounds` (261)
- `SpectralMinimum` (191): EigenvalueEquality (67)
- `SpectrumCountContinuity` (344): TraceEigenvalues (81), SpectrumCount (69), TracePowerBounds (64)
- `SvdBlocks` (393): SingularValueInvariance (74), SvdPowers (70), SingularValueScaling (69), SquareSingularBasis (51)
- `SylvesterCriterion` (528): ComplexVolumeSpectrum (167), PrincipalMinorPSD (114), PrincipalMinors (69)
- `SylvesterQualitative` (341): SylvesterBlocks (125), SylvesterSimilarity (67)
- `Weyl` (212)

**Matrix/Structured/**

- `GramSoftMinMeasurable` (129)
- `KroneckerSpectrum` (404): KroneckerNormRank (112), KroneckerSingularValues (107), KroneckerIdentities (66)
- `StructuredMatrices` (294): CirculantCharacterization (133)
- `Walsh` (342): Hessenberg (97), WalshFin (49)

**Matrix/Subspaces/**

- `CSDecomposition` (547): ComplexCSDecomposition (150), CanonicalCS (107), UnitaryBlockCompletion (73), OrthogonalBlockCompletion (72)
- `CSRank` (214): ComplexCSRank (89), OrthogonalSumCompletion (36)
- `GramIsometry` (432): OrthogonalProducts (129), ComplexGramIsometry (71), RectangularGramIsometry (50), OrthogonalBasisChange (49)
- `ObliqueProjectionNorms` (384): ComplexObliqueSecant (103), ObliqueProjectionSecant (95), ComplexObliqueSpectrum (83)
- `ObliqueProjectionSpectrum` (563): ObliqueCanonicalSpectrum (91), ComplexObliqueBlocks (88), ObliqueFrameInverse (74), ObliqueProjectionBlocks (72), ComplexObliqueCanonical (57), ObliqueProjectionCanonical (55), ObliqueComplementSpectrum (52)
- `OrthonormalBasisMatrix` (547): ComplexGramColumnDeterminant (128), FrameFourthContractions (100), PolarFrame (93), GramColumnDeterminant (81), FrameContractions (69)
- `PrincipalAngleDefinitions` (320): PrincipalAngleInvariance (90)
- `PrincipalAngleTangent` (351): GraphTangent (166), PrincipalAngleMaximum (63)
- `PrincipalAngles` (461): PrincipalAngleBridges (140)
- `ProjectionGaps` (612): ComplexProjectionBounds (160), ComplexProjectionComposition (100), ProjectionFrobeniusGaps (65)
- `Projections` (692)
- `ProjectorBlocks` (173): InverseOverlapGram (84)
- `ProjectorTrace` (65)

**Polynomial/BestApproximation/**

- `JacksonPolynomial` (248): Jackson (79)
- `Minimax` (270)
- `SawtoothDerivative` (251): SawtoothInterpolation (91), SineBasis (63)
- `SawtoothNorm` (289): JacksonPeriodic (100)
- `SawtoothZeros` (243)
- `SquareWave` (399): SawtoothSign (138), SawtoothSquareWave (104)

**Polynomial/Chebyshev/**

- `Core` (276): ChebyshevAliasing (94), CosineBasis (42)
- `LanczosFilterMean` (465): Growth (154), EvenChebyshevFilter (128)
- `Markov` (461)

**Polynomial/FunctionApproximation/**

- `AnalyticApproximation` (226)
- `AnalyticCoefficients` (332): BernsteinEllipse (169)
- `AnalyticFourier` (347): Approximation (137)
- `Exponential` (282)
- `Monomial` (276)

**Polynomial/Interpolation/**

- `Lagrange` (457): AnalyticInterpolation (174)

**Probability/ChiSquare/**

- `ChiSquare` (771)
- `DirectionalSquaredNorm` (214)

**Probability/Concentration/Basic/**

- `Net` (392): TailIntegral (117), MatrixCalculus (86), ChernoffFunctions (35), ScalarLaws (28)

**Probability/Concentration/Entropy/**

- `EntropyTensorization` (409)
- `EntropyTensorizationNonneg` (380): Herbst (119)

**Probability/Concentration/Martingales/**

- `ConditionalCgf` (315): TracePotentialStep (104), ConditionalLiebPredictable (83)
- `Freedman` (247): LocalSecondMomentIntegral (84), ConditionalLieb (46)
- `TracePotentialProcess` (286): FreedmanGlobal (97), TracePotential (65)
- `VarianceBudget` (342): LocalSecondMoment (80), LocalSecondMomentBounded (72), LocalSecondMomentIndicator (65)

**Probability/Concentration/Matrix/**

- `ChernoffMgfCgf` (357): BernsteinMgfCgf (98), LiebIntegralPosDef (71)
- `HermitianBernstein` (429): IndependentSumSecondMoment (77), VarianceAdditivity (53)
- `HermitianSeries` (444): RademacherMgfCgf (84), GaussianMgfCgf (52)
- `IntrinsicBernstein` (220)
- `IntrinsicBernsteinExpectation` (253)
- `IntrinsicChernoff` (423)
- `IntrinsicHermitianBernstein` (382): GeneralizedLaplace (73)
- `MasterBounds` (345): ExpectExtremaIntegrable (91), LaplaceTails (88), LaplaceExpectations (74)
- `MatrixChernoff` (338)
- `MatrixSeries` (418): MatrixBernstein (180), DilationVariance (54)
- `RademacherKhintchine` (324): RademacherPolynomialMoments (76), PolynomialMoment (52), TraceIntegrability (40)
- `Sampling` (237): UniformIidSampling (66)
- `SamplingWithoutReplacementTails` (303): SamplingWithoutReplacement (110)
- `TraceCgfSubadditivity` (347): CgfIndependentReplacement (78), MasterSumExponentialIntegrable (59), LiebRegularityShiftIntegrable (56), ProbabilisticLieb (47)

**Probability/Concentration/QuadraticForms/**

- `Centering` (335)
- `CutAverages` (329)
- `Decoupling` (392)
- `DiagonalCGF` (308): RademacherQuadraticMoments (138)
- `GaussianProductIntegrability` (455)
- `Geometry` (412)
- `HansonWright` (276): SquaredProjections (56)
- `LinearFormComparison` (320)
- `QuadraticMoments` (391)
- `TailAssembly` (345): UniversalBound (70)
- `VectorProductComparison` (403)

**Probability/Concentration/Scalar/**

- `McDiarmid` (313)
- `ScalarBernstein` (265)

**Probability/Gaussian/Basic/**

- `StandardVector` (196): CovarianceRepresentation (82)

**Probability/Gaussian/Calculus/**

- `IntegrationByParts` (483): OrnsteinUhlenbeck (135)
- `OrnsteinUhlenbeckEntropy` (542)
- `OrnsteinUhlenbeckEntropyGrowth` (280)
- `OrnsteinUhlenbeckGrowth` (408)
- `ProductIntegrationByParts` (356): PolynomialGrowthIntegrationByParts (105), Stein (101)

**Probability/Gaussian/Comparison/**

- `GordonMinimax` (691)
- `Interpolation` (291)
- `Slepian` (493): SlepianTails (41)
- `SudakovFernique` (372)

**Probability/Gaussian/Concentration/**

- `LogSobolev` (219)
- `LogSobolevCoverage` (272)
- `LogSobolevHerbst` (644): LipschitzConcentration (58)
- `LogSobolevOneDim` (512)

**Probability/Gaussian/Moments/**

- `ExpectationNormDiff` (338)
- `PolynomialLinearMoments` (255): SeriesPolynomialMoments (105)
- `PositiveMoments` (236)
- `SeriesSecondMoment` (296): Khintchine (103), SeriesKhintchine (86)
- `WickPairings` (322): Isserlis (147)

**Probability/Rademacher/**

- `RademacherSymmetry` (230): RademacherCube (77)

**Probability/Sampling/**

- `FiniteSampling` (53)

**Probability/SubGaussian/**

- `CenteredSquare` (523)
- `EvenMoments` (516)
- `ExpSquare` (416)
- `Moments` (311)
- `OrliczMGF` (220)

**RandomMatrix/Gaussian/Basic/**

- `Lipschitz` (391): LinearForms (131), LipschitzConcentration (58), PolynomialGrowth (53)

**RandomMatrix/Gaussian/InverseMoments/**

- `CutoffIntegrability` (309): RegularizedIntegrability (96), CutoffDerivativeIntegrability (93)
- `DiagonalLaw` (273)
- `FrobeniusMoments` (289)
- `GaussianWeakInequality` (386): ResolventLimit (83)
- `HardEdgeEndpoint` (462): OperatorHardEdge (47)
- `LambdaMinTail` (437)
- `SchurComplement` (269)
- `SpectralProbe` (357): GammaBounds (197)
- `SpectralTail` (360)
- `UnshiftedWeakInequality` (422)
- `WeakInequality` (316): RegularizedApproximation (87)

**RandomMatrix/Gaussian/Moments/**

- `ApproxMultiplication` (361): LogOverlapMoments (175)
- `FourthMoment` (388)
- `SecondMoment` (314)

**RandomMatrix/Gaussian/Spectral/**

- `Deviation` (192): Chevet (64)
- `Gordon` (618)
- `SmallBall` (317)
- `SpectralSecondMoment` (679)

**RandomMatrix/Gaussian/Wishart/**

- `SimpleSpectrum` (197)

**RandomMatrix/Haar/**

- `HaarFrameMeasure` (121)

**RandomMatrix/SubGaussian/**

- `SubGaussianJL` (229)
- `SubGaussianRows` (247)

**Sketching/Properties/ApproxMatrixMultiplication/**

- `ApproxMultiplication` (268)

**Sketching/Properties/JL/**

- `JL` (318)

**Sketching/Properties/SubspaceEmbedding/**

- `Basic` (275): SubspaceEmbedding (111), SingularValueEmbedding (79), Gram (53)

**Sketching/Sampling/**

- `LeverageSampling` (363): Leverage (87)
- `SamplingMultiplication` (465): SamplingMultiplicationBounds (97)

**Sketching/Structured/**

- `SRHT` (292)
- `SRHTFlattening` (397): SRHTCore (147), SRHTParameters (67)
- `SRHTWithReplacement` (223)
