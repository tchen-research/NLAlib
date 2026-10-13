# F4 wave 1: agent P report (`Probability/**`, `ForMathlib/{Probability,MeasureTheory,Analysis/Matrix}`)

Status: HANDED OFF UNFINISHED on 2026-10-13 (see "State at handoff" at the end). Renames are in `docs/renames/2026-10-F4-P.json`
(kept current while the round runs, so A1 and wave 2 can read them early).

## Law interface (P3/P4), done first

- `IsStandardGaussian μ g` / `IsRademacher μ r` deleted: statements say
  `HasLaw g (gaussianReal 0 1) μ` / `HasLaw r rademacherMeasure μ`.
- `gaussianVector n : Measure (n → ℝ) := Measure.pi fun _ => gaussianReal 0 1` (abbrev,
  `Probability/Gaussian/Basic/StandardGaussian.lean`) with `hasLaw_eval_gaussianVector`,
  `iIndepFun_eval_gaussianVector`, `hasLaw_gaussianVector_of_iIndepFun`,
  `HasLaw.hasLaw_eval_gaussianReal`, `HasLaw.iIndepFun_eval_of_gaussianVector`.
- `rademacherVector n := Measure.pi fun _ => rademacherMeasure` (abbrev,
  `Probability/Rademacher/Core.lean`) with the same five lemmas (`…_rademacherVector`,
  `HasLaw.hasLaw_eval_rademacherMeasure`, `HasLaw.iIndepFun_eval_of_rademacherVector`).
- `Probability/Rademacher/RademacherCube.lean` (`rademacherCubePMF`, `rademacherBoolSign`) deleted.
  **Wave-2 (A2, Sketching/Structured/SRHT*)**: the sign diagonal is a `rademacherVector n` sample
  (ℝ-valued), brief A8.
- Moment bundles split (see the rename table).
- `ProbabilityTheory.hasLaw_iff_map_eq (hν : ν ≠ 0)` in `ForMathlib/Probability/HasLaw.lean`.

## Requests to other owners

(filled in as they arise)

## State at handoff

Written 2026-10-13 by the third P agent (takeover), on the coordinator's instruction to stop. This
agent established the state, brought the rename table up to date and wrote this section; it edited
**no Lean file**, spawned no sub-agent and has no build running. Everything below describes the
uncommitted tree left by the two earlier P agents (base `75cf87d`).

### Last build

`flock /tmp/p-lake.lock lake build NLAlib.ForMathlib NLAlib.Probability` (log `/tmp/p2_build1.log`),
finished 2026-10-13 ~19:15: **failed**, 5 of my modules plus one upstream artefact. Everything else
in `NLAlib.ForMathlib` and `NLAlib.Probability` built. Not rerun since.

| module | first error |
|---|---|
| `Probability/Concentration/Matrix/SubgaussianMgfCgf.lean` | `:56:6` `cfc_mono`: "could not synthesize default value for parameter 'hf'"; goal `ContinuousOn (fun x => mgf g μ (θ * x)) (spectrum ℝ A)`. `hcont` is declared *after* the `rw`/`refine` that needs it (line 62); pass `hcont.continuousOn` explicitly as in the theorem above it (line 47). |
| `Probability/Concentration/QuadraticForms/HansonWright.lean` | `:65:24` `frobNorm_eq_zero_iff.1 h.symm`: M1 made `A` explicit, write `(frobNorm_eq_zero_iff A).1 h.symm`; then `:67` `simp at hOp` needs `specNorm_zero`. |
| `Probability/Gaussian/Moments/SeriesKhintchine.lean` | `:35:18` `Unknown identifier IsStandardGaussian` (also `:74`); the disjunctive hypothesis was never converted here (P4). |
| `Probability/Concentration/Matrix/IntrinsicHermitianBernstein.lean` | `:114:2` `simp only [specNorm_eq_norm] at *` makes no progress (leftover of the N1 sweep; delete the line or restrict it to the hypotheses that still mention `specNorm`). |
| `Probability/Concentration/Matrix/MatrixChernoff.lean` | `:245:21` `Unknown identifier master_bounds` (also `:257`, `:282`, `:318`): `MasterBounds.lean` was split into four theorems (rename table), the four call sites still project `.1`/`.2` out of the bundle. |
| `Matrix/Functions/DilationIdentities` (M2's) | "no such file or directory": a concurrent M2 build, not a source error. |

Downstream of the failures and therefore **not compiled** by that build (their on-disk text is the
predecessors' restated form and has never been compiled in this state; expect further errors):
`Gaussian/Moments/SeriesSecondMoment.lean` (imports `SeriesKhintchine`; it has the same
undefined `IsStandardGaussian … ∨ IsRademacher …` hypothesis at `:85`, so it will fail),
`Matrix/Sampling` (imports `MatrixChernoff`), `Matrix/{IntrinsicBernstein,IntrinsicBernsteinExpectation,MatrixBernstein}`
(import `IntrinsicHermitianBernstein`), `Matrix/{GaussianMgfCgf,RademacherMgfCgf,HermitianSeries,MatrixSeries}`
(import `SubgaussianMgfCgf`), and the aggregators above them. Compiled and fine in that build, among
the restated files: `MasterBounds`, `HermitianBernstein`, `IntrinsicChernoff`, `LaplaceTails`,
`LaplaceExpectations`, `ChernoffMgfCgf`, all of `Martingales/`, `ChiSquare/`, `Scalar/`,
`Gaussian/{Basic,Calculus,Comparison,Concentration}`, `Rademacher/`, `SubGaussian/`, and all of
`NLAlib.ForMathlib`.

No file is mid-edit in the sense of being syntactically broken: the five failures above are the
complete list of known errors.

### Items

- **P1 (𝕜-generic Tropp vocabulary and headlines): not started.** Every file of
  `Concentration/Matrix/**`, `Concentration/Martingales/**`, `Concentration/Basic/{MatrixStatistics,MatrixCalculus}`
  and `Gaussian/Moments/{Khintchine,Series*}` is still on `Matrix (Fin d) (Fin d) ℂ` with `[NeZero d]`
  (76 `NeZero` occurrences in 24 files; `rectSecondMoment`, `hermitianSecondMoment`, `cumulantSum` at
  `Basic/MatrixStatistics.lean:26,35,43` take `ℂ`). No real corollary exists for any headline.
  Finding for whoever continues: a direct generalisation is blocked upstream, because the
  deterministic inputs are ℂ-only in M2's files (`Matrix/Functions/{IntrinsicDimension,TraceExpBounds,DilationIdentities}`,
  `Matrix/OperatorTheory/{GoldenThompson,LiebConcavity,VariationalTraceExp,TraceExpConvex,…}`, most
  with `[NeZero d]`); `matrixExp`/`matrixLog`/`traceExp`/`lambdaMax`/`lambdaMin` themselves are
  already over `[RCLike 𝕜] [Fintype d]`. The plan that was about to start (nothing written): one
  transfer file with the entrywise embedding `𝕜 → ℂ` (`x ↦ ⟨re x, im x⟩`, an injective `ℝ`-star-algebra
  map for every `RCLike 𝕜`; Mathlib has only `RCLike.complexRingEquiv`/`realRingEquiv` under a
  case hypothesis) composed with `Matrix.reindex (Fintype.equivFin n)`, and lemmas that it preserves
  `lambdaMax`/`lambdaMin` (via `det`), `specNorm` (C*-identity + `lambdaMax` of the Gram),
  `IsHermitian`, `PosSemidef`, `≤`, `re ∘ trace`, `matrixExp`, `cfc`, measurability, `iIndepFun`
  (`.comp`) and Bochner integrals (`ContinuousLinearMap.integral_comp_comm'`, the map is isometric);
  then each headline is stated over `[RCLike 𝕜] [Fintype n] [Nonempty n]` (dimension factor
  `Fintype.card n`) and proved by applying the existing ℂ/`Fin` theorem to the embedded family.
  M1's `realMatrixComplexification` (`Matrix/Spectral/Complexification.lean`) is ℝ → 𝕜 only and has
  no `lambdaMax`/`specNorm`/integral lemmas. `intrinsicDimension` is M2's and ℂ-only.
- **P2 (tails as `μ.real s ≤ c`): done in `Probability/**` statements, partial in ForMathlib.**
  Converted: ChiSquare, DirectionalSquaredNorm, Net, SquaredProjections, SubGaussian/Moments, the whole
  Tropp chain, HansonWright, McDiarmid, LipschitzConcentration, LogSobolev (rename table). Missing:
  `ForMathlib/Probability/NonnegativeSupermartingale.lean:45,78` (`(μ {…}).toReal ≤ …` in two
  statements); tail *hypotheses* still in `ENNReal.ofReal` form at `Concentration/Basic/TailIntegral.lean:39,63,86`
  and `ForMathlib/Probability/ExponentialTailMoments.lean:59,115`; `Scalar/ScalarBernstein.lean:175,178`
  are inside a proof. The `LogSobolevHerbst`/`LogSobolevCoverage` `ENNReal.ofReal` hits are
  `lintegral` bounds, not tails.
- **P3 (laws): mostly done.** `gaussianVector`, `rademacherVector`, the `HasLaw` lemmas, deletion of
  `IsStandardGaussian`/`IsRademacher`/`rademacherCubePMF` are in place (top of this report). Missing:
  (a) the 4 uses in `Gaussian/Moments/SeriesKhintchine.lean:35,74` and `SeriesSecondMoment.lean:85`;
  (b) raw `Measure.pi fun _ => gaussianReal 0 1` in `Concentration/QuadraticForms/GaussianProductIntegrability.lean:185,191,226,229,278,284`,
  `Gaussian/Concentration/LogSobolev.lean:120`, `Gaussian/Moments/PositiveMoments.lean:26`;
  (c) **no bridge** `gaussianVector n` ↔ `stdGaussian (EuclideanSpace ℝ n)` and none to
  `gaussianMatrix` (the latter needs a `RandomMatrix` import: wave-2 request to R); the HighDimProb
  files (`QuadraticForms/{Geometry,LinearFormComparison,VectorProductComparison,GaussianProductIntegrability}`,
  `Gaussian/Basic/{StandardVector,CovarianceRepresentation}`) still use `stdGaussian` directly;
  (d) entrywise law + `iIndepFun` on a family is not yet `HasLaw` on the vector:
  `Matrix/MatrixSeries.lean:153-184`, `Matrix/HermitianSeries.lean:282-313`,
  `SubGaussian/Moments.lean:119,138`; (e) redundant `(hMeas : ∀ k, Measurable (g k))` next to a
  law/sub-Gaussian hypothesis: `HermitianSeries.lean:50,78,142,203,235,282-312`,
  `MatrixSeries.lean:26,67,127,142,153-183`, `SeriesKhintchine.lean:33,72`, `SeriesSecondMoment.lean:83`.
- **P4 (disjunctive hypothesis): partial.** Done in text (uncompiled, see above) for
  `Matrix/HermitianSeries.lean` and `Matrix/MatrixSeries.lean`: primary theorems take
  `∀ k, HasSubgaussianMGF (g k) 1 μ` and unit variance, with `_of_hasLaw_gaussianReal` /
  `_of_hasLaw_rademacherMeasure` corollaries; `Matrix/SubgaussianMgfCgf.lean` is new (one error,
  above). Not done: `Gaussian/Moments/SeriesKhintchine.lean:35,74`, `SeriesSecondMoment.lean:85`.
  Caution for these three: `SeriesSecondMoment` (`𝔼 re tr (∑ ξᵢAᵢ)² = re tr ∑ Aᵢ²`) needs only
  independence, mean zero and unit variance, but the `2p`-th moment Khintchine bound with constant
  `(2p-1)^p` is **not** a consequence of `HasSubgaussianMGF … 1` and unit variance (its proof is
  Gaussian integration by parts / sign flips); there the disjunction should become two
  `_of_hasLaw` corollaries (`HasLaw ξ (gaussianVector (Fin n)) μ`, `HasLaw ξ (rademacherVector (Fin n)) μ`)
  of the concrete `integral_re_trace_gaussianSeries_pow_le` / `…_rademacherSeries_pow_le`.
- **P5 (bundles, `∃ C`, duplicates): partial.** Done: the Tropp headline bundles are split and
  tagged (`master_bounds`, `matrix_chernoff`, `hermitian_bernstein`, `matrix_bernstein`, the
  intrinsic four, the two series, Laplace tails/expectations, the Gaussian/Rademacher mgf/cgf
  pairs); `∃ C` → `20` (`integral_specNorm_sum_le_of_intrinsicDimension`,
  `IntrinsicBernsteinExpectation.lean:262`); `UniversalBound.lean` deleted; `_fin` twins deleted in
  `ChiSquare.lean` and `McDiarmid.lean`. Missing: (a) duplicate noncommutative Khintchine still
  there (`Matrix/RademacherKhintchine.lean:144` tagged `(partial)`, `Gaussian/Moments/Khintchine.lean`,
  `SeriesKhintchine.lean:31,69`); (b) tagged bundles not split: `ChiSquare/ChiSquare.lean:456,595,618,727`,
  `Concentration/Basic/TailIntegral.lean:59,83`, `Martingales/ConditionalCgf.lean:51`,
  `QuadraticForms/QuadraticMoments.lean:97`, `SubGaussian/OrliczMGF.lean:176`,
  `Matrix/Sampling.lean:93,126,158` (check: conjunctions in the conclusion); (c) untagged public
  bundles: `Basic/MatrixCalculus.lean:81`, `Matrix/BernsteinMgfCgf.lean:28`, `Matrix/ChernoffMgfCgf.lean:142`,
  `Matrix/ExpectExtremaIntegrable.lean:74`, `Matrix/LiebRegularityShiftIntegrable.lean:28`,
  `Martingales/{LocalSecondMomentBounded.lean:26,LocalSecondMomentIndicator.lean:56,VarianceBudget.lean:76}`,
  `Scalar/ScalarBernstein.lean:27`; (d) private `…_package` lemmas with `let`–`∧` remain as proof
  devices (`MatrixBernstein.lean:71`, `IntrinsicHermitianBernstein.lean:~100`, `HermitianSeries.lean:183`).
- **P6 (PSD hypotheses, total `intrinsicDimension`): not started.** `0 ≤ lambdaMin … ∧ lambdaMax … ≤ L`
  in statements at `Matrix/ChernoffMgfCgf.lean:43,57,66,74,88,146`, `Matrix/MatrixChernoff.lean:36,125,352`,
  `Matrix/Sampling.lean:43,97,130,162`; `M ≠ 0`/`V ≠ 0` hypotheses at
  `Matrix/IntrinsicChernoff.lean:154,438,453`, `IntrinsicHermitianBernstein.lean:100,328`,
  `IntrinsicBernstein.lean:84,236`, `IntrinsicBernsteinExpectation.lean:164,265` (these are needed
  while `intrinsicDimension 0 = 0`; the definition is M2's).
- **P7 (moves): done except one file.** `git mv`, imports of the moved files resolve, aggregators
  list them:
  `ForMathlib/Probability/{UniformCollision,UniformProduct,UniformSamplingCounts,UniformSamplingCoupling,UniformSamplingJensen,UniformSamplingMarginals}.lean`
  and `Probability/Concentration/Matrix/{SamplingWithoutReplacement,SamplingWithoutReplacementTails,UniformIidSampling}.lean`
  → `NLAlib/Sketching/Sampling/`;
  `ForMathlib/MeasureTheory/{LocalWeakDensity,WeakDensity,WeightedWeakDensity,MonotoneDensity,SmoothMeasureComparison}.lean`
  → `NLAlib/RandomMatrix/Gaussian/Wishart/`. None of the 14 moved files has been compiled at its new
  location by a P build (they are outside `NLAlib.ForMathlib NLAlib.Probability`). **Not moved:**
  `ForMathlib/Data/ExactRowSubset.lean` (still there, edited; imported by
  `Sketching/Sampling/UniformSamplingCoupling.lean` and `ForMathlib/Data.lean`).
  `orthogonalGroupCompactSpace` → `ForMathlib/Topology/` not done (it is in `Matrix/Subspaces/Stiefel.lean`, M2's).
- **I6 (ForMathlib namespaces and tags): done in my three directories, open elsewhere.** No
  `namespace NLAlib` remains in `ForMathlib/{Probability,MeasureTheory,Analysis/Matrix}`
  (declarations are in `MeasureTheory`, `ProbabilityTheory`, `Matrix`, root; rename table) and no
  `atlas:` tag. Open: `ForMathlib/Analysis/NormSumSq.lean` still exists (imported by
  `ForMathlib/Analysis.lean`, `Matrix/Basic/CauchyBinet.lean`, `Sketching/Sparse/Bands/Directional/MarkedReindexing.lean`;
  not in P's directories); one tag left at `ForMathlib/Analysis/SpecialFunctions/Gamma.lean:60`
  (`tail-integral (partial)`, not P's directory); the note for the coordinator on `mathlib_prereqs`
  (`MomentInterpolation`) is not written — the tag was removed from the file, the atlas side is
  untouched.
- **N1/N2: partial.** No file-level `open scoped Matrix.Norms.*` in `Probability/**`
  (`open scoped … in` per declaration). `python3 scripts/check_norms.py NLAlib/Probability`: **10
  hits**, all `‖·‖` on a matrix in a signature: `Martingales/LocalSecondMoment.lean:42`,
  `Matrix/ChernoffMgfCgf.lean:65`, `HermitianSeries.lean:29`, `IntrinsicBernsteinExpectation.lean:36`,
  `IntrinsicChernoff.lean:39,107`, `MatrixBernstein.lean:60,66`, `MatrixChernoff.lean:35,69`
  (mostly private helpers). `MemLp (X k) 2 μ` hypotheses in the Tropp statements depend on the
  scoped norm without showing it (not flagged by the lint). N2 not audited.
- **I7 (docstrings, binder names): partial.** `python3 scripts/check_docstrings.py NLAlib/Probability NLAlib/ForMathlib`:
  **202 hits**; 0 in `ForMathlib/{Probability,MeasureTheory,Analysis/Matrix}`; about 125 in
  `Probability/**`, concentrated in `Concentration/Martingales/*` (all 13 files),
  `Gaussian/Moments/{Khintchine,Series*}`, `Concentration/Matrix/{RademacherKhintchine,RademacherPolynomialMoments,PolynomialMoment,Sampling,TraceIntegrability}`,
  `Concentration/Entropy/*`, and one each in ~15 Tropp files ("Ported from the Prove2me mission");
  the rest are in `ForMathlib/Analysis/*`, `ForMathlib/Algebra/*`, `ForMathlib/Data/ExactRowSubset.lean`
  (not P's directories, except ExactRowSubset which P was to move). HighDimProb binder names:
  `h_indep`/`hX_subG` remain only in `SubGaussian/EvenMoments.lean` (2 occurrences). The
  `theorem NLAlib.foo` after `end NLAlib` pattern is still in the Tropp files.

Scaffolds added: none.

### Requests still open

- **M2** (`Matrix/Functions`, `Matrix/OperatorTheory`): `intrinsicDimension`, `traceFunction`
  (`Functions/IntrinsicDimension.lean`), `TraceExpBounds`, `DilationIdentities`, `GoldenThompson`,
  `LiebConcavity`, `VariationalTraceExp` are ℂ/`[NeZero d]`; P1 needs them over `[RCLike 𝕜] [Fintype d]`
  or the transfer described under P1. `orthogonalGroupCompactSpace` → `ForMathlib/Topology/` (P7).
- **M1** (`Matrix/Spectral/Complexification.lean`): the natural home of the `𝕜 → ℂ` embedding and of
  `lambdaMax`/`lambdaMin`/`specNorm` invariance under `realMatrixComplexification`.
- **A1** (`Estimation/**`): apply `docs/renames/2026-10-F4-P.json` (entrywise
  `IsStandardGaussian … ∧ iIndepFun` hypotheses, `hasSubgaussianMGF_of_isStandardGaussian`,
  `memLp_two_and_moments_*`, the `…_pi_gaussianReal` → `…_gaussianVector` family, `hanson_wright_*`).
- **Wave 2, A2** (`Sketching/**`, `LowRank/**`): `Sketching/Structured/SRHTFlattening.lean:1` imports
  the deleted `Probability/Rademacher/RademacherCube` (signs are now a `rademacherVector n` sample,
  ℝ-valued); the 9 files received in `Sketching/Sampling/` need a first build and still carry their
  old docstrings; consumers of `matrix_chernoff`, `matrix_bernstein`, `master_bounds`,
  `intrinsic_*`, the χ² tails (`measure_…` → `measureReal_…`, `ENNReal.ofReal` → `μ.real`) follow the
  rename table; `ForMathlib/Data/ExactRowSubset.lean` is to be received in `Sketching/Sampling/`.
- **Wave 2, R** (`RandomMatrix/**`): the 5 weak-density files received in
  `RandomMatrix/Gaussian/Wishart/` need a first build; bridge
  `gaussianMatrix m n = (gaussianVector (m × n)).map …` / rows as `gaussianVector n` (P3) belongs
  next to `gaussianMatrix_eq_map_curry`; consumers of the renamed Gaussian lemmas
  (`gaussian_concentration_pi` split, `measure_ge_le_of_logSobolev` → `measureReal_…`, χ² tails).
- **Owner I**: atlas side of the split bundles (each component theorem carries the tag in Lean);
  `mathlib_prereqs` for `MomentInterpolation`; `noncommutative-khintchine` has `(partial)` tags on
  theorems until the duplicate is resolved.

### Rename table

`docs/renames/2026-10-F4-P.json` is current as of this handoff (144 entries): 37 entries were
added for names the predecessors had removed without recording (the Tropp bundle splits, the
`measure_…` → `measureReal_…` tails, the `_fin` twins, `hanson_wright_inequality`, the
`…_pi_rademacherMeasure` quadratic-form lemmas, `variance_quadForm_of_isSymm*`, the two deleted
modules). A name diff of every P file against `75cf87d` now finds no removed public declaration
without an entry. The `(.1)`/`(.2)` projections given for the split bundles were read off the
names and statements, not checked by compiling a consumer.
