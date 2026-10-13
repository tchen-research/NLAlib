# F4 wave 1: agent P report (`Probability/**`, `ForMathlib/{Probability,MeasureTheory,Analysis/Matrix}`)

Status: HANDED OFF UNFINISHED on 2026-10-13 (see "State at handoff" and the "Addendum after the handoff commit" that corrects it, both at the end). Renames are in `docs/renames/2026-10-F4-P.json`
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

## Addendum after the handoff commit (2026-10-13, 19:40)

Written by the first P agent, which was resumed after `6a09399`/`ab9218f` had been committed and
found the round stopped (`docs/F4_HANDOFF.md`). After reading the handoff it made **no Lean edit**
and ran no build: it merged the last stream report into the rename table and wrote this section.
Where this section and "State at handoff" disagree, this section is later.

### Uncommitted files (18), all from stream S1, compiled

Stream S1 (`Concentration/QuadraticForms/**`, `SubGaussian/**`, `Concentration/Scalar/**`,
`Concentration/Basic/Net.lean`, `ChiSquare/**`) was still running when the round was stopped and
finished at 19:32. Its last edits are the only difference between the working tree and `ab9218f`:

`ChiSquare/{ChiSquare,DirectionalSquaredNorm}.lean`,
`Concentration/QuadraticForms/{Centering,CutAverages,Decoupling,DiagonalCGF,GaussianProductIntegrability,Geometry,HansonWright,LinearFormComparison,QuadraticMoments,SquaredProjections,TailAssembly,VectorProductComparison}.lean`,
`Concentration/Scalar/{McDiarmid,ScalarBernstein}.lean`, `SubGaussian/{EvenMoments,OrliczMGF}.lean`.

Build that passed on exactly these sources (log `/tmp/s1_final_build.log`, no file is newer than
the log):

```
lake build NLAlib.Probability.SubGaussian NLAlib.Probability.Concentration.Scalar NLAlib.Probability.Concentration.Basic.Net NLAlib.Probability.ChiSquare NLAlib.Probability.Concentration.QuadraticForms
Build completed successfully (3789 jobs).
```

They are not committed (commits are the coordinator's). To drop them: `git checkout -- NLAlib/Probability`
(then `HansonWright.lean:65` fails again as in the handoff table and the rename-table entries marked
`_gaussianVector` for the χ² lemmas are ahead of the code).

### Corrections to "State at handoff"

- **Last build table:** the `HansonWright.lean:65` error is fixed (S1). Four P modules still fail;
  exact fixes below.
- **P2:** done in every S1 file (χ², Net, Hanson–Wright, McDiarmid, scalar Bernstein, sub-Gaussian
  moments). Left: the three tail *hypotheses* in `Concentration/Basic/TailIntegral.lean:39,63,86`
  (`μ {x | t < f x} ≤ ENNReal.ofReal (F t)`), and the two ForMathlib items listed in the handoff.
- **P3 (b):** no raw `Measure.pi fun _ => gaussianReal 0 1` / `… rademacherMeasure` remains in a
  statement of `Probability/**` (one `show … = P from rfl` inside a proof, `LogSobolev.lean:120`).
- **P3 (c):** the `stdGaussian` bridge exists: `gaussianVector_map_toLp_eq_stdGaussian`,
  `hasLaw_toLp_gaussianVector`, `hasLaw_dotProduct_gaussianVector (hv : ‖WithLp.toLp 2 v‖ = 1)` in
  `Gaussian/Basic/StandardVector.lean` (compiled). Only the `gaussianMatrix` bridge is missing
  (needs a `RandomMatrix` import: request to R). Four Hanson–Wright leaves keep `stdGaussian`
  because their proofs use the inner-product API.
- **P3 (d):** `SubGaussian/Moments.lean` Khintchine now takes
  `{ε : Ω → ι → ℝ} (hε : HasLaw ε (rademacherVector ι) μ)`. The two series files still take a
  family with `iIndepFun` and `Measurable`.
- **P5 (b), (c):** split in S1's files (`ChiSquare` ×4, `QuadraticMoments`, `OrliczMGF`,
  `ScalarBernstein`, the two maximal inequalities). Still bundled: `Basic/TailIntegral.lean:59,83`,
  `Basic/MatrixCalculus.lean` (`integrable_and_integral_matrixExp_smul_eq_cfc_mgf`),
  `Matrix/{BernsteinMgfCgf,ChernoffMgfCgf,ExpectExtremaIntegrable,LiebRegularityShiftIntegrable,Sampling}.lean`,
  `Martingales/{ConditionalCgf,LocalSecondMomentBounded,LocalSecondMomentIndicator,VarianceBudget}.lean`.
- **P6:** partly done in text. The four public matrix Chernoff theorems
  (`MatrixChernoff.lean:361-420`) take `hPSD : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef` and
  `lambdaMax (X k ω) ≤ L`; the `0 ≤ lambdaMin ∧ …` form survives only in the private
  `matrix_chernoff_package`, the helper lemmas of `ChernoffMgfCgf.lean` and `Sampling.lean`
  (public, not converted). `lambdaMin_nonneg_of_posSemidef` is public in `ChernoffMgfCgf.lean`.
- **I7:** `h_indep`/`hX_subG` are gone everywhere. `check_docstrings.py NLAlib/Probability`
  plus P's three ForMathlib directories: **126 hits**, all in the stream that was interrupted
  (Martingales 63, `Gaussian/Moments/{Khintchine,Series*}` 20, `Matrix/{RademacherKhintchine,RademacherPolynomialMoments,PolynomialMoment,Sampling,TraceIntegrability}` 22,
  Entropy 6, one "Ported from the Prove2me mission" line in each of 12 Tropp files and 3 Basic
  files). `check_norms.py NLAlib/Probability`: **10 hits**, 9 on `private` helper lemmas and
  `matrixVectorSqNorm_single` (`Martingales/LocalSecondMoment.lean:42`, public).
- **Rename table:** now 165 entries (12 S1 entries replaced, 21 added). In particular the χ² tails
  are `measureReal_…_gaussianVector` (not `…_gaussianReal`), and the χ² moment pairs are split.

### The four P modules that still fail, with the fix

1. `Concentration/Matrix/SubgaussianMgfCgf.lean:55-59`. The failing autoparam is `hf` of
   `cfc_comp'` inside the `rw` (not of `cfc_mono`). Move the `have hcont` of line 60 above the
   `rw` and pass it: `← cfc_comp' Real.log (fun x => mgf g μ (θ * x)) A (…) hcont.continuousOn`.
2. `Concentration/Matrix/IntrinsicHermitianBernstein.lean:114`. Delete
   `simp only [specNorm_eq_norm] at *` (`v` is a `let`, nothing to rewrite). The body below talks
   about `‖V‖`; where a goal then shows `specNorm V`, `rw [specNorm_eq_norm]` or `show` (`specNorm`
   unfolds to `‖·‖` under the scope opened before the lemma). Not compiled past this line.
3. `Concentration/Matrix/MatrixChernoff.lean:245,257,282,318`. Replace the projections of
   `master_bounds` by the four theorems of `MasterBounds.lean` (`θ` is now implicit, the sign
   hypothesis comes first, the tail theorems take no `hInt`):
   `:245` `log_traceExp_cumulantSum_div_le_integral_lambdaMin_sum μ X hθ' hMeas hHerm hInt hIndep (hExp _)`,
   `:257` `integral_lambdaMax_sum_le_log_traceExp_cumulantSum_div μ X hθ' hMeas hHerm hInt hIndep (hExp _)`,
   `:282` `measureReal_lambdaMin_sum_le_le_exp_mul_traceExp_cumulantSum μ X hθ' hMeas hHerm hIndep (hExp _)`,
   `:318` `measureReal_lambdaMax_sum_ge_le_exp_mul_traceExp_cumulantSum μ X hθ' hMeas hHerm hIndep (hExp _)`.
   `Sampling.lean` then needs the same treatment for `matrix_chernoff` (its three theorems still
   take `0 ≤ lambdaMin ∧ lambdaMax ≤ L`; restate with `PosSemidef` and call the public Chernoff
   tails), as do the three files moved to `Sketching/Sampling/`.
4. `Gaussian/Moments/SeriesKhintchine.lean:35,74` and `SeriesSecondMoment.lean:85`. Replace the
   disjunction as the handoff's P4 caution says: `SeriesSecondMoment` by independence, mean zero
   and unit variance (`integral_sum_smul_sq_eq_sum_sq` in `Matrix/HermitianSeries.lean` is that
   statement for the matrix-valued integral; take `re ∘ trace`); the two Khintchine theorems by
   `_of_hasLaw` corollaries `(hξ : HasLaw ξ (gaussianVector (Fin n)) μ)` /
   `(hξ : HasLaw ξ (rademacherVector κ) μ)` of `integral_re_trace_gaussianSeries_pow_le` /
   `integral_re_trace_rademacherSeries_pow_le` (`hξ.integral_comp` with the continuous integrand).
   The duplicate tag is then resolved by keeping `noncommutative-khintchine` on the two concrete
   theorems (drop `(partial)`) and on the two corollaries.

Never compiled, and written in one pass by this agent just before it was interrupted: the public
theorems appended to `HermitianBernstein.lean`, `MatrixBernstein.lean`,
`IntrinsicHermitianBernstein.lean`, `IntrinsicBernstein.lean`, `IntrinsicBernsteinExpectation.lean`,
`IntrinsicChernoff.lean`, `MatrixChernoff.lean` (each a projection of a private `…_package` lemma
that is the old bundle with `specNorm` in place of `‖·‖`), and all of `HermitianSeries.lean`,
`MatrixSeries.lean`, `GaussianMgfCgf.lean`, `RademacherMgfCgf.lean`. The handoff lists
`HermitianBernstein` and `IntrinsicChernoff` as compiled; the others are untested text.

### Concrete call sites broken outside P's files (from the three stream reports)

- **A1 (Estimation):** `Trace/Unbiased.lean` (3 sites,
  `integrable_and_integral_quadForm_eq_trace_of_second_moments` split);
  `QuadraticForms/HutchinsonLaws.lean` (`variance_quadForm_of_isSymm_of_fourth_moment_eq_{one,three}`
  → `…isHermitian…`); `Trace/HutchinsonTail.lean` (3 sites, `hanson_wright_mgf` concludes `μ.real`).
- **R (RandomMatrix):** `Basic/GaussianMatrix.lean:240` (`hasGaussianLaw_id_gaussianVector`);
  `Basic/LipschitzConcentration.lean` (`gaussian_concentration_pi` split);
  `InverseMoments/Probe.lean` (`(hasLaw_dotProduct_gaussianVector v hv').map_eq`,
  `…rpow_sum_sq_gaussianVector`, `…rpow_inv_sum_sq_gaussianVector`); `InverseMoments/OffDiagonal.lean`
  (dot-product lemmas split, right side `‖WithLp.toLp 2 w‖ ^ 2`); `InverseMoments/{Mean,FrobeniusMoments,DiagonalLaw}.lean`
  (χ² inverse moments split, `_fin` twin gone); `InverseMoments/LambdaMinTail.lean`
  (`integral_radial_gaussianVector`); `Moments/LogOverlap.lean`; `Spectral/SmallBall.lean`
  (`measureReal_sum_sq_le_le_gaussianVector`); `SubGaussian/{SubGaussianRows,SubGaussianJL}.lean`
  (`measureReal_le_abs_sum_sq_sub_card_of_hasSubgaussianMGF`).
- **A2 (Sketching):** `Properties/JL/JL.lean` (4 sites, the two Dasgupta–Gupta tails);
  `Sparse/CountSketchMoments.lean` (3 sites, `…_rademacherVector`);
  `Structured/SRHTFlattening.lean` (deleted import; `hasSubgaussianMGF_sum_mul_rademacher` takes a
  `HasLaw … (rademacherVector ι)` vector; `measureReal_sq_norm_ge_add_two_sqrt_mul_add_le`).
- **Edits made by stream S3 outside P's files and never build-verified** (call-site names only):
  `RandomMatrix/Gaussian/InverseMoments/SpectralProbe.lean` (~l.115),
  `RandomMatrix/Gaussian/Moments/LogOverlapMoments.lean` (~l.61), `Sketching/Structured/SRHT.lean:132`,
  `Sketching/Structured/SRHTWithReplacement.lean:160`, and the import lines of
  `Sketching/Structured/{SRHTCore,SRHT,SRHTWithReplacement}.lean`,
  `Sketching/Sparse/CountSketchExpectation.lean`, `RandomMatrix/Gaussian/InverseMoments/OperatorHardEdge.lean`.
- **M1:** `Matrix/Norms/Net.lean:25` names `measure_lt_specNorm_le_of_hasSubgaussianMGF` in a docstring.

### Notes for owner I

- `mathlib_prereqs` of atlas entry `positive-real-moment-comparison` (its four tags were removed
  from `ForMathlib/MeasureTheory/MomentInterpolation.lean`): `MeasureTheory.integrable_rpow_of_nonneg_of_le`,
  `MeasureTheory.integral_rpow_root_le_of_nonneg_of_le`, `MeasureTheory.integral_rpow_root_le_of_integral_rpow_le`,
  `MeasureTheory.integral_rpow_le_of_integral_rpow_le`; consumer
  `RandomMatrix/Gaussian/InverseMoments/SpectralProbe.lean` (should carry the tag).
- The `matrix-freedman (partial)` tag removed from `MeasureTheory.ae_posSemidef_condExp_of_ae_posSemidef`
  needs no new home: its consumers in `Martingales/` already carry `matrix-freedman`.
- `ForMathlib/Probability/Independence.lean` keeps both lemmas (`ProbabilityTheory.lintegral_of_indepFun`,
  `integral_of_indepFun`): Mathlib has no Fubini for a function of two independent variables.
- Not movable as the brief asks: `ForMathlib/Data/ExactRowSubset.lean` is imported by
  `Matrix/Basic/CauchyBinet.lean` (layer 0), so it cannot go to `Sketching/Sampling/` (layer 3)
  unless `CauchyBinet`'s `SizedSubset` stops using it.
