# Probability and random-matrix layers: what an outside reader will find odd

Read-only review of `NLAlib/Probability/**`, `NLAlib/RandomMatrix/**` and the parts of
`NLAlib/ForMathlib/{Probability,MeasureTheory}` they use (branch `nlalib-f2`, 2026-10-13, F2b
mid-flight). No Lean or lake process was run. Line numbers are the `def`/`theorem` keyword lines of
the on-disk sources; `RandomMatrix/Gaussian/Basic/GaussianMatrix.lean` was being edited during the
review (its `linForm` changed signature twice), so its lines are approximate. Signatures are quoted
with binders shortened; `{Ω}` abbreviates `{Ω : Type*} [MeasurableSpace Ω]`. Counts are `grep`/
`python` over the sources and `atlas/declarations.json` (679 declarations in scope, 189 tagged).
F2b state at review time: 6 files converted to `Matrix (Fin p) (Fin m) ℝ` + `HasLaw`
(`GaussianMatrix`, `LinearForms`, `Lipschitz`, `Invariance`, `SecondMoment`, `FourthMoment`); 43
files still call `gaussianMatrix` with `ℕ` arguments on arrays `Fin p → Fin m → ℝ` (36 in scope);
17 `μ.map … = gaussianMatrix` hypotheses in 5 files; 18 `_of_map_eq` wrappers in 2 files; 36
`Matrix.of.symm` in 8 files. All of that is "F2 in flight" and is not argued below.
Sketching/LowRank/Estimation consumers belong to the algorithms review, the `Matrix`
measurable-space instance to the infrastructure review.

## Top 10

1. **Two random-matrix worlds that never meet.** The Tropp port (`Probability/Concentration/Matrix`,
   36 files) lives on `X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ` with `[NeZero d]` (34 statements),
   `‖·‖` under `Matrix.Norms.L2Operator`, `.toReal` tails and an abstract `Ω` with `iIndepFun`; the
   Gaussian world (`RandomMatrix/Gaussian`) is real, integrates against `gaussianMatrix` directly,
   uses `specNorm`/`frobNorm` and `ENNReal.ofReal` tails. No theorem applies matrix Bernstein or
   Chernoff to a Gaussian or sub-Gaussian matrix, and none can without `Matrix.map ofReal`, because
   `lambdaMax`, `matrixExp`, `traceExp`, `intrinsicDimension`, `rectSecondMoment`,
   `hermitianSecondMoment`, `cumulantSum` are ℂ-only (`Matrix/Functions/ExpLog.lean:25-53`,
   `Concentration/Basic/MatrixStatistics.lean:24-39`). *Fix (port):* state the concentration layer
   over `[RCLike 𝕜]` and `[Fintype d]`, as the matrix core already is; `[NeZero d]` becomes
   `[Nonempty d]`, which the Martingales files (23 statements) already use.
2. **Tail bounds in three currencies (four with the success form).** Statements in scope: 22
   `(μ {…}).toReal ≤ …` (Tropp port and HighDimProb files, e.g. `matrix_bernstein`
   `MatrixBernstein.lean:74`, `hanson_wright_mgf` `HansonWright.lean:141`), 34
   `μ {…} ≤ ENNReal.ofReal (…)` (ChiSquare, `Net.lean:32`, `ScalarBernstein.lean:195`, all of
   `RandomMatrix/Gaussian`), 9 `μ.real {…} ≤ …` (McDiarmid, ScalarBernstein, two ChiSquare Chernoff
   forms), one `1 - ENNReal.ofReal (…) ≤ μ {…}` (`Deviation.lean:98`). `ChiSquare.lean` alone uses
   `μ.real` at :110/:200 and `ENNReal.ofReal` at :140/:178/:224/:256/:296 for the same χ²-tails.
   The brief fixes `μ.real`. *Fix:* `μ.real` everywhere; F2b should at least convert what it touches
   (`LipschitzConcentration.lean:40` is still `ENNReal.ofReal` and still on arrays).
3. **"Standard Gaussian" is spelled six ways.** Matrices: `HasLaw X (gaussianMatrix m n) μ` (new;
   3 `_of_hasLaw` corollaries, all in `Invariance.lean`), `μ.map X = gaussianMatrix n t` (17
   hypotheses, `Conditioning.lean:45-277`, `SketchRank.lean:141-295`; F2 in flight), and
   `∀ e : n × κ, IsStandardGaussian μ (fun ω => G ω e.1 e.2)` + `iIndepFun` (29 sites in
   Estimation). Vectors: `Measure.pi fun _ : ι => gaussianReal 0 1` on `ι → ℝ` (277 occurrences in
   40 files: ChiSquare, LogSobolev, Isserlis, Stein, SmallBall, …), Mathlib's
   `stdGaussian (EuclideanSpace ℝ (Fin n))` (8 files, the HighDimProb port in `QuadraticForms/`),
   and processes as `HasGaussianLaw (fun ω t => X t ω) P` (`Slepian.lean:317`,
   `SudakovFernique.lean:282`, `GordonMinimax.lean:545`). There is no `gaussianVector ι` and no
   bridge between `Measure.pi … gaussianReal` and `stdGaussian`. *Fix:* one vector law (Mathlib's
   `stdGaussian` with a `Measure.pi` bridge, or a named `gaussianVector ι` plus `HasLaw`
   corollaries); consumers take `HasLaw`.
4. **"Independent Rademacher signs" is spelled three ways, and noncommutative Khintchine is proved
   twice.** Abstract: `(hind : iIndepFun ε μ) (hlaw : ∀ i, IsRademacher μ (ε i))`
   (`SubGaussian/Moments.lean:122`, the Tropp series). Concrete product:
   `Measure.pi (fun _ => rademacherMeasure)` as the probability space in 19 statements
   (`Concentration/Matrix/RademacherKhintchine.lean:25-142`, `RademacherPolynomialMoments.lean`,
   `QuadraticForms/RademacherQuadraticMoments.lean`, `Rademacher/RademacherSymmetry.lean`). Boolean
   cube: `rademacherCubePMF ι : PMF (ι → Bool)` with `rademacherBoolSign`
   (`Rademacher/RademacherCube.lean:46`, for SRHT). `integral_re_trace_rademacherSeries_pow_le`
   (`RademacherKhintchine.lean:142`, concrete) and `integral_re_trace_independent_series_pow_le`
   (`Gaussian/Moments/SeriesKhintchine.lean:31`, abstract, disjunctive law) both carry
   `atlas: noncommutative-khintchine`. *Fix:* the abstract form is the theorem, the concrete product
   its `HasLaw` corollary; replace the `PMF (ι → Bool)` encoding by the `rademacherMeasure` product.
5. **The disjunctive law hypothesis.** Five theorems take
   `hLaw : (∀ k, IsStandardGaussian μ (g k)) ∨ (∀ k, IsRademacher μ (g k))`
   (`MatrixSeries.lean:102`, `HermitianSeries.lean:196`, `SeriesKhintchine.lean:31/:69`,
   `SeriesSecondMoment.lean:78`). A probabilist expects the class the proof uses: the only facts
   consumed are `HasSubgaussianMGF (g k) 1 μ` (giving `𝔼 e^{θ g A} ≤ e^{θ²A²/2}` through
   `integrable_and_integral_matrixExp_smul_eq_cfc_mgf`, `MatrixCalculus.lean:67`) and `𝔼 g² = 1`
   for the variance identity; mixed series are excluded for no reason. *Fix:* hypotheses
   `∀ k, HasSubgaussianMGF (g k) 1 μ` and `∀ k, ∫ g k ^ 2 = 1`; Gaussian and Rademacher are
   one-line corollaries.
6. **Headlines are `let`-`∧` bundles whose first conjunct is bookkeeping, and one is `∃ C`.** 41 of
   the 189 tagged declarations in scope are `∧`-bundles; 27 statement-level `let`s in 14 files.
   `matrix_bernstein` (`MatrixBernstein.lean:74`) returns
   `v = max ‖∑ 𝔼 S Sᴴ‖ ‖∑ 𝔼 Sᴴ S‖ ∧ 𝔼‖Z‖ ≤ … ∧ ∀ t, …`; `matrix_chernoff`
   (`MatrixChernoff.lean:119`) has five conjuncts and three `let`s; `gordon_extreme_singular_values`
   (`Gordon.lean:598`) has five (two of them integrability). A user must `.2.2` into them and cannot
   `rw` with the variance identity. `intrinsic_matrix_bernstein_expectation`
   (`IntrinsicBernsteinExpectation.lean:160`) is `∃ C : ℝ, 0 < C ∧ ∀ {Ω} …`, the only `∃ C` in the
   library, although the proof is `refine ⟨20, …⟩`. *Fix:* one theorem per conclusion (STANDARDS
   §3); state `C = 20`.
7. **The new `HasLaw` abbrevs carry Mathlib-unlike names and argument order, and their consumers
   keep hypotheses the abbrev contains.** `IsStandardGaussian μ g := HasLaw g (gaussianReal 0 1) μ`
   (`StandardGaussian.lean:31`) and `IsRademacher μ r` (`Rademacher/Core.lean:42`) put the measure
   first; Mathlib's `HasLaw X ν μ` and `HasGaussianLaw X μ` put it last, and `Is…` is Mathlib's
   prefix for a predicate on one object, not for "has law ν". Then
   `memLp_two_and_moments_of_isStandardGaussian … (hg : AEMeasurable g μ) (hlaw : IsStandardGaussian μ g)`
   (`StandardGaussian.lean:100`; same at `Rademacher/Core.lean:115`) takes what `hlaw.aemeasurable`
   gives; 10 sites take `(hMeas : Measurable g)` next to the law (`GaussianMgfCgf.lean:28`,
   `RademacherMgfCgf.lean:38`, `HermitianSeries.lean:196`, `MatrixSeries.lean:102`); 8 sites take
   `[IsProbabilityMeasure μ]` next to a law of mass 1 (`hasSubgaussianMGF_of_isRademacher`,
   `Rademacher/Core.lean:94`, while the Gaussian twin `StandardGaussian.lean:143` does not).
   `isRademacher_iff_map_eq` (`:48`) has no Gaussian twin. *Fix (F2b, now):*
   `HasStandardGaussianLaw g μ` / `HasRademacherLaw r μ` (or plain `HasLaw`), drop the redundant
   binders, state the mgf lemmas with `AEMeasurable` from the law.
8. **Junk-valued spectral vocabulary drives the concentration hypotheses.**
   `lambdaMax A := sSup (spectrum ℝ A)`, `lambdaMin` (`ExpLog.lean:25/:31`) are `0` on a matrix with
   no real spectrum and are not `IsHermitian.eigenvalues₀`; `intrinsicDimension A := re (tr A) / ‖A‖`
   (`IntrinsicDimension.lean:36`) is `0` at `A = 0`, which is why `intrinsic_matrix_bernstein`
   needs `hV : V₁ ≠ 0 ∨ V₂ ≠ 0` and `intrinsic_matrix_chernoff` `hM : M ≠ 0`;
   `rectSecondMoment μ Z := max ‖∫ Z Zᴴ‖ ‖∫ Zᴴ Z‖` (`MatrixStatistics.lean:24`) is `0` for
   non-integrable `Z`; `matrixExp := NormedSpace.exp` but `matrixLog := cfc Real.log`, two calculi
   bridged by `matrixExp_smul_eq_cfc`. PSD is `0 ≤ lambdaMin (X k ω) ∧ lambdaMax (X k ω) ≤ L` in
   `matrix_chernoff` and `(X k ω).PosSemidef` in `intrinsic_matrix_chernoff`
   (`IntrinsicChernoff.lean:152`); "Hermitian" is the a.e. hypothesis
   `∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian` (54 occurrences). *Fix:* `lambdaMax` from `eigenvalues₀`
   with an `IsHermitian` argument (or document the junk); PSD as `0 ≤ X k ω` under `MatrixOrder`;
   say once that a.e.-Hermitian is deliberate.
9. **Hanson–Wright exists twice, once in HighDimProb dialect.** `hanson_wright_mgf`
   (`HansonWright.lean:141`, `[Fintype ι]`, constant `1/(256 e²)`, tagged `hanson-wright`) and
   `hanson_wright_inequality` (`UniversalBound.lean:37`, `Fin n`, untagged) with hypotheses
   `4e ≤ C`, `8e³ ≤ C`, `16e ≤ C²`, `64e² ≤ C`, `0 < frobNorm A`, `0 < specNorm A`, proxy
   `⟨K ^ 2, sq_nonneg K⟩`, names `h_indep`/`hX_subG` (69 sites vs 11 `hind`),
   `set_option maxRecDepth 5000`. Most of `QuadraticForms/` (14 files, 4.0k lines) and
   `SubGaussian/{EvenMoments,ExpSquare,CenteredSquare}` are this port, `Fin n`-indexed with
   `EuclideanSpace` detours (`randomVector`, `coordinateMask`, `subtypeMask`, `Geometry.lean:117-172`).
   *Fix:* keep `hanson_wright_mgf` and `hanson_wright_of_lintegral_exp_sq_le_two`; the rest is
   proof scaffolding (manifest `merge`/`drop`).
10. **Provenance language an outsider cannot resolve, and NLAlib-specific subtrees inside
    ForMathlib.** "operator re-derivation `sh:haar-unique`", "`audit:local-moment`", "manuscript
    `cor:mcdiarmid`" occur on 133 lines in 33 files; "actual" ("the actual Haar frame law", "an
    actual finite independent sign cube") on 138 lines in 38 files; "genuine" 36 times; "audit G1
    C9" 19 times. In `ForMathlib`: `uniformExactRowSubsetPMF` and the four `UniformSampling*.lean`
    (641 lines, "supports atlas `srht-ose`"), `UniformCollision.lean` ("CountSketch Gram-error"),
    and the five weak-density files
    `{LocalWeakDensity,WeakDensity,WeightedWeakDensity,MonotoneDensity,SmoothMeasureComparison}.lean`
    (1027 lines, each "Section 5 of operator_rederivations.tex, atlas wishart-lambda-min-tail"),
    which exist for one theorem. *Fix:* replace manuscript labels by the published source and the
    atlas id; move sketch-specific sampling to `Sketching/Sampling` and the density files next to
    `InverseMoments` (a proof-named subtree), or state them as Mathlib candidates without NLAlib
    references.

## 1. Definitions a probabilist would find odd

- `gaussianMatrix (m n : Type*) [Fintype m] [Fintype n] : Measure (Matrix m n ℝ) :=
  (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1).map Matrix.ofMeasurableEquiv`
  (`GaussianMatrix.lean:59`): fine. But the converted consumers still write
  `gaussianMatrix (Fin p) (Fin m)` with `{p m : ℕ}` (`Invariance.lean:134/:218/:268`,
  `SecondMoment.lean:95`, `FourthMoment.lean:338`), so the `Fin` that STANDARDS §3 allowed only
  "where a Gaussian law needs the product measure" survives after its reason is gone. F2 in
  flight; if F2b restates these anyway, `{m n : Type*} [Fintype m] [Fintype n]` costs nothing now.
- `linForm c G` with `linForm_eq_frobInner … := rfl` (`GaussianMatrix.lean:274`; during the review
  `c` changed from `Matrix m n ℝ` to `m → n → ℝ`, so the `rfl` bridge may be gone): a second
  spelling of the Frobenius pairing, kept so the comparison proofs can index families
  `linForm (a t)`. STANDARDS §3 lists it; the docstring should say why `frobInner` is not used.
- Chi-square has no measure: `χ²_d` is always `(Measure.pi fun _ : Fin d => gaussianReal 0 1)`
  applied to `{g | ∑ i, g i ^ 2 ≤ u}` (`ChiSquare.lean:110-296`), and the one `[Fintype ι]`
  statement has a `_fin` twin tagged with the same atlas id
  (`integrable_and_integral_inv_sum_sq_gaussianReal` `:728` vs `…_fin` `:764`). *Fix:* delete
  the twin; a `chiSquare d : Measure ℝ` would let tails be stated on ℝ.
- Sub-Gaussian/sub-exponential: Mathlib's `HasSubgaussianMGF X c μ` throughout (23 files); ψ₂/ψ₁
  enter as `∫⁻ ω, ENNReal.ofReal (exp ((X ω / K) ^ 2)) ∂μ ≤ 2` (`HansonWright.lean:170`,
  `OrliczMGF.lean:116`) and `∫⁻ … exp (|X|/K) … ≤ 2` (`ScalarBernstein.lean:195`), never as a
  named Orlicz norm. Intentional (Mathlib has none); state the dictionary once. Variance proxies
  are `⟨K ^ 2, sq_nonneg K⟩` (60+ sites) and `⟨C / 4, by positivity⟩` (`McDiarmid.lean:252`):
  tactic proofs inside statements. *Fix:* `(K : ℝ≥0)` and `K ^ 2`.
- Haar: `Stiefel n k := {Q : Fin n → Fin k → ℝ // HasOrthonormalCols (Matrix.of Q)}`
  (`Matrix/Subspaces/Stiefel.lean:38`, an array subtype), `orthogonalHaar (n : ℕ)`
  (`HaarFrameMeasure.lean:21`), `haarFrameLaw (n k : ℕ) (hkn : k ≤ n) : Measure (Stiefel n k)`
  (`:47`, a proof argument in a definition), `gaussianMatrix_map_canonicalQRFrame … :
  (gaussianMatrix n k).map (canonicalQRFrame n k hkn) = haarFrameLaw n k hkn` (`HaarQR.lean:37`)
  as `map =`, not `HasLaw`; `HaarQR.lean` still builds `Matrix.of.symm (O * Matrix.of G)`. F2 in
  flight (manifest: rebuild); at port `Stiefel` is a subtype of `Matrix` and `hkn` goes
  (`Stiefel n k` is empty when `k > n`).
- Matrix mgf/cgf: `cumulantSum μ X θ := ∑ k, matrixLog (∫ matrixExp (θ • X k))`
  (`MatrixStatistics.lean:39`) is `Fin N`-indexed and silently `cfc Real.log 0 = 0` when an
  integral is not integrable. The mgf/cgf lemmas return pairs
  `(∫ matrixExp (θ g • A)) ≤ matrixExp (θ²/2 • A²) ∧ matrixLog (…) ≤ θ²/2 • A²`
  (`GaussianMgfCgf.lean:28`, `RademacherMgfCgf.lean:38`, `BernsteinMgfCgf.lean:27`,
  `ChernoffMgfCgf.lean:125`), the second conjunct being `matrixLog` monotonicity applied to the
  first. *Fix:* state the mgf bound; the cgf form is a lemma about `matrixLog`.
- Lieb and the Laplace method: `integral_traceExp_add_le_traceExp_add_matrixLog`
  (`ProbabilisticLieb.lean:30`) is Tropp Cor. 3.3.1 with `(hMeas : Measurable X)`, a.e.-Hermitian
  and `Integrable (matrixExp ∘ X)`; deterministic Lieb concavity is
  `isGreatest_variational_traceExp` (`Matrix/OperatorTheory/VariationalTraceExp.lean:26`,
  `[NeZero d]`, ℂ). Golden–Thompson is not stated; `norm_matrixExp_sum_le_prod`
  (`TraceExpBounds.lean:141`) is the norm form used instead. Document which inequality each master
  bound uses.
- Tail/dimension constants are defs with piecewise junk: `bernsteinTail d v L t` is `d` when
  `v + Lt/3 = 0 ∧ t = 0` and `0` when `v + Lt/3 = 0 ∧ t ≠ 0` (`MatrixStatistics.lean:47`),
  `gaussianSeriesTail` likewise (`ScalarLaws.lean:24`), `chernoffLowerTail d a L ε = d` when
  `L = 0` (`ChernoffFunctions.lean:23`), `mcdiarmidTail C t = if 0 < t then 0 else 1` when `C = 0`
  (`McDiarmid.lean:247`). Intentional (degenerate cases are proved); each docstring says so.
- `HasLocalMatrixSecondMoment μ m X V` (`Martingales/LocalSecondMoment.lean:56`): "`V` is the
  conditional second moment of `X`" encoded as equality of `lintegral`s of `‖X u‖²` and
  `⟨u, V u⟩` over every `m`-measurable set and every `u`, so that nothing is assumed integrable. A
  probabilist expects `μ[X ^ 2 | m] =ᵐ[μ] V`. Intentional (weaker); the docstring "genuine local
  conditional second moment" does not explain. *Fix:* rename (`IsCondSecondMoment`) and prove the
  `condExp` bridge both ways.

## 2. Statements weaker, stranger or more hypothesis-laden than the source

- `matrix_chernoff` (`MatrixChernoff.lean:119`): expectation bounds for every `θ > 0` "before
  optimisation" instead of Tropp's (5.1.3)–(5.1.4) with `(1 - e⁻¹)`, `(e - 1)`; the tails match
  (5.1.5)–(5.1.6), `ε < 1` for the lower tail as in the source. Document the deviation in the atlas.
- `hermitian_bernstein` (`HermitianBernstein.lean:133`) takes `hL2 : ∀ k, MemLp (X k) 2 μ` in
  addition to `λmax(X k) ≤ L` a.e.: needed (a one-sided bound gives no integrability); Tropp
  assumes it tacitly. Intentional, document.
- `master_bounds` (`MasterBounds.lean:25`) takes `hInt : ∀ k, Integrable (X k) μ` *and*
  `hExp : ∀ k, Integrable (matrixExp (θ • X k)) μ`; for Hermitian `X k` and `θ ≠ 0` the first
  follows from the second. Hypothesis that is (almost) always implied.
- 11 hypotheses are named `_hMeas`/`_hHerm`/`_hB`/`_ht` because the proof does not use them
  (`DilationVariance.lean:28`, `GeneralizedLaplace.lean:48`, `LaplaceTails.lean:56`,
  `VarianceAdditivity.lean:23`, `IndependentSumSecondMoment.lean:41`, `ScalarBernstein.lean:27`,
  `LambdaMinTail.lean:240`, `LogOverlap.lean:36`, …). *Fix:* delete them.
- `gaussian_concentration` (`LipschitzConcentration.lean:40`): `hL : 0 < L` where `0 ≤ L`
  suffices (at `L = 0` the event has probability `1 ≤ e⁰`); bundles integrability with the tail; on
  arrays; `ENNReal.ofReal`. `gaussian_concentration_pi` (`Probability/…/LipschitzConcentration.lean:42`)
  is the same statement on `ι → ℝ`; the matrix one should be its `HasLaw` corollary.
- `measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix` (`Deviation.lean:41`) and
  `gordon_extreme_singular_values` (`Gordon.lean:598`) use the real-only `sigmaMin (Matrix.of A)`,
  `0` for wide `A` (lower bound vacuous there, documented), and need `hn : 1 ≤ n` because
  `sigmaMin` on an empty index is junk: Gordon with a hypothesis the source does not have (the
  matrix review owns `sigmaMin`).
- `bernstein_sum_of_lintegral_exp_abs_le_two` (`ScalarBernstein.lean:195`, ψ₁ Bernstein, constant
  `1/64`, `K i ≤ B`) and `…_uniform` (`:251`, `K i = K`) are two theorems for one.
- `matrix_chernoff_sampling_lower/upper` (`Sampling.lean:93/:125`): index `Fin N` "inherited from
  `matrix_chernoff`" per docstring, i.e. a `Fin` kept because a dependency has it (STANDARDS §3
  calls this a defect). Without-replacement sampling (`SamplingWithoutReplacementTails.lean:36/:94/:153`,
  `UniformIidSampling.lean:18`) uses `(uniformExactRowSubsetPMF hk).toMeasure` and
  `(PMF.uniformOfFintype (Fin k → α)).toMeasure` as the probability space: a fourth way (after
  `Ω`, `Measure.pi`, `PMF (ι → Bool)`) to say "draw `k` indices".
- `matrix_freedman` (`Freedman.lean:31`) matches Tropp 2011 Thm 1.2 including `t = 0`, `L = 0`;
  `hXMeas : ∀ j, Measurable[ℱ (j + 1)] (X j)`, `hXInt`, `hMean : μ[X j | ℱ j] =ᵐ 0` and
  `HasLocalMatrixSecondMoment` spell out the adapted-difference package instead of Mathlib's
  `Adapted`/`Martingale`. Intentional; document the correspondence.
- Hypotheses that are always true: `[IsProbabilityMeasure μ]` next to a `HasLaw` (8 sites);
  `AEMeasurable g μ` next to a `HasLaw` (`StandardGaussian.lean:100`, `Rademacher/Core.lean:115`);
  `Measurable g` where `AEMeasurable` would do (10 sites); `hV : V ≠ 0`/`hM : M ≠ 0` that exist
  only because `intrinsicDimension 0 = 0` (Top 10 #8).

## 3. Vocabulary inconsistencies that survive

- Laws: Top 10 #3, #4, #7. Also `hasGaussianLaw_id_gaussianMatrix` (`GaussianMatrix.lean:256`)
  next to the instance `isGaussian_gaussianMatrix` (`:233`): it is `IsGaussian.hasGaussianLaw_id`.
- Norms: 16 statements write `‖A‖` on a matrix (Tropp/Freedman/sampling files, e.g.
  `hBound : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ L` in `matrix_bernstein`, `v := max ‖V₁‖ ‖V₂‖` in
  `intrinsic_matrix_bernstein`, `‖matrixIncrementSum V k ω‖ ≤ v` in `matrix_freedman`); 19
  Concentration statements use `specNorm`/`frobNorm` (`Net.lean`, `QuadraticForms`,
  `SubGaussianRows`). STANDARDS §3 exempts "the Probability files"; the exemption makes
  `rectSecondMoment`/`hermitianSecondMoment` print as `‖∫ …‖` with the scoped instance invisible in
  the signature. *Fix:* `specNorm` in definitions and statements; `‖·‖` only inside proofs.
- `IsSymm` vs `IsHermitian`: `variance_quadForm_of_isSymm` and two `…_of_fourth_moment_eq_*`
  (`QuadraticMoments.lean:339/:361/:378`) take `hA : A.IsSymm` on `Matrix n n ℝ`; everything else
  takes `IsHermitian`. *Fix:* `IsHermitian`.
- Orthonormal columns: `hU : Uᵀ * U = 1` (`LinearImage.lean:68`, `DiagonalLaw.lean:263`,
  `SchurComplement.lean:147`) and `hV₁ : V₁ᵀ * V₁ = 1` (`Conditioning.lean:45-277`) vs
  `HasOrthonormalCols` in the converted `Invariance.lean`. F2 in flight.
- ASCII Greek: `lambdaMax`, `lambdaMin`, `sigmaMin`, `gammaRatio_le` (`LambdaMinTail.lean:323`)
  in 20+ theorem names (`integral_lambdaMax_le_and_le_integral_lambdaMin`,
  `measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix`). Mathlib would write
  `eigenvalueMax`/`singularValueMin`; the definitions are the matrix review's, the names propagate.

## 4. Structural oddities

- Tropp port vs NLAlib. Tropp 2015: `Concentration/Basic/{MatrixStatistics,MatrixCalculus,ChernoffFunctions,ScalarLaws}`
  and most of `Concentration/Matrix` ("Ported from the Prove2me mission": 21 files, each declaring
  `theorem NLAlib.foo` after `end NLAlib` / `open NLAlib`, 27 files in all, a pattern no other
  directory uses). Tropp 2011 Freedman: `Martingales/` (13 files, "operator rederivations").
  Prove2me Gaussian series: `Probability/Gaussian/**`, `RandomMatrix/Gaussian/**`, `ChiSquare`.
  HighDimProb (Apache-2.0): most of `QuadraticForms/` and `SubGaussian/{EvenMoments,ExpSquare,CenteredSquare}`.
  "Operator re-derivation" manuscript: `Haar/`, `RandomMatrix/SubGaussian/`, `Sampling/`,
  `Rademacher/{RademacherCube,RademacherSymmetry}`, `ChiSquare/DirectionalSquaredNorm`,
  `Scalar/McDiarmid`, `Entropy/`, the hard-edge half of `InverseMoments/`. A reader cannot tell
  these apart from the tree; a provenance line in each aggregator's module docstring would help.
- Matrix content in the scalar directory: `Probability/Gaussian/Moments/{Khintchine,SeriesKhintchine,SeriesSecondMoment,SeriesPolynomialMoments}.lean`
  are about `∑ i, ξ i • A i` with `A i : Matrix ι ι ℂ` and belong with
  `Concentration/Matrix/RademacherKhintchine.lean` (Top 10 #4). `Probability/ChiSquare/DirectionalSquaredNorm.lean`
  ("supports `srht-ose`") and `Probability/Sampling/FiniteSampling.lean` are sketching support in layer 1.
- Proof-named subtree: `RandomMatrix/Gaussian/InverseMoments` is 21 files / 5069 lines, of which
  `{Probe,SpectralProbe,WeakInequality,UnshiftedWeakInequality,GaussianWeakInequality,OperatorHardEdge,HardEdgeEndpoint,RegularizedApproximation,RegularizedIntegrability,ResolventLimit,CutoffIntegrability,CutoffDerivativeIntegrability,LambdaMinTail}`
  are the steps of one proof (`wishart-lambda-min-tail`), with step-names as theorem names
  (`integral_sigmaMin_transpose_sq_law_unshifted_weak_nonneg_gaussianMatrix`,
  `UnshiftedWeakInequality.lean:400`) and the 1027-line weak-density cluster in ForMathlib as its
  tail (Top 10 #10). The consumer-facing results are `gaussianMatrix_sigmaMin_transpose_sq_le_le`
  (`LambdaMinTail.lean:390`), `gaussianMatrix_lt_specNorm_pinvR_le` (`SpectralTail.lean:235`) and
  the `integrable_and_integral_*_pinvR_*` moments (`Mean.lean:235`, `FrobeniusMoments.lean:110`,
  `SpectralProbe.lean:123`). *Fix (port):* `InverseMoments/{Mean,Moments,Tails}.lean` plus one
  `HardEdge/` proof directory; density lemmas stated for Mathlib without atlas references.
- ForMathlib material that is NLAlib-specific: Top 10 #10; also `MatrixConditionalExpectation.lean`,
  `ConditionalParameterJensen.lean`, `IntegralUpdate.lean`, `MomentInterpolation.lean` name the
  NLAlib result they serve. Genuine Mathlib candidates, correctly marked: `Independence.lean`,
  `IndepExpSum.lean`, `MapProd.lean`, `TailComparison.lean`, `BoundedDifferences.lean`,
  `NonnegativeSupermartingale.lean`.

## Top 10, one line each

1. Tropp port is ℂ/`Fin d`/`‖·‖`/`.toReal`; Gaussian world is ℝ/`specNorm`/`ENNReal`; nothing crosses.
2. Tails in `.toReal` (22), `ENNReal.ofReal` (34), `μ.real` (9), `1 - ofReal ≤` (1); `ChiSquare.lean` uses two.
3. "Standard Gaussian" spelled six ways (`HasLaw`, `μ.map =`, entrywise `IsStandardGaussian`, `Measure.pi`, `stdGaussian`, `HasGaussianLaw`).
4. "Independent Rademacher signs" spelled three ways; noncommutative Khintchine proved twice.
5. Disjunctive `Gaussian ∨ Rademacher` law hypothesis instead of `HasSubgaussianMGF g 1 ∧ 𝔼 g² = 1`.
6. Headlines are `let`-`∧` bundles with a bookkeeping first conjunct; one `∃ C` (C = 20 in the proof).
7. `IsStandardGaussian μ g` naming/argument order vs Mathlib `HasLaw g ν μ`; redundant `AEMeasurable`/`Measurable`/`[IsProbabilityMeasure]` binders.
8. Junk-valued `lambdaMax`/`intrinsicDimension`/`rectSecondMoment` drive `≠ 0` hypotheses; PSD and Hermitian spelled two ways.
9. Hanson–Wright twice; HighDimProb dialect (`Fin n`, `h_indep`, four constant hypotheses, `⟨K ^ 2, sq_nonneg K⟩`).
10. Manuscript provenance labels ("operator re-derivation", "actual") and NLAlib-specific subtrees inside ForMathlib.
