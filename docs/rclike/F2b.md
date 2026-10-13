# F2b: `gaussianMatrix` on `Matrix`, `HasLaw` as the single law interface (second F2 PR)

Agent F2b (lead) with sub-agents F2b-A (InverseMoments, Wishart, PolynomialGrowth,
Matrix/Structured) and F2b-B (Conditioning, SketchRank, Haar, Matrix/Subspaces, LowRank),
2026-10-13. Brief: `docs/FOUNDATIONS_BRIEF.md` §2 (second PR), §6. Builds on F2a
(`docs/rclike/F2a.md`: `Matrix.instMeasurableSpace`, `Matrix.instBorelSpace`,
`Matrix.ofMeasurableEquiv`).

## Definition choice

```lean
def gaussianMatrix (m n : Type*) [Fintype m] [Fintype n] : Measure (Matrix m n ℝ) :=
  (Measure.pi fun _ : m => Measure.pi fun _ : n => gaussianReal 0 1).map Matrix.ofMeasurableEquiv
```

This is the brief's first option (`.map Matrix.of`, written with the measurable equivalence so
that `MeasurableEquiv`/`MeasurePreserving` lemmas apply without coercion bookkeeping). The other
option, the pi measure typed directly as a measure on `Matrix` (accepted by the elaborator since
`Matrix.instMeasurableSpace` is `MeasurableSpace.pi`), was implemented first and rejected:
`unfold gaussianMatrix` then produces `Measure.pi …` at type `Measure (Matrix m n ℝ)`, which is
not type-correct at instance transparency, so `rw` with `Measure.pi_pi`,
`integral_fintype_prod_eq_prod` etc. fails ("motive is not type correct", "function expected").
With the push-forward definition every basic fact is one composition with
`measurePreserving_ofMeasurableEquiv_gaussianMatrix` (which holds by `rfl`), and downstream proofs
never unfold: they move to the product measure with `integral_gaussianMatrix_eq` /
`integrable_gaussianMatrix_iff`. The `Fin p`/`Fin m` law is `gaussianMatrix (Fin p) (Fin m)`; there
is no separate definition.

## Core API (`RandomMatrix/Gaussian/Basic/GaussianMatrix.lean`), all over `[Fintype m] [Fintype n]`

| declaration | content |
|---|---|
| `measurePreserving_ofMeasurableEquiv_gaussianMatrix` | `Matrix.of` pushes `⊗ᵢ⊗ⱼ N(0,1)` to `gaussianMatrix m n` (the definition) |
| `integral_gaussianMatrix_eq`, `integrable_gaussianMatrix_iff` | integrals / integrability move to the product measure on `m → n → ℝ` |
| `isProbabilityMeasure_gaussianMatrix` (instance) | |
| `measurePreserving_gaussianMatrix_entry`, `memLp_gaussianMatrix_entry` | entry law `N(0,1)`, all moments |
| `measurePreserving_gaussianMatrix_row`, `iIndepFun_gaussianMatrix_row` | rows are i.i.d. standard Gaussian vectors |
| `iIndepFun_gaussianMatrix_entry` | entries (indexed by `m × n`) are independent |
| `integral_comp_gaussianMatrix_entry_eq`, `integral_gaussianMatrix_entry_eq_zero`, `integral_gaussianMatrix_entry_sq_eq_one`, `integrable_const_mul_gaussianMatrix_entry_mul`, `integral_gaussianMatrix_entry_mul` | first two moments, `E[G_ab G_cd] = δ_ac δ_bd` |
| `gaussianMatrix_map_uncurry`, `gaussianMatrix_eq_map_curry` | flattening to `Measure.pi` on `m × n` and back (through `(MeasurableEquiv.curry m n ℝ).trans Matrix.ofMeasurableEquiv`) |
| `isGaussian_gaussianMatrix` (instance), `hasGaussianLaw_id_gaussianMatrix` | Gaussian measure on `Matrix m n ℝ` (via `isGaussian_map_of_measurable`, no norm needed) |
| `measurable_block` | `Measurable fun G : Matrix m t ℝ => Vᵀ * G` |
| `linForm (c : m → n → ℝ) (G : Matrix m n ℝ)`, `linForm_eq_frobInner`, `continuous_linForm` | coefficient stays an array, the sample is a matrix |

Removed: `aemeasurable_of_map_eq_gaussianMatrix` (use `HasLaw.aemeasurable`).

Law predicates: `IsStandardGaussian μ g` and `IsRademacher μ r` are now `abbrev`s of
`HasLaw g (gaussianReal 0 1) μ` and `HasLaw r rademacherMeasure μ` (argument order unchanged;
`isRademacher_iff_map_eq` kept, now proved). `IsGaussian`/`HasGaussianLaw` for vectors unchanged.

`Matrix` has no global norm. Where a Mathlib result needs a normed sample space (`HasGaussianLaw.map_fun`,
`IsGaussian` of a product, Fernique) the files use `open scoped Matrix.Norms.L2Operator` (its
topology is `Matrix`'s, so the Borel instance applies; SpectralSecondMoment) or
`Matrix.Norms.Elementwise` with an explicit `BorelSpace` term (PolynomialGrowth, F2b-A), or flatten.

## Laws: `μ.map … = gaussianMatrix …` → `HasLaw`

Every hypothesis `μ.map X = gaussianMatrix …` and `μ.map (fun ω => Matrix.of.symm (G ω)) = …` is now
`HasLaw X (gaussianMatrix (Fin p) (Fin m)) μ` with `X : Ω → Matrix (Fin p) (Fin m) ℝ` (Conditioning,
SketchRank, HaarQR, all of LowRank). Laws of deterministic maps that were stated as
`Measure.map f (gaussianMatrix …) = gaussianMatrix …` are `HasLaw f (gaussianMatrix …) (gaussianMatrix …)`:

| old | new (+ corollary for a random matrix) |
|---|---|
| `gaussianMatrix_map_orthogonal` | `hasLaw_gaussianMatrix_orthogonal` (now over `Fintype` index types), `…_of_hasLaw` |
| `gaussianMatrix_map_block` | `hasLaw_gaussianMatrix_block` (rows `Fin n`: the completion lemma needs `Fin`; `k t` over `Fintype`), `…_of_hasLaw` |
| `gaussianMatrix_indepFun_block` | same name (Fintype `k r t`), `gaussianMatrix_indepFun_block_of_hasLaw` |
| `gaussianMatrix_map_transpose` | `hasLaw_gaussianMatrix_transpose`, `…_of_hasLaw` |
| `gaussianMatrix_map_mul_right` | `hasLaw_gaussianMatrix_mul_right`, `…_of_hasLaw` |
| `gaussianMatrix_map_first_cols` (B) | `hasLaw_gaussianMatrix_first_cols` |

Orthonormality hypotheses of these (and of Conditioning, DiagonalLaw/Residual/OffDiagonal) are
`HasOrthonormalCols V`. The vector laws in LinearImage (`gaussianMatrix_map_mulVec*`, `= Measure.pi …`)
and the Haar laws in HaarQR (`= haarFrameLaw/orthogonalHaar`) keep their measure-identity form
(not Gaussian-matrix laws); HaarQR gained `_of_hasLaw` forms.

## Wrappers deleted / renamed (all in `docs/renames/2026-10-F2.json`)

`map_block_eq_gaussianMatrix`, `indepFun_block_of_map_eq` (Conditioning; duplicates of the
Invariance corollaries), `aemeasurable_of_map_eq_gaussianMatrix`;
`ae_hasOrthonormalCols_gaussianRangeFrame_of_map_eq` → `…_of_hasLaw`,
`ae_project_gaussianRangeFrame_of_map_eq` → `…_of_hasLaw` (SketchRank);
`integral_powerRayleighRelativeError_le_of_map_eq_pi_gaussianReal` → `…_le_of_hasLaw`,
`integral_lanczosRayleighRelativeError_le_of_map_eq_pi_gaussianReal` → `…_le_of_hasLaw`
(Estimation/Spectral; vector law now `HasLaw G (Measure.pi …) μ`).

## `_of_hasLaw` corollaries added (primary statement against `gaussianMatrix` kept)

- SecondMoment `integral_frobSq_mul_gaussianMatrix_mul_of_hasLaw`; FourthMoment
  `integral_frobSq_mul_gaussianMatrix_mul_sq_of_hasLaw`; ApproxMultiplication
  `integral_frobSq_mul_gram_mul_transpose_sub_of_hasLaw`.
- Gordon `integral_specNorm_gaussianMatrix_le_sqrt_add_sqrt_of_hasLaw`,
  `sqrt_sub_sqrt_le_integral_sigmaMin_gaussianMatrix_of_hasLaw`, `gordon_extreme_singular_values_of_hasLaw`;
  Chevet `integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le_of_hasLaw`,
  `integral_specNorm_mul_gaussianMatrix_mul_le_of_hasLaw`; SpectralSecondMoment
  `integrable_and_integral_specNorm_sq_mul_gaussianMatrix_mul_le_of_hasLaw`,
  `integral_specNorm_sq_mul_gaussianMatrix_mul_le_of_hasLaw`.
- Deviation `measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix_of_hasLaw`,
  `measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix_of_hasLaw`,
  `one_sub_le_measure_sigmaMin_and_specNorm_gaussianMatrix_of_hasLaw`; SmallBall
  `measure_sq_dist_col_span_le_le_gaussianMatrix_of_hasLaw`, `measure_sigmaMin_le_le_gaussianMatrix_of_hasLaw`;
  LipschitzConcentration `gaussian_concentration_of_hasLaw`; JL `jl_distributional_of_hasLaw`.
- Invariance/LinearImage: the five `…_of_hasLaw` above.
- F2b-A (23): Mean (3), Probe (1), SimpleSpectrum (2), UnshiftedWeakInequality (3),
  OperatorHardEdge (1), LambdaMinTail (3), SpectralProbe (4), SpectralTail (3), FrobeniusMoments (3);
  names in the sub-agent list: `integrable_and_integral_inv_self_mul_transpose_gaussianMatrix_of_hasLaw`,
  `integral_inv_self_mul_transpose_gaussianMatrix_of_hasLaw`, `integrable_and_integral_frobSq_pinvR_gaussianMatrix_of_hasLaw`,
  `integrable_and_integral_rpow_specNorm_inv_self_mul_transpose_gaussianMatrix_le_of_hasLaw`,
  `ae_charpoly_separable_self_mul_transpose_gaussianMatrix_of_hasLaw`, `ae_injective_eigenvalues_self_mul_transpose_gaussianMatrix_of_hasLaw`,
  `ae_tendsto_unshiftedGram_softMin_energy_gaussianMatrix_of_hasLaw`, `integral_sigmaMin_transpose_sq_unshifted_weak_nonneg_gaussianMatrix_of_hasLaw`,
  `integral_sigmaMin_transpose_sq_law_unshifted_weak_nonneg_gaussianMatrix_of_hasLaw`,
  `gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral_of_weak_inequality_of_hasLaw`,
  `gaussianMatrix_one_sigmaMin_transpose_sq_le_eq_of_hasLaw`, `gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral_of_hasLaw`,
  `gaussianMatrix_sigmaMin_transpose_sq_le_le_of_hasLaw`, `integrable_and_integral_half_gap_rpow_specNorm_inv_gaussianMatrix_le_of_hasLaw`,
  `integrable_and_integral_rpow_specNorm_inv_gaussianMatrix_le_sharp_of_hasLaw`, `integral_rpow_specNorm_inv_gaussianMatrix_rpow_inv_le_sharp_of_hasLaw`,
  `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le_sharp_of_hasLaw`, `gaussianMatrix_lt_specNorm_pinvR_le_of_hasLaw`,
  `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le_of_hasLaw`,
  `integrable_and_integral_specNorm_inv_self_mul_transpose_pow_gaussianMatrix_le_of_hasLaw`,
  `integrable_and_integral_frobSq_inv_self_mul_transpose_gaussianMatrix_of_hasLaw`,
  `integrable_and_integral_frobSq_pinvR_sq_gaussianMatrix_of_hasLaw`, `gaussianMatrix_lt_frobSq_pinvR_le_of_hasLaw`.
- F2b-B: HaarQR `gaussianMatrix_map_canonicalQRFrame_of_hasLaw`, `gaussianMatrix_map_canonicalQR_orthogonal_of_hasLaw`.

## Tails (`μ.real s ≤ c`)

Converted statements: LipschitzConcentration `gaussian_concentration`; Deviation (all three);
SmallBall (both); GaussianEmbedding `one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix`
(`1 - δ ≤ μ.real …`); JL `jl_distributional`, `jl_lemma`, `jl_lemma_prob_le_of_log_le`,
`jl_lemma_prob_le_half`; F2b-A: `gaussianMatrix_sigmaMin_transpose_sq_le_le`,
`gaussianMatrix_lt_specNorm_pinvR_le`, `gaussianMatrix_lt_frobSq_pinvR_le`. Internal ENNReal union
bounds bridge with `ofReal_measureReal`. Not converted: measure-vs-`lintegral` bounds
(`gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral`, HardEdgeEndpoint), and the
`(μ s).toReal ≤` tails of HermitianSeries/MatrixSeries/HutchinsonTail/SLQ* (files touched only for
call-site repairs or not at all; left for the port).

## Coordinator review items (docs/review/oddities_probability.md)

1. Redundant binders dropped: `hg : AEMeasurable g μ` in `memLp_two_and_moments_of_isStandardGaussian`
   and `memLp_two_and_moments_of_isRademacher`; `[IsProbabilityMeasure μ]` in
   `hasSubgaussianMGF_of_isRademacher` and `memLp_two_and_moments_of_isRademacher` (derived from the
   law); `hMeas : Measurable g` in `gaussian_matrix_mgf_cgf_eq` and `rademacher_matrix_mgf_cgf_le`
   (callers repaired: HermitianSeries, HutchinsonLaws, DiagonalEstimator). **Skipped:** `hMeas` in
   `hermitian_gaussian_series` / `matrix_gaussian_series`: the proofs use strong measurability of
   the coefficient sums (`Finset.measurable_sum`, `Measurable.comp` in `hXMeas`); replacing it by the
   law's `AEMeasurable` needs an AEMeasurable rework of those proofs, beyond F2. Callers'
   own now-unused `hmeas` binders (HutchinsonLaws, DiagonalEstimator) were left (signature change of
   Estimation theorems, not in scope).
2. `Fintype` generalization done where the proof allowed it: Invariance (`orthogonal` fully;
   `block`/`indepFun_block` except the row index `Fin n`, needed by `exists_unitary_completion`),
   SecondMoment sandwich section, all of FourthMoment, LipschitzConcentration, Conditioning's
   sandwiched lemmas (B). InverseMoments keeps `Fin`/ℕ (statements use `(k : ℝ) - r`).
3. `gaussian_concentration` is now over `Matrix p m ℝ` (any Fintype), with a `μ.real` tail and the
   corollary `gaussian_concentration_of_hasLaw`. **`0 ≤ L` was not adopted:** it is false for
   `L = 0` (then `h` is constant, the event is everything and has probability `1 > e^{-t²/2}` for
   `t > 0`); `gaussian_concentration_pi` also requires `0 < L`.
4. Acceptance scale (counts before → after): `Matrix.of.symm` outside the ForMathlib file 36 → 0;
   `….map … = gaussianMatrix` 17 → 0; `_of_map_eq` (outside Sparse) 18 → 13, all 13 the field name
   `eq_zero_of_map_eq_zero` of NLAlib's seminorm structures (`InvariantNorm`, `SymmetricGauge`, …,
   mirroring Mathlib's `AddGroupNorm` field; not a law wrapper, not renamed); `gaussianMatrix` with ℕ
   arguments → 0 (every call is `gaussianMatrix (Fin p) (Fin m)` or over Fintype types).

## Files changed (66 Lean files + docs)

Core/lead: Probability/Gaussian/Basic/StandardGaussian, Probability/Rademacher/Core,
Probability/Concentration/Matrix/{GaussianMgfCgf,RademacherMgfCgf,HermitianSeries,MatrixSeries},
Probability/Gaussian/Moments/{SeriesKhintchine,SeriesSecondMoment}, RandomMatrix/Gaussian/Basic/
{GaussianMatrix,LinearForms,Lipschitz,LipschitzConcentration}, Invariance/{Invariance,LinearImage},
Moments/{SecondMoment,FourthMoment,ApproxMultiplication,LogOverlap},
Spectral/{Gordon,Chevet,SpectralSecondMoment,Deviation,SmallBall}, Sketching/Gaussian/GaussianEmbedding,
Sketching/Properties/JL/JL, Estimation/{QuadraticForms/HutchinsonLaws,Diagonal/DiagonalEstimator,
Spectral/RandomStartPower,Spectral/RandomStartLanczos}.
F2b-A: Matrix/Structured/{Measurable,SpectralMeasurable,GramSoftMinMeasurable},
Basic/PolynomialGrowth, Wishart/SimpleSpectrum, InverseMoments/{Residual,Mean,DiagonalLaw,
OffDiagonal,Probe,FrobeniusMoments,HardEdgeEndpoint,SpectralProbe,SpectralTail,
RegularizedApproximation,RegularizedIntegrability,ResolventLimit,CutoffIntegrability,
CutoffDerivativeIntegrability,UnshiftedWeakInequality,GaussianWeakInequality,OperatorHardEdge,
LambdaMinTail}.
F2b-B: Matrix/Subspaces/{Stiefel,CanonicalQR,PolarFrame}, Haar/HaarQR, Moments/Conditioning,
Spectral/SketchRank, LowRank/{Nystrom/GaussianNystrom,Nystrom/RawGaussianNystrom,Nystrom/Structural,
RandomizedSVD/GaussianSketch,RandomizedSVD/OptimalError,RangeFinding/ExpectedPower,
RangeFinding/SpectralRangeFinder}.
Docs: STANDARDS §3 (index types, vocabulary entry for `gaussianMatrix`/`linForm`, probability
bullet: global matrix instances, `HasLaw`, `_of_hasLaw`, `μ.real`, `HasOrthonormalCols`, norms),
`docs/renames/2026-10-F2.json` (+13 entries).

Notable statement changes beyond the mechanical ones: `Stiefel n k` is
`{Q : Matrix (Fin n) (Fin k) ℝ // HasOrthonormalCols Q}`; `norm_array_le_one_of_hasOrthonormalCols`
now bounds the L2-operator norm (name kept, no external users); Structured measurability lemmas take
`G : Matrix r k ℝ`; PolynomialGrowth's `‖G‖` is the elementwise sup norm under
`open scoped Matrix.Norms.Elementwise` (same norm as the old pi norm).

## Build and checks

```
$ lake build NLAlib.Probability NLAlib.RandomMatrix NLAlib.LowRank NLAlib.Sketching NLAlib.Estimation NLAlib.Matrix.Subspaces NLAlib.Matrix.Structured NLAlib.Matrix
Build completed successfully (4978 jobs).
```
(`NLAlib.Matrix` added because 53 Matrix modules import the changed Subspaces files.) No
`declaration uses 'sorry'` in the log; no sorry added. `python3 scripts/check_layers.py`: import
layers OK; `python3 scripts/check_names.py`: names OK (7103 declarations). `scripts/Audit.lean`,
`ExtractDecls.lean`/`sync_atlas.py`, `check_atlas.py` and a root build were not run (whole-library
Lean processes; left to the coordinator's §6 run).

## Acceptance

```
$ grep -rn "Matrix.of.symm" NLAlib
$ grep -rn "μ.map .* = gaussianMatrix\|\.map .* = gaussianMatrix" NLAlib
$ grep -rn "_of_map_eq" NLAlib --exclude-dir=Sparse | grep -v "eq_zero_of_map_eq_zero"
$ grep -rn "_of_map_eq" NLAlib --exclude-dir=Sparse | wc -l
13        (all `eq_zero_of_map_eq_zero`, the seminorm-structure field)
$ grep -rn "instance.*MeasurableSpace\|instance.*BorelSpace" NLAlib --exclude-dir=Sparse
NLAlib/ForMathlib/MeasureTheory/Matrix.lean:37:instance instMeasurableSpace …
NLAlib/ForMathlib/MeasureTheory/Matrix.lean:42:instance instBorelSpace …
$ grep -rnP "(?<![\w.])gaussianMatrix \d" NLAlib
```

## What remains

- `Matrix.of` on genuine arrays remains inside proofs that split a row off with
  `MeasurableEquiv.piFinSuccAbove` (InverseMoments Mean, DiagonalLaw, OffDiagonal: 50 occurrences,
  all on array-typed variables after `integral_gaussianMatrix_eq`), and in one private array lemma;
  a port could restate these row splits on `Matrix` (`Matrix.of` of `Fin.insertNth`).
- `gaussianMatrix_map_inv_self_mul_transpose_apply_self` (DiagonalLaw, no atlas tag) still states a
  `Measure.map … = Measure.map …` identity (not a `= gaussianMatrix` law).
- RawGaussianNystrom keeps a proof-internal product-law equation `(μ.map X).prod (gaussianMatrix …)`.
- LowRank keeps `Vᵀ * V = 1` hypotheses (rule 4 is for RandomMatrix; accepted by defeq).
- Three atlas-tagged integrability-only theorems (`gram-cutoff-vector-field`) and
  `variance_quadForm_gaussianMatrix_column` (HutchinsonLaws), `jl_lemma*` (JL) have no `_of_hasLaw`
  corollary; private helpers `integrable_and_integral_{le,eq}_of_hasLaw` in SpectralProbe /
  SpectralTail / FrobeniusMoments would be one public `HasLaw` lemma in a Mathlib-facing file.
- Not-converted tails listed above; unused `hmeas` binders in Estimation callers.
