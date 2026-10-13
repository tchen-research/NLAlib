# F4 consistency round: handoff (2026-10-13)

The round was stopped mid-wave-1 and handed over. **The tree at this commit does not build.**
The last green commit is `75cf87d` (F4 wave 0) on this branch; before it, `04038b8` (F2) on
`nlalib-f2`.

## What to read

1. `docs/F4_CONSISTENCY_BRIEF.md`: the decisions (N norms, S spectral quantities, D duplicates
   and names, A algorithms, P probability, I atlas/docs/infrastructure), file ownership, waves.
2. `docs/STANDARDS.md` §3: the spec the round implements (Norms, Condition number, laws, tails,
   statement rules). It is ahead of the code.
3. `docs/review/STATE_2026-10-13.md` and `docs/review/oddities_{matrix,algorithms,probability,infrastructure}.md`:
   the findings the brief answers, with `file:line`.
4. `docs/f4/<agent>.md`: each has a section **"State at handoff"** written from the files and
   one build, not from the earlier claims. Trust that section over the tables above it:
   `M1.md` (Matrix/{Norms,Perturbation,Spectral,Calculus,Structured,Measurability}),
   `M2.md` + `M2-B/Fa/I/S/F/S1/S2.md` (Matrix/{Basic,Subspaces,Factorizations,Inequalities,Functions,OperatorTheory}),
   `P.md` (Probability, ForMathlib probability), `A1.md` (Krylov, Polynomial, Estimation).
5. `docs/renames/2026-10-F4-*.json`: old → new names (or a recipe). 611 entries in total.
   Downstream call sites in RandomMatrix, Sketching, LowRank, Solvers have **not** been updated.

## Branches

| branch | head | state |
|---|---|---|
| `nlalib-scaffold` | `a45c47a` | F1, green, not pushed. PR link `/tmp/rclike/PR_F1_url.txt` |
| `nlalib-f2` | `04038b8` | F2 + tooling fixes + reviews, green, not pushed. PR link `/tmp/rclike/PR_F2_url.txt` |
| `nlalib-f4` | this commit | wave 0 green at `75cf87d`; wave 1 in progress on top, **broken** |

## Done and compiled

- Wave 0 (`75cf87d`): `HasOrthonormalCols` and `projResidual` (was `residual`) in
  `Matrix/Basic/Orthonormal.lean`; `conditionNumber` → `moorePenroseConditionNumber`; all 37
  deprecated aliases deleted; `autoImplicit`/`BigOperators` lines removed.
- Lints: `scripts/check_norms.py`, `scripts/check_docstrings.py` (not yet in CI).
- `Matrix/Basic` and `Matrix/OperatorTheory` build. All of `Polynomial`, `Krylov/Spaces`,
  `Krylov/Processes/Arnoldi`, `Krylov/Spectral/QRAlgorithm` build. `ForMathlib` builds. Most of
  `Probability` builds.

## On disk but never compiled

Large parts of wave 1 are text edits that no build has reached, because an upstream module
fails first. In particular: the new `conditionNumber : ℝ≥0∞` and its API (N4); most of
`Matrix/Norms` behind `KyFanNorm.lean`; 38 `Inequalities` modules; 8 `Factorizations` modules;
most of `Subspaces`; 45 of 84 Krylov/Estimation modules (Ritz, PowerMethod, random start,
Hutchinson, SLQ); the restated Gaussian/Rademacher series files; the files moved to
`Sketching/Sampling/` and `RandomMatrix/Gaussian/Wishart/`. Expect further errors once the
first layer is fixed.

## First layer of failures (full build at handoff)

Update after the build below was taken: a Probability sub-stream that was still running
finished and its 18 files are committed on top (`SubGaussian`, `Concentration/Scalar`,
`ChiSquare`, `Concentration/QuadraticForms`; its own build of those modules passed, 3789 jobs).
That removes the `HansonWright.lean:65` failure from the log. `docs/f4/P.md` ends with an
"Addendum after the handoff commit" that corrects its "State at handoff" section and lists the
call sites outside Probability that its renames break, per owner.

Log: `docs/f4/build_at_handoff.log` (`lake build`, filtered to `✖` and `error:` lines).

Real errors, one per module:

| module | first error |
|---|---|
| `Matrix/Norms/KyFanNorm.lean:55` | `apply Finset.sum_subset` does not unify (sides reversed) |
| `Matrix/Perturbation/ConditionNumber.lean:37` | syntax: `open Classical in` between docstring and `def` |
| `Matrix/Perturbation/BauerFike.lean:114` | `simpa` needs `specNorm_eq_norm` |
| `Matrix/Spectral/MatrixPowerBounds.lean:119` | stray `unfold specNorm` |
| `Matrix/Spectral/SvdBlocks.lean:127` | sed artefact `bestRankFrobSq_eq_bestRankFrobSq` |
| `Matrix/Functions/PolynomialCalculus.lean:209` | rewrite with a renamed `specNorm_mul_…_of_hasOrthonormalCols` lemma |
| `Matrix/Subspaces/ProjectionGaps.lean:234` | unsolved goals (patched for :56, not rebuilt) |
| `Matrix/Subspaces/OrthogonalBlockCompletion.lean:27` | `hX.transpose` no longer exists |
| `Matrix/Subspaces/ObliqueProjectionBlocks.lean:44` | `exists_orthogonal_sum_completion` → `exists_unitary_sum_completion` |
| `Matrix/Subspaces/Stiefel.lean:135` | `simp` made no progress |
| `Krylov/Processes/ArnoldiProcess.lean:160` | `inner_eq_dotProduct_ofLp` → `inner_eq_star_dotProduct_ofLp` + `star_trivial` |
| `Probability/Concentration/Matrix/SubgaussianMgfCgf.lean:55` | autoparam of `cfc_comp'` cannot be synthesised (`hcont` is declared too late) |
| `Probability/Gaussian/Moments/SeriesKhintchine.lean:35` | `IsStandardGaussian`/`IsRademacher` deleted; disjunction not converted |
| `Probability/Concentration/Matrix/IntrinsicHermitianBernstein.lean:114` | `simp only [specNorm_eq_norm] at *` no progress |
| `Probability/Concentration/Matrix/MatrixChernoff.lean:245` | `master_bounds` was split; call sites not updated |
| `RandomMatrix/Gaussian/Basic/GaussianMatrix.lean:240` | `hasGaussianLaw_id_pi_gaussianReal` → `hasGaussianLaw_id_gaussianVector` |
| `RandomMatrix/Gaussian/Wishart/SoftMin/UnshiftedGramSoftMin.lean:321` | `sigmaMin` deleted (S1) |
| `LowRank/Structural/RangeFinder.lean:154` | `IsBestRankApprox` → `IsBestFrobRankApprox A k Y` |
| `Sketching/Sparse/CountSketchMoments.lean:49` | `integrable_quadForm_sq_pi_rademacherMeasure` renamed (see `F4-P.json`) |

Imports of modules that wave 1 deleted or merged (the importing file still exists):
`Matrix/Spectral/SigmaMinTransport` (← `Subspaces/PrincipalAngleBridges`),
`Matrix/Factorizations/{CholeskyStep,ComplexCholeskyPivot}` (← `LowRank/Cholesky/*`),
`Matrix/Norms/ComplexFrobeniusTrace` (← `Subspaces/ComplexVolumeProjectorTrace`, `ComplexGramColumnDeterminant`),
`Matrix/Functions/ComplexDiagonalFilter` (← `Subspaces/ComplexCSDecomposition`, `ComplexObliqueSpectrum`),
`Matrix/Basic/ComplexFullRowInverse`, `Matrix/Inequalities/PlaneRotation` (← `RandomMatrix/…/InverseMoments/OffDiagonal`),
`Probability/Rademacher/RademacherCube` (← `Sketching/Structured/SRHTFlattening`).
Replacement names are in the rename tables.

## Not started

- **Subspaces (M2):** the 15 `Complex*` twins are still present (D5); `principalAngles` over 𝕜
  (D3); `tanThetaMax`/`sinThetaMax` hypotheses (S3). Merge plans are in `docs/f4/M2-S1.md`, `M2-S2.md`.
- **M1:** Schatten unification and `nuclearNorm` abbrev (N3); Frobenius Mirsky over 𝕜;
  `eigenspaceProjector` over 𝕜; Hessenberg predicates over `[LinearOrder n]`; `rectDiag` only;
  52 signatures still spell a vector norm with `⬝ᵥ` (N2).
- **P:** P1 (Tropp chain over 𝕜 or real corollaries; still `Matrix (Fin d) (Fin d) ℂ` with
  `[NeZero d]`), P6 (PSD hypotheses), the `gaussianVector` ↔ `stdGaussian`/`gaussianMatrix`
  bridges, remaining bundles.
- **A1:** `chebyshevAnalyticCoeff` from `f : ℝ → ℝ`; the CG and Lanczos realisation scaffolds;
  top Ritz value still an index with a maximality hypothesis.
- **All of wave 2:** Sketching (F3 endpoint shape, SRHT, leverage sampling), LowRank (headline
  names, "expected" quantities as integrals, twins, tails), `Solvers/` → `RandomizedSolvers/`,
  RandomMatrix (tails, `gaussianVector` consumers, receiving moved files), and owner I (Books
  re-status, atlas prose, `(partial)` definitions, live-doc sync, ForMathlib namespaces,
  history folder, atlas areas, CI lints, port manifest regeneration).

## Corrections to the brief found during the round

- `hA.conjTranspose_mul_mul_same Q` is not a Mathlib lemma for `IsHermitian`; M1 used
  `Matrix.isHermitian_conjTranspose_mul_mul Q hA`.
- The noncommutative Khintchine `(2p-1)^p` bound does not follow from sub-Gaussian MGF plus unit
  variance; there the Gaussian-or-Rademacher disjunction should become two `HasLaw` corollaries
  rather than P4's hypothesis.
- The A11 filter lemma went to `Chebyshev/EvenChebyshevFilter.lean`, not `Growth.lean` (import cycle).
- `check_norms.py` has false positives on `‖F z‖` (function values) and entry norms.

## Lint counts at handoff

`check_norms.py`: 226 hits (450 before the round; Matrix 117, LowRank 24, Sketching 22,
RandomMatrix 21, Polynomial 21, Probability 10, Krylov 6, Estimation 5).
`check_docstrings.py`: 1101 hits (2211 before; LowRank 311, Matrix 240, RandomMatrix 194,
Sketching 148, Probability 126, ForMathlib 76, Solvers 6).

## How to continue

Either fix forward from this commit, layer by layer (`lake build`, fix the first layer above,
repeat; the atlas and index are stale until the build is green, then run
`lake env lean scripts/Audit.lean`, `lake env lean scripts/ExtractDecls.lean`,
`python3 scripts/sync_atlas.py`, `check_atlas.py`, `check_names.py`, `check_layers.py`,
`coverage.py`, `check_norms.py`, `check_docstrings.py`), or restart wave 1 from `75cf87d` and use
this commit as reference for the restated statements. Run `python3 scripts/reorg.py --gen-aggregators`
after adding, moving or deleting files. On this machine (31 GB) more than about four
concurrent Lean-loading processes exhaust memory, and concurrent `lake build`s cause spurious
"object file does not exist" errors.
