# F4: the consistency round (2026-10-13)

**Authority.** Tyler, after reading `docs/review/STATE_2026-10-13.md`: "let's do this for the
norms. It should be consistent and specified in the specs. And address all the other issues
also. Condition number should be the standard ‖A‖‖A⁻¹‖ definition with infinity or undefined for
non-invertible. This condition number can be renamed to something else since it comes up some."
This supersedes the freeze of `docs/FOUNDATIONS_BRIEF.md` §4 for the items below. Everything else
in that brief (one spelling, no leaf generalisation beyond what an item asks, the check list per
PR) still holds. `docs/STANDARDS.md` §3 is the spec; this file is the work list. Where the two
disagree, STANDARDS wins and this file is wrong.

Branch `nlalib-f4`, stacked on `nlalib-f2` (which is stacked on `nlalib-scaffold`). Item numbers
(M1…, A1…, P1…, I1…, C.n) refer to `docs/review/oddities_*.md` and `STATE_2026-10-13.md` §C.

## 0. Rules for agents

Same as `docs/DEDUP_ROUND_BRIEF.md` §0, in short:
- Exclusive file ownership (§3). Never edit a file you do not own; if you need an upstream change,
  write it in your report as a request and work around it.
- One Lean process at a time per agent. Build only your own modules:
  `lake build NLAlib.Matrix.Norms.Core …` (never bare `lake build`; never `import Mathlib`). Before
  building, wait until no other `lake build` is touching your upstream (check `pgrep -af "lake build"`);
  a spurious "olean not found" means another build was running: rerun.
- Renames are direct (STANDARDS §1, pre-`v0.1`): no deprecated aliases. Update every call site you
  own; call sites you do not own go in your rename table and report, and the owner applies them
  (downstream owners: read every upstream rename table before building).
  Rename table: `docs/renames/2026-10-F4-<agent>.json` (`"old": "new"`, or `"old": "<recipe>"`).
- Atlas tags travel with the statement. When you split a bundle, tag every component theorem
  and delete the bundle. When you delete a duplicate, the surviving declaration carries the tag.
  A definition is never tagged `(partial)`.
- Proofs: port every proof. If a restated theorem resists, leave a `SCAFFOLD: <id>` with a proof
  sketch (ALGORITHM_CONVENTIONS / STANDARDS §4) and list it in the report. Do not weaken a
  statement to make a proof go through.
- Docstrings: every declaration you touch loses provenance noise (§2 I-docs) and gets a one-line
  statement of what it says, with a published source.
- Report: `docs/f4/<agent>.md` (what changed, renames, scaffolds, requests to other owners,
  items you could not do and why). Reply with the report path and the item list.

## 1. Decisions

### N. Norms (STATE C.1 #2, M1, A §3; STANDARDS §3 "Norms")

- **N1** Matrix norms in public statements are the named functions `specNorm`, `frobNorm`,
  `frobSq`, `nuclearNorm`, `schattenNorm`, `kyFanNorm`. The notation `‖A‖` applied to a matrix is
  allowed in statements only in `Matrix/Functions/`, `Matrix/OperatorTheory/` (C*-algebra and
  CFC files, under a file-level `open scoped Matrix.Norms.L2Operator`), in the bridge lemmas
  `specNorm_eq_norm` / `frobNorm_eq_norm`, and in `ForMathlib/`. Everywhere else a file has no
  file-level `open scoped Matrix.Norms.*`; a proof that needs Mathlib's normed API writes
  `open scoped Matrix.Norms.L2Operator in` before that one declaration and rewrites with the
  bridge. `scripts/check_norms.py` (owner I) enforces the file-level rule and flags `‖` in
  signatures of non-exempt files.
- **N2** The vector 2-norm is `‖WithLp.toLp 2 x‖` (𝕜-generic; Mathlib's `EuclideanSpace`
  API). Squared: `‖WithLp.toLp 2 x‖ ^ 2`; unit vectors: `‖WithLp.toLp 2 x‖ = 1`. The spellings
  `Real.sqrt (x ⬝ᵥ x)`, `{x // x ⬝ᵥ x = 1}` and `x ⬝ᵥ x` *as a norm* disappear from statements
  (`x ⬝ᵥ y` as a bilinear pairing is fine). Bridges: `norm_toLp_sq_eq_re_star_dotProduct` (𝕜),
  `norm_toLp_sq_eq_dotProduct_self` (ℝ) in `Matrix/Norms/Core.lean` (owner M1 adds the second).
- **N3** One Schatten spelling: `schattenNorm (A) (p : ℝ≥0∞) : ℝ` (delete `schattenNormExtended`,
  `schattenSeminorm`, `schattenInvariantNorm` as definitions; keep their content as lemmas).
  `nuclearNorm A` is `schattenNorm A 1` (abbrev). `kyFanNorm A k` and `eigenvaluePrefix` are
  defined through `sumLargest` of `singularValues` / `eigenvalues₀`. `OrthogonallyInvariantNorm`
  becomes `UnitarilyInvariantNorm` over 𝕜 (atlas id `unitarily-invariant-norm-def`), its
  `transpose` lemma moves into `Norms/InvariantNorm.lean`.
- **N4 Condition number.** `conditionNumber (A : Matrix n n 𝕜) : ℝ≥0∞ :=
  if IsUnit A then ENNReal.ofReal (specNorm A * specNorm A⁻¹) else ⊤`, in
  `Matrix/Perturbation/ConditionNumber.lean`, atlas `condition-number-def`. API:
  `conditionNumber_of_isUnit`, `conditionNumber_eq_top_iff`, `one_le_conditionNumber` (Nonempty n),
  `conditionNumber_eq_singularValues_ratio (hA : IsUnit A)`, `conditionNumber_eq_eigenvalues₀_ratio`
  (PosDef), `conditionNumber_conjTranspose`, `conditionNumber_inv`. Perturbation bounds take
  `(hA : IsUnit A)` and are stated with `(conditionNumber A).toReal`. The present pseudoinverse
  quantity is renamed `moorePenroseConditionNumber (A : Matrix m n 𝕜) : ℝ` (σ₁/σ_r; 0 at A = 0,
  documented), keeps its theorems, and is listed in the same atlas entry as a second definition.

### S. Spectral quantities (C.1 #3–5)

- **S1** `sigmaMin` is deleted. The smallest singular value of `A : Matrix m n 𝕜` with
  `card n ≤ card m` is `singularValues A (Fintype.card n - 1)`; the variational form is the lemma
  `singularValues_last_eq_iInf` (`= ⨅ x : {x // ‖WithLp.toLp 2 x‖ = 1}, ‖WithLp.toLp 2 (A *ᵥ x)‖`),
  proved from `IsHermitian.eigenvalues₀_last_eq_iInf` for `Aᴴ * A`. Theorems about `sigmaMin` are
  restated with `singularValues`. `eigenvalues₀_last_eq_iInf` is stated over 𝕜.
- **S2** `lambdaMax`/`lambdaMin (A : Matrix n n 𝕜) : ℝ := sSup/sInf (spectrum ℝ A)` over 𝕜
  (moved to `Matrix/Spectral/Core.lean`), with `lambdaMax_eq_eigenvalues₀_zero (hA : A.IsHermitian)`
  and `lambdaMin_eq_eigenvalues₀_last`. Junk for non-Hermitian `A` is documented. The `lamMin_*`
  theorem names are rewritten.
- **S3** Definitions stay total (Mathlib convention); the *tagged theorems* carry the hypothesis
  that makes them true for a reason: `IsUnit (A * Aᴴ)` for the inverse-Gram norm identities,
  `IsUnit (Qᴴ * X)` for the `tanThetaMax` results, `DifferentiableAt ℝ f x` for `mapAbsCondition`,
  `IsUnit A` for `conditionNumber`. The junk value is stated in each docstring.

### D. Duplicates and names in the Matrix layer (C.1 #7–8, #10; M §1–§4)

- **D1** `residual Q A` → `projResidual Q A` (not `b − Ax`; no Mathlib collision).
  `HasOrthonormalCols` and `projResidual` move to `Matrix/Basic/Orthonormal.lean`, upstream of
  `Norms`; every raw `Pᴴ * P = 1` / `Pᵀ * P = 1` hypothesis becomes `HasOrthonormalCols P`.
  (Coordinator does the move and the rename in wave 0.)
- **D2** Rectangular diagonal: `rectDiag` only. Schur complements: `generalizedSchurComplement`
  (𝕜, `Bᴴ`), `pivotSchur`, `eliminationStep` (was `choleskyStep`); the ℂ copy is deleted. Leading
  minors: `leadingSubmatrix A k`, `leadingMinor := det ∘ leadingSubmatrix`, both in `Basic`;
  `trailingMinor`, `principalMinor A S` as lemmas or thin defs on top. Prefix sums: `sumLargest`.
  Rotations: `planeRotation u v c s` basis-free; `givens i j c s` is its coordinate case in
  Golub–Van Loan orientation (`G(i,j,θ)ᵀ A` zeroes an entry) with the sign convention documented.
  Eigenprojectors: `eigenspaceProjector hA ℓ` and `eigenvectorProjector hA i`, over 𝕜. The range
  projector: `rangeProjector B` over 𝕜 in `Subspaces/Projections.lean`
  (`rangeProjector_eq_mul_moorePenroseInverse`); `complexColumnProjector` deleted.
- **D3** `IsBestRankApprox` → `IsBestFrobRankApprox A k Y`; argument order `A` first for
  `truncatedSVD A k`, `singularValueTailSq A k`, `bestRankFrobSq A k`, `IsBestFrobRankApprox`.
  `singularValueTailSq` and `bestRankFrobSq` are one definition (`bestRankFrobSq`).
  `principalAnglesFintype` → `principalAngles` over 𝕜 without the reindex. `IsUpperHessenberg`,
  `IsTridiagonal` over `[LinearOrder n] [Zero α]`, retagged `hessenberg-def`; `IsHessenbergForm`
  joins them. `OperatorConvexOn` loses `NeZero`. `Inequalities/Mirsky.lean` →
  `SingularValueMajorization.lean`, retagged. `IsAffineMinimiser` → `IsAffineMinimizer`.
- **D4** Statements: Weyl and the compression lemmas use `(hA.add hB).eigenvalues₀` and
  `(hA.conjTranspose_mul_mul_same Q).eigenvalues₀` instead of extra Hermitian hypotheses;
  `(B - A).PosSemidef` → `A ≤ B`; `IsSymm` → `IsHermitian` in every real statement; existence
  theorems for `[LinearOrder n]` predicates are stated for `[LinearOrder n]` (`LU`, `Cholesky`,
  `QR`, polar); every `_fintype`/`_fin`/`_all_dims` twin collapses to one `Fintype` statement
  named for its content; the `equivFin` transports (`WedinFiniteIndex`, `RankNorm`,
  `SquareSingularBasis`) are restated on `m n` or derived from `IsSVD` and dropped.
- **D5** The `Complex*` vocabulary twins in Matrix leaves (15 in `Subspaces/`, `Basic/{ComplexFullRowInverse,
  ComplexPosSemidefTrace}`, `Norms/ComplexFrobeniusTrace`, `Factorizations/ComplexCholeskyPivot`,
  `Functions/ComplexDiagonalFilter`, `Inequalities/ComplexDiagonalMajorization`) are merged into
  the 𝕜 statement, F1-style; `Spectral/ComplexQZ.lean` stays (no real QZ).
- **D6** Placement: `Matrix/Calculus/{GramSoftMin*,InversePower*,UnshiftedGramSoftMin,
  GramCutoffCalculus,GramTrace}` and `Structured/GramSoftMinMeasurable` →
  `RandomMatrix/Gaussian/Wishart/SoftMin/`; `Structured/{Measurable,SpectralMeasurable}` →
  `Matrix/Measurability/`; `Perturbation/MapConditioning` → `ForMathlib/Analysis/Calculus/Conditioning.lean`;
  `realMatrixComplexification` and its API → `Matrix/Spectral/Complexification.lean`. Subdirectories
  of `Matrix/` remain topics, not layers (documented in `Matrix/README` paragraph of STANDARDS §2).

### A. Algorithms (C.2 #11–15, #17–19; A1–A10, A §1–§4)

- **A1 (= F3)** Every sketch-distribution theorem concludes
  `μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U ε} ≤ δ` (`docs/SKETCH_INTERFACE.md`), with
  `IsSubspaceEmbedding` over 𝕜 (`U : Matrix m d 𝕜`). Gaussian, CountSketch, sparse (endpoint
  wrappers only; the quarry stays), SRHT (via a bridging lemma from the Gram event), leverage
  sampling (restated with `leverageScore`, `IsSubspaceEmbedding`, `selectionMatrix`). Needless
  `HasOrthonormalCols U` hypotheses in relabelling lemmas go.
- **A2** Headline atlas ids on the unconditional theorems, with Mathlib-style names
  (`integral_frobSq_projResidual_le_bestRankFrobSq`, …); `rsvd_main`, `rsvd_truncated_main`,
  `gn_main`, `gn_main_of_completion`, `completion_reduction`, `error_decomp`, `Assembly.*` become
  untagged lowerCamel helpers (private where nothing else uses them; `namespace Assembly` dissolved).
  One parametrisation across LowRank: oversampled rank `t` with `k + 2 ≤ t` (documented as
  HMT's `k + p`). The Nyström trace bound is stated for `A.PosSemidef` with
  `spectralTraceTail`. `truncatedRsvdOutput`, `gaussianRangeFrame` stay internal; the user-facing
  relation is `IsRangeFinder Q Y := HasOrthonormalCols Q ∧ range Y ≤ range Q`.
- **A3** "Expected" quantities are integrals: `Kaczmarz.expErr`, `SketchProject.expErr`,
  `choleskyExpectedTrace`, `volumeSamplingExpectedFrobSq` are replaced by the law (a `PMF` on
  paths / a `Measure`) and the finite sum becomes a lemma. The ℝ and ℂ volume-sampling twins
  become one 𝕜 statement with the `Measure` shape.
- **A4** `complexBlockKrylovSpace`, `complexSubspaceIterate` deleted (the field-generic ones
  exist). Principal-angle tangents: `tanThetaMax` only (vector case `k = 1`); the bridge
  `sq_tanThetaMax_replicateCol_eq_tanSqAngle` is proved and `tanSqAngle`, `subspaceTangent`,
  `vectorTangentToFrame`, `complex*` are deleted; one subspace-iteration convergence family under
  `subspace-iteration-convergence`.
- **A5** Ritz, power, random-start statements take an eigenvector `u` (`A *ᵥ u = λ • u`,
  `‖WithLp.toLp 2 u‖ = 1`) instead of `hA.eigenvectorBasis i₁`; the top eigenvalue is
  `hA.eigenvalues₀ 0`; `(hA.conjTranspose_mul_mul_same Q)` is built inside the statement.
- **A6** Gauss exactness: `p.degree < 2 * q` only; `mem_krylovSpace_iff` is the hypothesis-free
  statement. Random-start Lanczos is indexed by matvecs (`K_{q+1}`, bound `/ q ^ 2`, `1 ≤ q`), one
  `Fintype` statement, no `Fin (n+1)` / `_all_dims` copies. `exists_eigenvalues_…_ge` uses `K_{q+1}`
  and `^ q`. Docstrings of `singularValues`-indexed bounds state the HMT translation (σ_{k+1}).
- **A7** Krylov processes: `LanczosDecomp` hypotheses are `IsHermitian`; names say what they are
  (`arnoldiProcess*` for the ℕ-indexed process, `ArnoldiDecomp.*` for the predicate, `*Recurrence`
  for recursions), with a table in `Krylov/Processes/Arnoldi.lean`'s module docstring; one
  definition of β in both docstrings; `CGSucceeds`/`LanczosSucceeds` added (or
  ALGORITHM_CONVENTIONS §1.3 amended with the reason they are unnecessary); `lanczosRitzValue` is
  the sup of Rayleigh quotients over `K_q` (countable form as a lemma); `chebyshevAnalyticCoeff`
  is defined from `f` by the real integral (contour formula as a lemma); the sawtooth/Jackson
  helpers are `private` or get content names; `krylovFunApprox A f b Q` argument order shared
  with `slqEstimate`.
- **A8** Estimators take `Matrix n κ ℝ` test matrices with implicit `κ`; `SketchProject` uses
  `S * A` orientation; random signs are ℝ-valued with law `rademacherMeasure` (`srhtLaw` on
  `(Fin n → ℝ) × …`; `Bool` signs and the quarry's `Sign` stay only inside the frozen Sparse proof).
- **A9** Optimal-error tails: `bestRankFrobSq A k` (Frobenius) and `spectralTraceTail hA k`
  (PSD trace); `complexGramTail`, inline sums and `filterTailMaxAbs` go.
- **A10** Constants are not improved in this round; each docstring states the source constant
  next to the proved one. JL stays at `N ^ 2` ordered pairs, documented. GMRES's diagonalisable
  bound is documented as the real-diagonalisable case.
- **A11** Placement: top-level `Solvers/` → `RandomizedSolvers/` (layer 5); the Rayleigh/transpose
  helpers in `Krylov/Quadrature/GaussQuadrature` → `Matrix/Basic/QuadForm.lean`; AMM lives in
  `Sketching/Properties/ApproxMatrixMultiplication` only; `Polynomial/Chebyshev/LanczosFilterMean`
  → `Chebyshev/Growth` with the filter-mean lemma next to its consumer. `Krylov/Spectral` keeps
  the QR algorithm, power method and inverse iteration (module docstring says so).
- **A12** snake_case paper names → Mathlib naming (`jl_lemma` → `measure_jl_failure_le`,
  `hutchinson_of_rademacher` split, `complex_polynomial_filter_residual_bounds` split into
  spectral and Frobenius theorems, …).

### P. Probability and random matrices (C.3 P1–P10)

- **P1** The Tropp vocabulary (`lambdaMax`, `lambdaMin`, `matrixExp`, `matrixLog`, `traceExp`,
  `intrinsicDimension`, `rectSecondMoment`, `cumulantSum`, matrix MGF/CGF) and the headline
  theorems (matrix Chernoff, Bernstein, Freedman, Gaussian/Rademacher series, Lieb,
  Golden–Thompson) are stated over `[RCLike 𝕜]` and `[Fintype n]` where the proof goes through the
  CFC generically; where it does not, the ℂ theorem stays and a real corollary via
  `realMatrixComplexification` is added, so that every headline applies to
  `X : Ω → Matrix n n ℝ`. `[NeZero d]` becomes `[Nonempty n]` where needed.
- **P2** Tails: `μ.real s ≤ c` everywhere (Probability, RandomMatrix, Sketching, LowRank,
  Estimation). Success forms `1 − δ ≤ …` become failure forms. No `ENNReal.ofReal` tails, no
  `(μ s).toReal`.
- **P3** Laws: `HasLaw` only. `gaussianVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1` and `rademacherVector n := Measure.pi fun _ => rademacherMeasure`
  are the names for the product measures (`Probability/Gaussian/Basic`, `Probability/Rademacher/Core`),
  with `gaussianMatrix_eq_map_curry`-style bridges to `gaussianMatrix` and to
  `stdGaussian (EuclideanSpace ℝ n)`. The abbrevs `IsStandardGaussian μ g` and `IsRademacher μ r`
  are deleted; statements say `HasLaw g (gaussianReal 0 1) μ` / `HasLaw r rademacherMeasure μ`
  (Mathlib order). Entrywise `IsStandardGaussian … ∧ iIndepFun` hypotheses on a `n → κ → ℝ` or
  `Matrix` become `HasLaw G (gaussianMatrix n κ) μ`. `rademacherCubePMF` goes. Redundant
  `AEMeasurable`/`Measurable`/`[IsProbabilityMeasure μ]` binders next to a law are dropped.
- **P4** The disjunctive Gaussian-or-Rademacher hypothesis becomes `∀ k, HasSubgaussianMGF (g k) 1 μ`
  plus `∀ k, ∫ (g k)^2 = 1`, with the two laws as corollaries.
- **P5** Every `let`–`∧` bundle splits into theorems (each tagged); `∃ C` becomes the explicit
  constant. The duplicate noncommutative Khintchine and the duplicate Hanson–Wright
  (`UniversalBound.lean`) are deleted; `_fin` twins (ChiSquare, McDiarmid) deleted.
- **P6** PSD hypotheses are `PosSemidef` / Loewner `≤`, never `0 ≤ lambdaMin ∧ …`;
  `intrinsicDimension` stays total, theorems take `M ≠ 0` only where the source does.
- **P7** Placement: `ForMathlib/{UniformSampling*,Data/ExactRowSubset}` → `Sketching/Sampling/`;
  the five weak-density files → `RandomMatrix/Gaussian/Wishart/`; `orthogonalGroupCompactSpace`
  → `ForMathlib/Topology/`.

### I. Atlas, docs, infrastructure (C.4 #20–27; I1–I27)

- **I1** Books: every item whose atlas ids are all proved is re-statused (`nlalib` if the entry's
  statement covers the item, else `partial` with a note); the `hj13` edition note is fixed.
- **I2** Atlas prose: every entry whose Lean is over `RCLike`/`Fintype` says so (D13 list plus
  the 14 found by the review; usage strings teach `HasOrthonormalCols`, `ᴴ`, `HasLaw`);
  `check_atlas.py` warns on `\mathbb R^{` in an entry whose formalizations are `RCLike`.
- **I3** No definition is `(partial)`; `check_atlas.py` warns on proved → candidate edges;
  candidates with Lean content get their status.
- **I4** All 37 deprecated aliases deleted (direct renames); `docs/renames/2026-10-F1.json` is
  the record.
- **I5** Live docs synced to the code: STANDARDS (§2 tree without `REORG_PLAN`; §3 as amended
  by this round), CONTRIBUTING (no `chN_`, no `NLAlib/Gaussian/`), README (layers incl. Krylov,
  scripts; last section moved to `docs/history/`), `llms.txt` (repo URL, vocabulary),
  `check_layers.py` docstring, `docs/coverage/README.md`, `atlas/README.md`,
  `docs/FOUNDATIONS_BRIEF.md` §1 (sorted-index `rectDiag`, `ComplexQZ` exemption; one-paragraph
  note that this round was authorised on 2026-10-13).
- **I6** ForMathlib: upstreamable facts in Mathlib namespaces (`_root_.ConcaveOn.…`,
  `_root_.ProbabilityTheory.iIndepFun.…`), file names mirroring Mathlib paths; NLAlib-specific
  helpers moved to their consumers (P7, D6); `NormSumSq` deleted (Mathlib lemma), `BlockCauchySchwarz`
  deleted (no importer), `MomentInterpolation`'s atlas tag moved to `mathlib_prereqs`; no atlas
  tags in ForMathlib (tags move to the consumer theorem).
- **I7** Docstring noise: "manuscript `sa:…`/`rt:…`/`sh:…`" keys, "operator re-derivation",
  commit hashes, "Audit G0 …", "(label to verify)" (resolved or deleted), "actual"/"genuine",
  "Prove2me" are removed from every docstring (each owner for their files; `scripts/check_docstrings.py`
  flags them). Names containing `Manuscript` are renamed.
- **I8** Hygiene: `scripts/__pycache__` removed and ignored; `AuditNewProofs.lean`,
  `AuditGaussianInverse.lean` removed from CI and deleted; `set_option autoImplicit false` and
  `open scoped BigOperators` lines deleted; `respectTransparency false` removed where the file
  still builds (report the rest); MIT headers on the nine derived files; historical docs moved to
  `docs/history/` with a one-line index; `docs/ports/` merged into `docs/port/`; atlas areas
  renamed to the directory names, `schema.json` `$id` fixed; `reorg.py` `TREE` matches the tree.
- **I9** The port manifest is regenerated at the end of the round (coordinator).

## 2. Not in this round

The Sparse quarry (`Sketching/Sparse/**`) beyond its endpoint wrappers (A1) and MIT headers;
constant improvements (A10); the Krylov layer going complex; enforcing a layer order inside
`Matrix/`.

## 3. Ownership and waves

Wave 0 (coordinator): this brief, STANDARDS §3, `Matrix/Basic/Orthonormal.lean` (D1 move,
`residual` → `projResidual`), `conditionNumber` → `moorePenroseConditionNumber` (mechanical, N4's
new definition is M1's), alias deletion (I4), `__pycache__`/`autoImplicit`/`BigOperators` (I8
mechanical part), full build.

Wave 1 (four agents, in parallel):
- **M1** `Matrix/{Norms,Perturbation,Spectral,Calculus,Structured,Measurability}`: N1–N4, S1–S3,
  D4 (Weyl/compression, Mirsky), D6 moves, D5 for `Norms/ComplexFrobeniusTrace`, I7 in its files.
- **M2** `Matrix/{Basic,Subspaces,Factorizations,Inequalities,Functions,OperatorTheory}`:
  N1/N2 in its files, D2, D3, D4 (PosSemidef, IsSymm, Fin existence, `_fintype` twins), D5,
  I7 in its files.
- **P** `Probability/**`, `ForMathlib/{Probability,MeasureTheory,Analysis/Matrix}`: P1–P6, N1/N2
  in its files, I7.
- **A1** `Krylov/**`, `Polynomial/**`, `Estimation/**`: A5–A7, A8 (estimators), A11 (helpers out
  of GaussQuadrature: request to M2), A12, N1/N2, I7.

Wave 2 (after wave 1 builds):
- **A2** `Sketching/**` (except the quarry's interior), `LowRank/**`, `RandomizedSolvers/**`:
  A1–A4, A8 (sketch orientation, signs), A9, A10 docstrings, A11, A12, P2 in its files, N1/N2, I7.
- **R** `RandomMatrix/**`: P2, P3 (`gaussianVector` consumers), D6/P7 receiving moves, N1/N2, I7.
- **I** `atlas/`, `docs/`, `scripts/`, `.github/`, `README.md`, `CONTRIBUTING.md`: I1–I8,
  `check_norms.py`, `check_docstrings.py`.

Coordinator after each wave: full build, `Audit.lean`, `ExtractDecls`, `sync_atlas`, `check_*`,
`coverage.py`; commit per wave; manifest regeneration and the PR at the end.
