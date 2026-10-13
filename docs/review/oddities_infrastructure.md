# Review: infrastructure, ForMathlib, atlas, docs (what a newcomer would find odd)

Read-only review, 2026-10-13, branch `nlalib-f2` (HEAD `a45c47a`, F2a uncommitted: 10 modified Lean
files plus `ForMathlib/MeasureTheory/Matrix.lean`, `docs/rclike/F2a.md`, `docs/renames/2026-10-F2.json`).
Nothing was built; numbers come from `atlas/*.json` (index regenerated 14:39, atlas 13:17),
`docs/port/manifest.json`, `docs/coverage/*.json` and greps over `NLAlib/`. Matrix, Krylov and randomized
theorem content is out of scope here (see `docs/review/oddities_matrix.md`).

## 1. Map of the repository as it stands

### 1.1 Tree (Lean files incl. aggregators / lines)

```
NLAlib.lean                 root aggregator (10 imports)
NLAlib/  1092 .lean = 989 content + 103 generated aggregators, 157 914 lines
  ForMathlib/    107 / 7 843   layer -1  Algebra 7 · Analysis 44 (30 content files beside 5 subdirs)
                                         · MeasureTheory 18 · Probability 13 · LinearAlgebra 11 · Data 2
                                         · Combinatorics 1 · Logic 1 · Order 1
  Matrix/        505 / 62 475  layer 0   Spectral 128 · Inequalities 80 · Perturbation 64 · Subspaces 55
                                         · Factorizations 37 · Norms 34 · Basic 31 · Functions 20
                                         · OperatorTheory 19 · Structured 15 · Calculus 11
  Polynomial/     32 / 4 866   layer 0   BestApproximation 12 · Chebyshev 7 · FunctionApproximation 7 · Interpolation 2
  Probability/   132 / 22 761  layer 1   Concentration 80 · Gaussian 35 · SubGaussian 5 · Rademacher 3 · ChiSquare 2 · Sampling 1
  Krylov/         37 / 7 843   layer 1   Quadrature 7 · Solvers 7 · Spectral 6 · Processes 5 · Spaces 5 · MatrixFunctions 1
  RandomMatrix/   54 / 10 901  layer 2   Gaussian 47 (6 subdirs) · Haar 2 · SubGaussian 2
  Sketching/     149 / 30 696  layer 3   Sparse 124 (frozen quarry, F3) · Properties 10 · Structured 5 · Sampling 4 · Gaussian 1
  LowRank/        41 / 7 051   layer 4   Cholesky 8 · Nystrom 6 · Sampling 6 · RangeFinding 5 · RandomizedSVD 4 · PolynomialMethods 3 · Structural 2
  Estimation/     18 / 2 266   layer 4   Quadrature 6 · Spectral 3 · Trace 2 · Diagonal 1 · QuadraticForms 1
  Solvers/         7 / 1 114   layer 5   Kaczmarz 4 · SketchAndProject 1
atlas/    atlas.json (1.4 MB), declarations.json (6.2 MB, generated), external.json (generated),
          import_usage.json (generated 2026-10-12, pre-F1), schema.json, viewer.template.html,
          viewer.html (gitignored build), vendor/katex.inline.css, README.md, TARGETING.md
site/     built copy of the atlas + index.html (8.5 MB) + llms.txt (gitignored, deployed by pages.yml)
scripts/  15 files (below), plus a committed scripts/__pycache__/reorg.cpython-313.pyc
docs/     29 top-level files + 11 subdirectories (audit 4, coverage 11, dedup 15, port 3+8 tools,
          ports 1, rclike 29, renames 30, reorg 3+11, targets 6, review)
.github/  ci.yml (build, Audit, two one-off audits, ExtractDecls freshness, layers, names, atlas, site), pages.yml
```

### 1.2 Layer rule

A module imports only its own layer and lower (`scripts/check_layers.py`, `LAYER` dict):
-1 ForMathlib · 0 Matrix, Polynomial · 1 Probability, Krylov · 2 RandomMatrix · 3 Sketching ·
4 LowRank, Estimation · 5 Solvers. Same-layer sideways imports are allowed by the script but none
exist today (Krylov↔Probability, LowRank↔Estimation, Matrix↔Polynomial all 0). Every `<Dir>.lean`
is a generated aggregator (`scripts/reorg.py --gen-aggregators`); content lives in leaf directories,
except `ForMathlib/Analysis` (30), `ForMathlib/LinearAlgebra` (6), `Sketching/Sparse` (11),
`Sketching/Sparse/Bands` (9), which hold content files beside subdirectories.

### 1.3 Scripts

| script | does | CI |
|---|---|---|
| `Audit.lean` | axioms of every `NLAlib.*` theorem; writes `.lake/sorries.txt` | yes |
| `AuditGaussianInverse.lean`, `AuditNewProofs.lean` | one-off "these named proofs are sorry-free" checks from two codex PRs (`maxHeartbeats 0`) | yes |
| `ExtractDecls.lean` | `atlas/declarations.json` (+ `external.json`): name, kind, module, line, signature, doc, sorry, `atlas:`/`SCAFFOLD:` tags, `uses` | freshness diff |
| `sync_atlas.py` | rewrites each result's nlalib `formalizations`, `status`, `uses_defs` from the tags | via check_atlas |
| `check_atlas.py` | schema, referential integrity, decl existence, sorry cross-check, `sync --check` | yes |
| `check_layers.py` | import-layer lint | yes |
| `check_names.py` (+ `name_exemptions.txt`) | weak naming lint (no single CamelCase theorem, source prefixes, Basic.lean rule) | yes |
| `coverage.py` | validates `docs/coverage/<book>.json`, writes `<book>.md` | no |
| `build_viewer.py` / `build_site.py` | atlas + index + coverage into one HTML page | site build |
| `reorg.py` | mapping tables → `git mv`, import rewrite, aggregators | no |
| `ImportUsage.lean` / `apply_imports.py` | minimal import suggestions → `atlas/import_usage.json` / apply | no |
| `docs/port/tools/*.py` | generated the port manifest (build, groups, overrides, writemd, …) | no |

### 1.4 Docs: live vs historical

Live (someone should keep these true): `README.md`, `AGENTS.md`, `CONTRIBUTING.md`,
`docs/FOUNDATIONS_BRIEF.md` (governs until the port; overrides STANDARDS), `docs/STANDARDS.md`,
`docs/llms.txt` (deployed to the site), `atlas/README.md`, `atlas/TARGETING.md`,
`docs/ALGORITHM_CONVENTIONS.md` and `docs/KRYLOV_DEFINITIONS.md` (cited by STANDARDS §2),
`docs/SKETCH_INTERFACE.md` (F3 deliverable), `docs/port/{MANIFEST.md,manifest.json}` (port work list),
`docs/coverage/*` (Books tab data), `docs/renames/*.json` (rename ledger), `docs/ports/sparse-fock-MIT.txt`
(licence of 110 files), `docs/rclike/DESIGN.md` + `F1b-alpha.md` (cited by STANDARDS for D1/E′).

Historical (agent briefs and reports; nothing reads them mechanically): `ROUND1/3/4/5/6/8/9_*`,
`ROUND8/9_FOLLOWUP`, `TARGETS_ROUND7_BRIEF`, `AUDIT_ASSUME_BRIEF`, `COVERAGE_BRIEF` (process note),
`DEDUP_BRIEF`, `DEDUP_ROUND_BRIEF`, `DEDUP_FOLLOWUP`, `REORG_PLAN`, `REORG_BRIEF`, `REORG_FOLLOWUP`
(67 KB), `SPARSE_INTEGRATION` (superseded by F3), `GOLDEN_THOMPSON`, `MATRIX_TOOLKIT_COMPLETION`,
`coverage-fixes.md` (three codex PR descriptions), `TroppMatrixConcentration.md` (original README of
the ported project), and the subdirectories `audit/`, `dedup/`, `targets/`, `reorg/`, `rclike/` (except
the two files above; `Proto.lean`, scan JSONs). FOUNDATIONS §4 defers archiving them to the port.

## 2. State numbers

| quantity | value |
|---|---|
| declaration records in `declarations.json` | 7 096; 6 660 after removing 328 line-0 auto-generated entries (`congr_simp` 165, `sizeOf_spec`, `eq_def`, `ctorIdx`, …) and `casesOn`/`recOn`/`noConfusion` |
| of which | 5 613 theorems, 901 defs, 57 instances, 37 inductives; 104 without a docstring |
| root (non-`NLAlib.`) declarations | 24: 18 `Matrix.IsHermitian.*`, 3 `Matrix.PosSemidef.*`, 1 `Matrix.PosDef.*` + 2 index artefacts; F2a adds `Matrix.instMeasurableSpace` & co. (not yet indexed) |
| sorry | 16 `sorry` lines in 11 files, all under 16 `SCAFFOLD:` declarations; 39 declarations depend on sorry (23 transitively) |
| atlas results | 354: 254 proved · 87 candidate · 12 scaffold · 1 assumed · 0 stated/planned |
| atlas kinds | 115 theorem · 109 bound · 48 definition · 43 identity · 23 lemma · 15 application · 1 algorithm |
| nlalib formalizations | 1 724 (856 proved, 829 proved-partial, 19 scaffold, 20 stated); 55 results list ≥ 10, max 42 (`principal-angles-def`) |
| sources / areas / libraries | 94 (5 unused) / 40 / 10 |
| deprecated aliases | 37, in 9 Matrix core files, all `since 2026-10-13` (F1); 13 in `Subspaces/Projections.lean` |
| `atlas:` tag lines / prose `Atlas:` mentions | 1 697 / 914 |
| port manifest (`docs/port/manifest.json`) | 1 003 entries: keep 357 · merge 432 · drop 68 · rebuild 146; ForMathlib 91: keep 29 · merge 62 · drop 0 |
| manifest drift | 16 entries for files F1 deleted (`Complex*`, `RealComplex*`, `FiniteIndexTransport`); 2 files missing (`ForMathlib/MeasureTheory/Matrix`, `…/Matrix/LiebJensen`, the latter excluded on purpose) |
| F2 remaining (acceptance greps) | `Matrix.of.symm` 163 hits, `_of_map_eq` 61 hits |
| file-level options | `respectTransparency false` 95 (81 in Matrix), `maxHeartbeats` 29 (up to 2 000 000), `maxRecDepth` 10, redundant `autoImplicit false` 242 (lakefile already sets it) |
| `open scoped` | `Matrix` 573, `Matrix.Norms.L2Operator` 361, `BigOperators` 179 (a no-op today), `MatrixOrder` 103, `ComplexOrder` 96, `Classical` 24 (no unscoped `open Classical`) |
| headers | 125 files carry a copyright header (110 MIT from the Sparse port, 12 Apache from other ports); the other ~860 content files have none |

## 3. Oddities, ranked

Ranked by how likely they are to mislead a reader or a tool. "Fix" is a recommendation; items marked
**port** fall under FOUNDATIONS §4 (defer to `NLA-lib/NLAlib`).

### A. The status a reader sees is wrong

1. **The Books tab says "candidate" for 147 Horn–Johnson statements that are proved.** In
   `docs/coverage/hj13.json`, 159 items have status `candidate`; for 147 of them every atlas id they
   point to is now `proved` (e.g. §0.4.2 → `rank-inequalities`, §0.8.1 → `cauchy-binet`; 12 point to
   `simultaneous-diagonalization`, 11 to `gershgorin-diagonal-dominance`). The matrix-toolkit rounds
   closed them but nobody re-statused the index, and `coverage.py` only checks that ids exist. The
   report header (`hj13.md`) still reads 39 ✓ / 159 ○. Trefethen and Gautschi have the inverse
   problem: 7 and 15 items marked `nlalib`/`partial` cite at least one atlas entry that is `candidate`.
   Fix: in `coverage.py`, derive or at least check item status against the atlas (`candidate` item
   whose ids are all proved → error), then re-status. Also: the `edition_note` of `hj13.json:3` is two
   part-notes concatenated ("chapters 0–3 only … this file indexes Chapters 4–8").
2. **One bridge lemma turns a 41-declaration definition entry into "scaffold".**
   `principal-angles-def` (42 formalizations, 41 proved) shows `scaffold` because
   `Krylov/Spectral/PowerMethod.lean:388` starts its docstring `SCAFFOLD: principal-angles-def` and ends
   `atlas: principal-angles-def (partial)`. `ExtractDecls.lean:47` pushes the SCAFFOLD id first, and
   `:55` (`!out.contains id`) then skips the line that would have marked it partial, so the `(partial)`
   is silently lost. Same mechanism makes `givens-rotation-def` (20 forms; `Givens.lean:355`) and
   `gram-schmidt` (22 forms) scaffolds. Five proved results then `depends_on` a "scaffold"
   (`davis-kahan-sin-theta`, `wedin-sin-theta`, `pseudoinverse-perturbation`,
   `subspace-iteration-convergence`, `cs-decomposition`). Fix: honour `(partial)` after a SCAFFOLD id
   (set `part` when any `atlas:` line marks the id partial); decide whether a SCAFFOLD bridge lemma
   should ever be the non-partial witness of a definition entry.
3. **Partial-only and definition entries stay `candidate` although Lean has them.** 12 candidates
   have only partial formalizations (`krylov-grade` is tagged `(partial)` on the definition
   `krylovGrade` itself; `gmres-def`, `fom-def`, `residual-polynomial`, `jacobi-matrix-identities`, …),
   and 17 proved results `depends_on` such candidates (`cg-finite-termination` → `krylov-grade`,
   `chebyshev-approx-analytic` → `bernstein-ellipse-def`, …). A proved result resting on a "candidate"
   reads as a contradiction. Fix: a definition is never partial (tag it plainly); add a
   `check_atlas` warning for proved→candidate edges.
4. **The axiom audit skips the `_root_` declarations STANDARDS mandates.** `Audit.lean:13,18` audits
   names with prefix `NLAlib` only, so Courant–Fischer/Weyl/interlacing (`Matrix.IsHermitian.*`, 18),
   `Matrix.PosSemidef.*`, and F2a's `Matrix.instMeasurableSpace`, `Measurable.matrix_mul` are never
   axiom-checked and never reach `.lake/sorries.txt`, so `check_atlas`'s sorry cross-check misses them.
   `ExtractDecls.isPublicName` (`:62`) was fixed to select by module; Audit was not. Fix: use the same
   module-based predicate in `Audit.lean`. (CI's step is also named "no sorry" while scaffolds are allowed.)
5. **35 proved results are proved only by a `*_properties` / `*_characterizations` bundle.**
   E.g. `davis-kahan-sin-theta` ← `davis_kahan_toolkit_properties` (`Perturbation/DavisKahanToolkit.lean:21`),
   `polar-decomposition`, `normal-matrices`, `cs-decomposition`, `gershgorin-diagonal-dominance`,
   `schur-triangularization`, `diagonalizable-def`, … (full list: results whose every non-partial
   nlalib formalization matches `_properties$|characterizations$`). The bundle is a conjunction of up to
   a dozen clauses; its signature is a pasted pretty-print with `_inst_1`, `u_1`, `have S := …` binders,
   unusable with `rw`/`apply`, and `check_names.py` lets such names through. The "proved" badge is
   true but the `usage` a reader is told to follow is a bundle. Fix: **port** (FOUNDATIONS §4 lists
   deleting `*Toolkit.lean` and bundles); until then, tag the clause theorems non-partially and the
   bundle `(partial)` so the atlas points at usable statements.
6. **Deprecated aliases are atlas formalizations.** Batteries' `alias` copies the target docstring,
   tag line included, so 5 deprecated aliases are listed beside their targets
   (`specNorm_mul_transpose_self`, `specNorm_sub_mul_transpose_mul_le`,
   `specNorm_add_sq_le_of_mul_transpose_eq_zero`, `frobSq_mul_left_of_conjTranspose_mul_self` in
   `norms-frob-spec`; `specNorm_le_one_of_isSymm_of_isIdempotentElem` in `projection-facts`), and the
   hand-written `usage` strings that survive sync still teach the old API ("From `hQ : Qᵀ * Q = 1`").
   Two docstring styles coexist (inherited "**Alias** of …" vs "Deprecated alias (F1 …)"). Fix:
   ExtractDecls should record `deprecated` and skip tags on deprecated declarations; give every alias
   the explicit one-line docstring.
7. **`declarations.json` is 4.6 % noise.** 328 line-0 records (`Matrix.IsHermitian.cfc.congr_simp`,
   `mulLinearMap.congr_simp`, `basisOfLinearIndependentOfCardEqFinrank'.congr_simp`, `sizeOf_spec`,
   `eq_def`, `ctorIdx`, …) enter through the module-based selection; `isAutoComponent` filters
   `match_`/`proof_`/`eq_` but not these. Users grepping the index (AGENTS.md recipe) see Mathlib names
   as NLAlib declarations. Fix: drop `line = 0` and the known suffixes in `isPublicName`.

### B. Content that no longer matches the Lean

8. **Atlas text still says ℝ / `Fin` after F1.** D13 (`docs/rclike/DESIGN.md:22,390`) promised to
   reword 12 definition entries; 11 still say ℝ (`svd`: "Every $A\in\mathbb R^{m\times n}$ …
   $U\Sigma V^\top$", all four Lean forms over `RCLike`; `matrix-norms-def`: "of a real matrix";
   `pseudoinverse`, `residual-def`, `quadform-def`, `orthonormal-columns-def`, `best-rank-approx-def`,
   `condition-number-def`, `svd-def`, `schatten-norms-def`, `principal-angles-def` (this one is still
   real in Lean)). Beyond D13: `eckart-young`, `weyl-mirsky`, `cauchy-interlacing`,
   `projection-facts`, `orthonormal-completion`, `psd-cone-self-dual`, `norms-frob-spec` (14 entries
   with RCLike Lean and ℝ text); `eckart-young-frobenius`'s conclusion still explains "on Fin indices
   truncatedSVD attains it … explicit Fin(card) normalization"; `pseudoinverse`'s usage for
   `specNorm_moorePenroseInverse_eq_fintype` cites "the explicit Fin(card) reindex". Fix: the D13 pass,
   plus a `check_atlas` heuristic (RCLike signature, `\mathbb R^{` text → warn).
9. **Rules documents describe the pre-F1/F2 world.** `STANDARDS.md:156` "Mathlib has no
   `MeasurableSpace (Matrix m n ℝ)`" and the `matrixMeasurableSpace` exception (deleted by F2a);
   example paths `Matrix/Pseudoinverse.lean` (`:18`), `Estimation/Hutchinson.lean`,
   `Krylov/Polynomial.lean` (`:97`) do not exist; §2 sends readers to `REORG_PLAN.md` for the tree, a
   2026-10-12 assessment with 602-file sizes and the old `Concentration/`, `Gaussian/` names.
   `CONTRIBUTING.md:28` and §7 (`:117–123`) say Tropp theorems "keep a `chN_` prefix" (there are 0) and
   that LRA/Gaussian work "moves into `NLAlib/Gaussian/`" (gone). `README.md:15–26` lists layers
   without Krylov and scripts as four files; its last section advertises `coverage-fixes.md`, a codex PR
   description. `scripts/check_layers.py:5` docstring has the old layer names (Concentration 1,
   Gaussian 2) while `LAYER` is right. `docs/coverage/README.md:22` "NLAlib proves the real-symmetric
   form of Hermitian statements". `atlas/README.md:76` "Status today (2026-10-09): 110 results".
   `TroppMatrixConcentration.md` points at `NLAlib/Concentration/Matrix/`. `llms.txt:3` gives the repo as
   `tchen-research/NLAlib`, FOUNDATIONS as `NLA-lib/NLAlib`. Fix: one doc-sync PR (allowed: it is not
   Lean); move README's last section to `docs/`.
10. **The F2 acceptance grep cannot pass under the freeze.** `STANDARDS.md:231` / `FOUNDATIONS_BRIEF.md:125`
    require `instance.*MeasurableSpace` to hit only the new ForMathlib file, but
    `Sketching/Sparse/SparseLaws.lean:19,29` declare two `MeasurableSpace` instances and Sparse is frozen
    (F3). Fix: exempt `Sketching/Sparse` in the grep, explicitly.
11. **The port manifest is a pre-F1 snapshot.** 16 entries name deleted files, the F2 file is absent,
    `field` still says ℂ for 198 files. Its ForMathlib merges are mechanical and topically odd:
    `Algebra/{Polynomial,Intervals,DiagonalSums,SignedCoefficients}` → `Algebra/InterlacingWeights.lean`;
    `SpecialFunctions/Gamma` → `Analysis/PowerInequalities`; `ImplicitFunction` and `Convex/Integral` →
    `LipschitzApprox`; `MatrixConditionalExpectation` → `IntegrableSup`; `TailComparison` →
    `ConditionalParameterJensen`. `BlockCauchySchwarz` (235 lines, zero importers, its `blockAnalysis`
    defs used nowhere) is `keep`; ForMathlib has no `drop` although `NormSumSq` is a two-line corollary
    of Mathlib's `sq_sum_le_card_mul_sum_sq`. Fix: regenerate after F2, hand-review ForMathlib targets by
    Mathlib directory, drop dead files.
12. **Stale generated side files.** `atlas/import_usage.json` (2026-10-12) still shows `residual` over
    ℝ with `Q.transpose`; `atlas.json` top-level `updated_at` is 2026-10-12 while results carry
    2026-10-13; `schema.json:3,18` has `$id …/randnla-atlas-0.1.json` on `prove2.me` but pins
    `schema_version` to `"0.2"`.

### C. ForMathlib: what is there and what looks misplaced

ForMathlib is 91 content files / 7.6 k lines / 270 declarations, all in `namespace NLAlib` except
the new `ForMathlib/MeasureTheory/Matrix.lean` (`namespace Matrix`). Most files have exactly one
importer, the leaf that needed the helper.

13. **It is not "general facts not about NLAlib's objects" (STANDARDS §2).** NLAlib-specific
    vocabulary lives here: `UniformSampling{Counts,Coupling,Jensen,Marginals}` define
    `iidSubsetJointPMF`, `sequenceLabelCount`, `uniformExactRowSubsetPMF` (SRHT/Sparse support);
    `Data/ExactRowSubset` (an `abbrev` type used by `CauchyBinet`); `Analysis/BernsteinParameter`
    (an identity about the matrix-Bernstein exponent); `Analysis/Matrix/{Order,QuadraticForm}` and
    `MeasureTheory/MatrixConditionalExpectation` are ℂ-only matrix facts (`Matrix n n ℂ`,
    `Order.lean:27`), at odds with the RCLike core; `Order/InterlacingDeletion`,
    `Algebra/InterlacingWeights`, `LinearAlgebra/IsolatedCharpoly` are helpers of one Matrix file each.
    Four ForMathlib topics have a same-named Matrix twin file (`SchurTriangularization`,
    `SimultaneousTriangularization`, `OrderedSchur`, `Triangular`, plus two `GramSchmidt.lean`).
    Fix (**port**): sort into "upstreamable" (keep, Mathlib namespaces) vs "NLAlib helper" (move to the
    consumer's area).
14. **Upstream candidates are named for NLAlib, not Mathlib.** Everything is `NLAlib.foo`, so
    dot notation and upstreaming both need renames; three declarations even sit in pseudo-Mathlib
    namespaces under `NLAlib`, where dot notation cannot find them:
    `NLAlib.ConcaveOn.le_map_integral_of_integral_mem` (`Analysis/Convex/Integral.lean:22`),
    `NLAlib.ConcaveOn.condExp_map_le_of_condExp_mem` (`MeasureTheory/ConditionalJensen.lean:23`),
    `NLAlib.iIndepFun.integrable_exp_mul_sum₀` (`Probability/IndepExpSum.lean:21`). File names are
    topic names (`BinomialRootComparison`, `GeometricRate`), not the Mathlib file they would land in
    as STANDARDS §2 asks. Fix (**port**): ForMathlib declarations in Mathlib namespaces, mirroring
    Mathlib paths; meanwhile `_root_.ConcaveOn.…` would at least make dot notation work.
15. **Mathlib overlaps and Mathlib facts as atlas results.** `NormSumSq.lean:24` is
    `norm_sum_le` + `sq_sum_le_card_mul_sum_sq`; `MomentInterpolation.lean:39` restates
    `eLpNorm_le_eLpNorm_of_exponent_le` as integrals and is itself the atlas result
    `positive-real-moment-comparison` (area `gaussian-inverse`); `Independence.lean` re-proves Fubini
    for independent variables from `indepFun_iff_map_prod_eq_prod_map_map`. ForMathlib carries 9 atlas
    tags (5 results, incl. `matrix-freedman` on `ae_posSemidef_condExp_of_ae_posSemidef`), against
    "Mathlib facts are not atlas results". Fix: keep the bridge lemmas, move the atlas tags to the
    consumer results or cite `mathlib_prereqs`.
16. **The new global instances are right but sit beside others.** `Matrix.instMeasurableSpace` /
    `instBorelSpace` (`ForMathlib/MeasureTheory/Matrix.lean:37,42`) are the instances Mathlib would add
    (intentional, document it — done in the module docstring). Other global instances on Mathlib types
    remain outside ForMathlib: `orthogonalGroupCompactSpace` (`Matrix/Subspaces/Stiefel.lean:24`), and
    the scoped `NLAlib.TwoPi.fact_zero_lt_two_pi` in `FourierCircle.lean:33`. Fix (**port**): move the
    `CompactSpace (orthogonalGroup)` instance to ForMathlib.
17. **Provenance noise from ports.** 1 770 40-hex commit hashes and 1 461 "SparseFock" mentions in
    docstrings (mostly Sparse, but 3 ForMathlib and 6 Matrix files); 386 citations of "operator
    re-derivations `rt:…`/`sh:…`" labels whose document is not in the repo; 256 "Prove2me" mentions.
    Nine files derived from the MIT Sparse code (2 ForMathlib, 2 Matrix, 5 Sketching) carry no MIT
    header although `CONTRIBUTING.md` says to keep the origin's copyright line (and calls every origin
    Apache-2.0, while `docs/ports/` holds an MIT licence). Fix: licence headers now (cheap, legally
    relevant); provenance trimming at **port**.

### D. Conventions that surprise a Mathlib-trained reader

18. **One flat `namespace NLAlib` with `_root_.Matrix.IsHermitian.*` inside.** Intentional
    (STANDARDS §2) and well motivated (dot notation on `hA`), but combined with oddity 4 it means the
    most important spectral theorems live outside the namespace the tooling audits. Also 1 677
    declarations under `NLAlib.SparseSketch.*` and five under `NLAlib.Assembly.*`
    (`rsvd_explicit`, `gn_assembly`: algorithm-named, `LowRank/RandomizedSVD/Assembly.lean`). Document it.
19. **`atlas:` vs `Atlas:`.** The machine tag is a lower-case line `atlas: id` at the end of a
    docstring (1 697); a capitalised prose `Atlas: \`id\`` (914) is ignored, and both often appear in
    the same docstring (`MatrixStatistics.lean:37–38`). 180 defs and 1 instance are tagged, so
    "formalizations" of a theorem entry include definitions. Intentional, but the case distinction is
    invisible; document it in STANDARDS §4 and have ExtractDecls warn on `Atlas:` in the last line.
20. **`SCAFFOLD:` docstrings double as tags.** A sorry lives only in a declaration whose docstring
    starts `SCAFFOLD: <id>`; 16 exist (Krylov 8 incl. PowerMethod, Matrix/Factorizations 6,
    Matrix/Spectral/Inertia 1, LowRank/Cholesky/PartialCholesky 1). Downstream sorry-dependent declarations are reported `stated` (23). Intentional;
    see oddity 2 for the partial bug.
21. **File-level options.** `set_option backward.isDefEq.respectTransparency false` in 95 files
    (81 Matrix, 1 ForMathlib: `UniformCollision.lean:16`) is a compatibility switch Mathlib does not
    use; `maxHeartbeats` up to 2 000 000 in 29 files; `maxRecDepth` in 10; `autoImplicit false`
    repeated in 242 files although `lakefile.lean` sets it; `open scoped BigOperators` 179 times.
    **port** (FOUNDATIONS §4), but `autoImplicit`/`BigOperators` lines are zero-risk deletions.
22. **`open scoped Classical` in 24 files** (6 ForMathlib), none unscoped. Mathlib discourages it in
    statements (it changes `Decidable` instances in signatures). Check that no public statement elaborates
    with a classical instance where a caller has a real one; **port**.
23. **Names.** `frobSq`/`frobNorm`/`frobInner`/`specNorm` instead of Mathlib's `‖A‖` under the scoped
    norms (bridges `frobNorm_eq_norm`, `specNorm_eq_norm` exist), `pinvL`/`pinvR` beside
    `moorePenroseInverse`, `quadForm` that collides with `QuadraticForm` vocabulary: intentional,
    documented in STANDARDS §3. Less defensible: theorem names that mention deleted definitions
    (`lamMin_eq_of_orthogonal_diagonalization`, F1 deleted `lamMin`), `_fintype` suffixes left by the
    `Fin`/`Fintype` split (`specNorm_moorePenroseInverse_eq_fintype`, `exists_cholesky_of_posSemidef_fintype`),
    182 names containing `complex` (leaf twins outside the F1 core), ASCII Greek in fields and names
    (`LanczosDecomp.alpha/beta`, `lambdaMax`/`lambdaMin`, `sigmaMin`), British `IsAffineMinimiser`
    (58 hits) where Mathlib spells `Minimizer`, and bundle names `*_toolkit_properties`.
24. **Deprecated aliases before v0.1.** STANDARDS §1 (`:38`) says renames are direct before `v0.1`;
    F1 nevertheless added 37 aliases, about 12 of which no file other than the declaring one mentions
    (FOUNDATIONS: alias only if used outside the core). Coverage still cites three
    (`hj13` §0.6.5 → `exists_orthogonal_completion`, `exists_orthonormal_complement`; Thm 2.1.4 →
    `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`). Fix: repoint coverage, drop unused aliases,
    keep `docs/renames/2026-10-F1.json` as the record.

### E. Repository hygiene

25. **"F1" means three things.** Dedup agent F1 (`docs/dedup/F1.md`, `renames/2026-10-12-dedup-F1.json`),
    foundation change F1 (`renames/2026-10-F1.json`, `docs/rclike/F1-*.md`), and F2a's report filed
    under `docs/rclike/` although it is about measurability. Round codes G0–G3, T1–T3, M1–M7, P_*, S1–S2,
    A1–B3, K-A…, D-A… appear across docs. Also `docs/port/` vs `docs/ports/` (manifest vs licence).
    Fix: a `docs/history/` folder with a one-line index of each round.
26. **Committed build artefacts and one-off checks.** `scripts/__pycache__/reorg.cpython-313.pyc` is
    tracked; `docs/rclike/Proto.lean` is an unbuilt Lean file in docs referencing missing `T1–T4.lean`;
    CI permanently runs two one-off PR audits (`AuditNewProofs.lean` 30 KB of module lists,
    `AuditGaussianInverse.lean` with `maxHeartbeats 0`) that Audit.lean subsumes once oddity 4 is fixed.
    `reorg.py`'s `TREE` lists leaves that do not exist (`ForMathlib/Topology`, `Probability/Basic`,
    `Solvers/Preconditioning`, …) and omits ones that do (`ForMathlib/Analysis/Calculus`, …).
27. **Atlas areas are the pre-reorg taxonomy.** Areas are `gaussian`, `concentration`, `lra`,
    `gaussian-concentration-tools`, … while directories are `Probability`, `RandomMatrix`, `LowRank`;
    REORG_PLAN expected the two trees to coincide. Five sources are unused (`buchholz01`,
    `tropp11-freedman`, `tropp12`, `mcdiarmid89`, `ftu23`); five results cite no source
    (`orthonormal-columns-def`, `quadform-def`, `trace-estimators-def`, `inverse-power-gram-def`,
    `orthonormal-basis-matrix`); the libraries `lra` and `gaussian-facts` are `ours: true` though ported.
    **port** (FOUNDATIONS §4: splitting the atlas out).

What I checked and found fine: no layer violations or sideways imports; no unscoped `open Classical`;
`sync_atlas.py` now marks `proved` only when every non-partial formalization is sorry-free, and no
proved result has a non-proved non-partial formalization; coverage `decls` all resolve; a heuristic
scan for results proved only by one-line wrappers found none beyond the bundle pattern of oddity 5.

## Summary: top 10

1. Books tab: 147 HJ items shown as "candidate" are proved; coverage statuses are never checked against the atlas.
2. ExtractDecls drops `(partial)` after a `SCAFFOLD:` id, so `principal-angles-def` (41 proved forms), `givens-rotation-def`, `gram-schmidt` read "scaffold".
3. `Audit.lean` audits only `NLAlib.*` names: Courant–Fischer/Weyl (`_root_.Matrix.IsHermitian.*`) and the new Matrix instances escape the axiom and sorry checks.
4. 35 "proved" results are witnessed only by `*_properties` bundles with pasted pretty-printed signatures.
5. 11 of the 12 D13 entries and ~5 more still describe the core over ℝ / `Fin`; usage strings teach the removed `Qᵀ * Q = 1` API.
6. Deprecated aliases inherit `atlas:` tags (5 listed as formalizations); 12 aliases have no external user; coverage cites 3.
7. Live docs are pre-F1/F2 in places: STANDARDS §3 measurability paragraph, nonexistent example paths, CONTRIBUTING §7 and `chN_`, README layers, coverage README "real-symmetric", llms.txt repo URL.
8. Proved results depend on "candidate" entries (17 edges) because definitions are tagged `(partial)`; 12 candidates have Lean content.
9. ForMathlib mixes upstreamable facts with NLAlib-specific and ℂ-only matrix helpers, all in `namespace NLAlib` (three in fake `NLAlib.ConcaveOn`/`NLAlib.iIndepFun` namespaces), with Mathlib overlaps (`NormSumSq`, `MomentInterpolation` as an atlas result) and a dead 235-line file kept by the manifest.
10. The port manifest is pre-F1 (16 deleted files, ℂ fields) and the F2 acceptance grep cannot pass while Sparse's two `MeasurableSpace` instances are frozen.
