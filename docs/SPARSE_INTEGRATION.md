# Integrating the sparse-sketch trace-moment proof (formerly `Sketching/Sparse/SparseFock`)

Owner's directive (2026-10-12): "sparse fock is a strange name. the stuff for this proof should
be integrated properly." This document is the design produced for that, with the coordinator's
decisions on the open points recorded here (the design text below is as written by the design
agent; the decisions override its recommendations where they differ).

## Decisions taken (coordinator, 2026-10-12)

- **D1 finite laws**: keep the real-weighted `FiniteLaw` structure, but as *proof-internal*
  machinery inside the sparse-sketch directory (namespace `NLAlib.SparseSketch`), not as library
  vocabulary under `Probability/Sampling`: the library states laws as Mathlib measures and
  expectations as Bochner integrals (STANDARDS §3), and the public theorems already do so. The
  existing bridge to measures stays; a later port to `PMF` is optional.
- **D2 frames**: keep `Frame` internal, with bridges to `HasOrthonormalCols` (recommended option).
- **D3 layout**: approved as designed (public leaf `Sketching/Sparse`; `MomentMethod`,
  `IIDComparison`, `FockModel`, `Bands/{Directional,Heavy,Light,Mixed}` below it); add the leaves
  to `TREE` in `scripts/reorg.py`.
- **D4 namespace**: `NLAlib.SparseSketch` (plus the five sector sub-namespaces) for the machinery;
  public definitions and theorems flat in `NLAlib` as designed.
- **D5 public names**: as proposed (`sparseStackMatrix`, `uniformSparseMatrix`, `sparseMomentOrder`, …).
- **D6 sign type**: deferred (not part of the integration).
- **D7 atlas**: split CountSketch out as `countsketch-ose`; add the four `candidate` entries;
  the manuscript's bibliographic data is for the owner to supply (source entries added as stubs).
- **D8 optional generalisations**: deferred until after the integration.
- **D9 sums of squares**: `x ⬝ᵥ x` and `‖x‖ ^ 2`, via one temporary definition during the move.

# Design: integrating the SparseFock subtree into NLAlib

Read-only design (2026-10-12). No repository file was edited and no Lean or lake process was run. Inputs were review_sparsefock.{md,json}, review_formathlib.md, atlas/declarations.json (16:44 snapshot), STANDARDS.md, REORG_PLAN.md and scripts/reorg.py. The machine-readable companion is `design_sparse_integration.json`. It holds:
- the 132-row file table;
- the namespace map;
- a draft map of 1608 declaration renames and 115 deletions, checked to have 0 internal collisions and 0 clashes with existing `NLAlib.*` names;
- the phases with their items and file counts;
- the decisions D1–D9;
- the atlas plan.

## 0. What the subtree is

**Provenance.** It is a port of the Lean project `SparseFockFormal`:
- author Diar Heidary, MIT licence (`docs/ports/sparse-fock-MIT.txt`), pinned commit `b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`;
- it formalises a TeX manuscript that the docstrings cite by its labels: `sh:sparse` (SparseStack) and `sh:exact-s` (uniform exact-s columns, i.e. OSNAP);
- `FullyIndependentSparseStack` is the manuscript's "TeX Theorem 1.1".

**The theorem.** SparseStack and OSNAP are ε-subspace embeddings with probability at least 1−δ. The parameters are:
- s < 1356·q/ε nonzeros per column;
- m < 306456·(d+q)/ε² rows;
- q = max(1, ⌈log₂(d/δ)⌉).

**The proof is a moment method:**
1. Markov's inequality on E tr G^{2q}, where G = UᵀSᵀSU − I.
2. Comparison of the sparse sketch with an iid sparse-ternary model. This uses a martingale (fill/thin) coupling and the convexity of A ↦ tr A^{2q}.
3. The iid moment is written as the vacuum moment of a multiplication operator on a product orthogonal-polynomial ("Fock") basis.
4. That operator is split into bands that raise, preserve or lower the grade. A ladder iteration bounds the vacuum moment by the band norms.
5. The band norms are bounded sector by sector (heavy–heavy, light/shared-leg, mixed light–heavy, directional) by the envelope 3+√2.
6. Explicit rounded parameters finish the proof.

**Side results.**
- 4q-wise independent SparseStack has the same guarantee, and so does OSNAP with 4q-wise independent whole columns.
- A frame sampled independently of the sketch is also covered.

**Why the name has to go.** "Fock" is a genuine term for the occupation-number space in step 3. As the name of the whole topic, though, it says nothing about what the topic proves. The proposal names the topic by its stages and keeps "Fock" only for the Fock-space objects.

## 1. Inventory (role groups)

Counts are files / lines. Each row of the JSON `files` table carries one of these roles.

| role | what | files |
|---|---|---|
| **G** general mathematics that belongs elsewhere (9 files, 2.2k lines) | the FiniteLaw family: ForMathlib/Probability/{FiniteLawBasics, FiniteLawIndependent, FiniteProductLaw, FiniteLawMeasure} + SF/UniformExactSFiniteLaw + SF/FiniteLocalMoments; SF/TypedBlockCS (block Cauchy–Schwarz on PiLp 2); the general halves of SF/TracePowerConvexity and SF/MatrixTail; small helpers inside proof files (§2) | |
| **M** sketch model, laws, parameters (11 files, 2.4k lines) | SparseStackModel, SparseStackDistribution, UniformExactSModel, SparseLaws, CountSketch; parameters SparseParameterConstants, SparseFailureOrder, SparseRoundedScales, SparseMomentParameters; ParsevalFrame, MatrixFrameBridge | |
| **C** moment / trace calculus machinery (89 files, 23.4k lines) | Fock model (Pattern, LocalOperators, BandInventory, FiniteSiteOperators, ExternalOperators, FockHilbert, TernaryJacobi, ProductFock, VacuumMoment, FiniteL2); bands (GlobalBands, NamedBands, ConcreteLadder(+Iteration), BandEnvelope, BandCoefficientBounds, ScalarBounds, ConcreteBandAssembly, ConcreteBandEnvelope); Directional (8), Heavy (13), Light (20), Mixed (3); iid comparison (SparseIID* ×6, MomentTransfer, DistributionBridges, the exact-s coupling ×10); tail and assembly (MatrixTail, ConcreteMomentEndgame, EmbeddingAssembly, IndependentFrameAssembly, ExactSparseProjectionTail, ExactSparseRoundedBounds) | |
| **T** final theorems and wrappers (10 files, 1.8k lines) | internal endpoints FullyIndependentSparseStack, ExactSparseMatrixEmbedding, SparseMomentMatching, ExactSparseMomentMatching; public wrappers SparseEmbedding (5 `sparse-ose` tags), SparseEmbeddingTransport (2), SparseFiniteIndex (2), SparseFrameBridge, CountSketchExpectation/Tail (4 `sparse-ose (partial)`) | |
| **S** shims and aggregator (13 files) | 11 SparseFock re-export shims, ForMathlib/Probability/FiniteLaw.lean, the SparseFock.lean aggregator | |

Out of scope: `ForMathlib/Probability/FiniteProductEvents.lean`. It is in namespace NLAlib, is used by SRHT and is not part of the port.

## 2. What moves out, where, and under what name

**Finite laws (decision D1).** `SparseFock.FiniteLaw` is a real-weighted `PMF` on a Fintype. A third spelling, `finiteSamplingPMF` with NNReal weights, already lives in Probability/Sampling.
- **Recommendation (a): keep the real-weighted structure** as a computational representation.
  - Rename it `NLAlib.FiniteLaw` and move it to `Probability/Sampling/{FiniteLaw, FiniteLawIndependent, FiniteLawProduct, FiniteLawMeasure, FiniteLawLocalMoments}.lean`.
  - The module docstring should say that it is a view of `PMF`, linked by the existing `toPMF` / `toMeasure` / `integral_toMeasure` / `real_toMeasure`, plus a new `ofPMF`.
  - Rule: atlas-tagged statements use `Measure`, as the public wrappers already do.
- **Why not replace it.** Replacing it by `PMF`/`Measure` means rewriting 37 files: about 250 occurrences of `FiniteLaw`, about 265 `.expect` calls and about 130 `.prob` calls into ENNReal or Bochner arithmetic. That is several agent-days of high-risk work, and the convex-order and conditional-law computations depend on exact real sums.
- **The move is cheap.** Only 5 files write `SparseFock.FiniteLaw` with the qualifier. Unqualified `FiniteLaw` keeps resolving inside `NLAlib.*`.
- **Merged into the moved files:**
  - `FiniteLaw.uniform` / `map` / `ext_weight` (from UniformExactSFiniteLaw);
  - from SparseIIDTransfer: `expect_fintype_sum` → `FiniteLaw.expect_sum`, `expect_finset_sum`, `expect_mul_const`, `barycenter` → `FiniteLaw.barycenter`, and `finite_jensen` → `FiniteLaw.map_barycenter_le_expect`;
  - the k-wise matching layer: `MatchesUpTo` → `FiniteLaw.MatchesUpTo`, `HasLocalDegree` → `NLAlib.HasLocalDegree`.
  - `DependsOn` is exactly Mathlib's `DependsOn f ↑S`, so it is deleted.
- **Fallback (b):** keep it proof-internal as `NLAlib.SparseSketch.FiniteLaw`.

**Parseval frames (decision D2).** `ParsevalFrame.Frame n d` is a bundled `HasOrthonormalCols` in row form. It appears in 67 files, about 500 times, including about 380 uses of `F.u`.
- Keep it internal as `NLAlib.SparseSketch.Frame` and add bridges:
  - `Frame.rows := rowMatrix F.u` (this also replaces both `frameRows`);
  - `Frame.hasOrthonormalCols`;
  - `frameOfMatrix` stays.
- Public statements are already in `HasOrthonormalCols`.
- `EVec d` is replaced by `EuclideanSpace ℝ (Fin d)` (18 files) and `ParsevalFrame.normSq` by `‖x‖^2`.
- Redefining `Frame` on top of `HasOrthonormalCols` is an option for the owner, to do last if at all.

**Other moves and replacements.**

| item | to | new name |
|---|---|---|
| TypedBlockCS (13 decls, Mathlib-only) | ForMathlib/Analysis/InnerProductSpace/BlockCauchySchwarz.lean | `typed_block_cs` → `norm_sum_comp_sq_le`; `typed_block_cs_with_projections` → `norm_sum_comp_sq_le_of_projections`; `analysis_gram_eq` → `blockAnalysis_adjoint_comp_eq`; `synthesis_cogram_eq` → `blockSynthesis_comp_adjoint_eq`; `block_comp_eq` → `blockSynthesis_comp_blockAnalysis_eq`; `blockAnalysis`/`blockSynthesis` flat in NLAlib |
| MatrixTail general | Matrix/Spectral/TraceEigenvalues.lean | `opNorm_even_pow_le_trace` → `specNorm_pow_two_mul_le_trace_pow` (state with `specNorm`; fold in the `_of_nonempty` variant); `trace_even_pow_nonneg` → `trace_pow_nonneg_of_even` |
| MatrixTail finite-law Markov | Probability/Concentration/Matrix/FiniteLawTraceMarkov.lean | `matrix_markov_tail` → `FiniteLaw.prob_le_norm_le_expect_trace_pow_div` |
| MatrixTail duplicates | delete | `trace_pow_eq_sum_eigenvalues`, `opNorm_eq_piNorm_eigenvalues` (keepers now in Matrix/Spectral/TraceEigenvalues and QuadraticProbe), `opNorm_le_iff_quadraticForm` → `specNorm_le_iff_abs_dotProduct_mulVec_le`, `quadraticForm*`, `IsGramOSE*` → `isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le`, `applyRectMatrix` → `Matrix.toEuclideanLin` |
| TracePowerConvexity general (~20 decls) + `symmetricMatrices` | Matrix/Functions/TracePowerConvexity.lean (layer 0; imports Matrix.Calculus.InversePowerConcavity) | names kept (`convexOn_traceEvenPower`, …); delete the 3 wrappers and `hasDerivAt_affineMatrix`/`traceCLM`; the sparse corollary goes to IIDComparison/TraceMomentOrder.lean |
| trace-power convexity, optional later | — | `symmetricMatrices` could become Mathlib `selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℝ)` |
| `outer` (Parseval, External) | Mathlib | `Matrix.vecMulVec` (definitional) |
| sums of squares (5 defs: `FiniteHilbert.normSq`, `LightSectorConcrete.energy`, `coordinateEnergy`, `coordNormSq`, `fockNormSq`) | Mathlib (D9) | `x ⬝ᵥ x`, through one interim `SparseSketch.sumSq` |
| quadratic forms (`LightSectorConcrete.quadratic`, `coordinateQuadratic`, `HeavyBandsConcrete.quadratic`, `MatrixTail.quadraticForm`) | library | `NLAlib.quadForm` |
| OSE spellings: `IsMatrixSparseStackOSE`, `IsMatrixUniformExactSOSE` | library | `IsSubspaceEmbedding` |
| OSE spellings: `IsSparseStackOSE`, `IsUniformExactSOSE` | library | `IsSubspaceEmbedding (sparseStackMatrix Z) (rowMatrix F.u) ε` |
| OSE spelling: `IsGramOSE` | library | the Gram lemma |
| small helpers | Mathlib / Matrix/Norms / ForMathlib/Algebra/DiagonalSums | `two_mul_le_sq_add_sq` → `two_mul_le_add_sq`; `sum_erase_univ_eq_sub` → `Finset.sum_erase_eq_sub`; `sum_subtype_eq_filter` → `Finset.sum_subtype_eq_sum_filter`; `l2_norm_transpose` and `norm_transpose_real` → `specNorm_transpose` / `Matrix.l2_opNorm_conjTranspose`; `trace_pow_smul` → `smul_pow` + `trace_smul`; `abs_entry_le_l2_opNorm` → `abs_apply_le_specNorm`; `sum_erase_comm` → `sum_sum_erase_comm` (the duplicates `sum_ordered_swap` and `sum_offDiagonal_swap` are deleted); `normSq_sum_le_card` → `norm_sum_sq_le_card_mul_sum_norm_sq` |
| FiniteL2 (WeightedONBasis) | into the proof: FockModel/WeightedBasis.lean | takes a `FiniteLaw` parameter; dead chain `vacuum_moment`, `vacuum_mulOp`, `mulOp_pow`, `mulOp_one` deleted |

## 3. The proof-specific remainder

**Layout (decision D3).** Name the directories by proof stage, not by "SparseFock". This needs 8 new leaves in `TREE` in scripts/reorg.py, and `Sketching/Sparse/SparseFock` is removed.

```
Sketching/Sparse/               public: CountSketch*, SparseStack, SparseStackLaw, UniformSparse, SparseLaws,
                                SparseEmbedding, SparseEmbeddingTransport, SparseFiniteIndex        (11 files)
Sketching/Sparse/MomentMethod/  Frame, FrameOfMatrix, ParameterConstants, MomentOrder, RoundedScales,
                                MomentParameters, GramError (new), GramTail, Endgame, Assembly, IndependentFrame,
                                SparseStackTheorem, UniformSparseTail, UniformSparseRoundedBounds,
                                UniformSparseTheorem, SparseStackLimitedIndependence, UniformSparseLimitedIndependence (17)
Sketching/Sparse/IIDComparison/ TernaryCoordinateLaws, SelectionKernel, SelectorMarginals, ConditionalBarycenter,
                                IndependentCopyLift, ConvexOrder, TraceMomentOrder (new), MomentTransfer,
                                DistributionBridges, FillThinCoupling, Exact{SignActions, SelectionSymmetry,
                                ColumnMarginals, ConditionalSupport, CoordinateSymmetry, ConditionalBarycenter,
                                IIDMatrixError, ConditionalMatrixTransfer, MomentTransfer}               (19)
Sketching/Sparse/FockModel/     OccupationPattern, LadderMatrices, LadderWords, SiteKernels, TensorOperators,
                                FockSpace, TernaryJacobi, ProductBasis, WeightedBasis, VacuumMoment       (10)
Sketching/Sparse/Bands/         GlobalBands, NamedBands, Ladder, LadderIteration, EnvelopeArithmetic,
                                CoefficientBounds, ScalarBounds, BandAssembly, BandEnvelope                (9)
Sketching/Sparse/Bands/Directional/  OccupationProfiles, SiteTransitions, MarkedCoefficients, MarkedReindexing,
                                OccupationEnergy, OutputEnergy, RestrictedBounds, NormalizedBands          (8)
Sketching/Sparse/Bands/Heavy/   MarkedSites … NormalizedBands (Heavy prefix dropped)                     (13)
Sketching/Sparse/Bands/Light/   AbstractContraction, SharedLegOperators, … NormalizedBands                (20)
Sketching/Sparse/Bands/Mixed/   RowFactorization, RestrictedBounds, NormalizedBands                        (3)
```

**Why this layout.**
- Each directory is one stage of the proof (§0).
- The public leaf contains only library-vocabulary statements.
- `BandInventory` goes to FockModel (as LadderWords) because FiniteSiteOperators imports it.
- The parameters go with MomentMethod: q is the moment order.
- Base names repeat across sector directories (e.g. `NormalizedBands`), which Lean allows.

Every old path is mapped exactly once in the JSON `files` table: 98 moves, 12 shim deletions, 1 merge-out, 2 splits, 8 kept, 2 new files.

**Namespaces (decision D4).** There are 48 module namespaces today. They become:
- **`NLAlib.SparseSketch`**: one internal namespace for everything proof-internal;
- **sub-namespaces** `SparseSketch.UniformSparse` (the exact-s twins), `.Directional`, `.Heavy`, `.Light`, `.Mixed`, which keep the sector-scoped paper notation (`D0`, `CMatrix`, `AUpMatrix`, …);
- **type namespaces** for dot notation: `Frame`, `Level`, `Leg`, `Word`, `Shift`, `Pattern`, `Profile`, `WeightedONBasis`, `FiniteLaw`;
- **flat public names (D5).** The parameter functions become `sparseMomentOrder`, `sparseColumnSparsity`, `sparseBlockRows` and `sparseRows`. The models become:
  - SparseStack: `SparseStackSample`, `SparseStackSelectors`, `SparseStackSelectors.toSample`, `sparseStackMatrix`, `sparseStackSelectorLaw`;
  - uniform exact-s: `UniformSparseSupport`, `UniformSparseColumn`, `UniformSparseSample`, `uniformSparseMatrix`, `uniformSparseSampleLaw`, `uniformSparseColumnLaw`.

  These match the existing `sparseStackMeasure`, `uniformSparseMeasure`, `sparseStackMatrixOn` and `uniformSparseMatrixOn`.
- **Gram statements.** Public statements use `Sᵀ * S`, so `sketchGram` disappears from them.

**Renaming generic names.**
- Constants:
  - `cStar` → `convexOrderConstant`, `Cband` → `bandConstant`, `L` → `scaleConstant`;
  - `M0` → `rowTarget`, `Dq` → `momentDim`;
  - `betaEnvelope` → `bandEnvelope`, `roundedMomentBase` → `momentBase`.
- Fock-model objects:
  - `TernaryJacobi.law` → `ternaryLaw` (and `coordinateLaw` is deleted);
  - `EtaOutcome` → `TernaryOutcome`; `LocalOperator.Op` → `LevelOp`;
  - `weightedInner` / `weightedONBasis` → `ternary*` and `product*`.
- Fibers and gradings:
  - `fiber`, `fullFiber` and Heavy `fiber` → `fockFiber`;
  - `Homogeneous` ×3 → `IsGradeShift g δ M`;
  - `gradeZ` ×2 → `Pattern.gradeZ` and `fullGradeZ`.
- Name cleanups:
  - `SparseStackLimitedIndependence.*` gets the suffix `_of_matchesUpTo`;
  - inside UniformSparse, the prefixes `uniformExactS_` and `exactS_` are dropped.

**Checking the rename map.** The generated map (JSON `decl_renames_draft`) has 0 collisions and 0 clashes with existing `NLAlib.*` names. That holds once the Phase 1–2 deletions are applied: the only would-be clashes were the 4 trace wrappers, and Phase 1 deletes them.

**The Light/Mixed/Heavy copy families.**
- **Delete:**
  - the 12-lemma `LightBandsConcrete` block in LightMixedFactorization (verbatim copies of the Mixed ones, unused downstream);
  - `MixedBandsConcrete.norm_normalized_mixed_term_eq` (the Directional copy is kept);
  - `LightBandsConcrete.RowFock` and `NamedBands.Physical`;
  - the Heavy copies of `frameRows`, `fiber` and `full_normSq_eq_sum_fiber` (Heavy imports Directional, so Directional is upstream).
- **Parametrise:**
  - the SparseStack and exact-s Gram layers, over the sketch matrix S (new MomentMethod/GramError.lean);
  - the two `unconditional_convex_order` proofs, through one `FiniteLaw.expect_convex_le_of_barycenter`;
  - the three conclusion bundles: delete them and give each endpoint two theorems.
- **Optional, after the integration (D8):**
  - Up/Down heavy-leg parametrisation of the Mixed factorisation lemmas;
  - the S-parametrised coupling layer (xMarginal, conditionalYLaw, selectionKernel, jointColumnLaw);
  - unifying `UniformSparseSupport` with `ExactRowSubset`.

## 4. Order of work and risk

Run a full build after every phase. File counts come from grep.

| phase | content | files | parallel? | risk |
|---|---|---|---|---|
| 1 | **1A** delete 12 shims and repoint 20 importers, the aggregators and scripts/AuditNewProofs.lean (35 files). **1B** Light/Mixed duplicates, RowFock, Physical (7). **1C** MatrixTail and TracePowerConvexity duplicates (5). **1D** Mathlib one-liners (17). **1E** unused decls (3) | ~60 | yes: 5 groups with disjoint files (l2_norm_transpose belongs to 1D only) | low |
| 2 | vocabulary bridges 2a–2l (§2, §3): outer 16, sums of squares ~30, quadForm 17, frameRows/fiber 27, toEuclideanLin 6, IsGradeShift 13, OSE spellings 13, Gram layer 18, bundles 6, convex order 3, WeightedONBasis 4 | ~80 distinct | in 4 waves: W1 {2a, 2e, 2g, 2l}; W2 {2b, 2c}; W3 {2d, 2f}; W4 {2h, 2i, 2j, 2k}. Heavy and Light files are shared across items, so parallel agents need worktrees and a rebase, or one agent per wave | medium; 2i is the riskiest |
| 3 | moves out: 3a FiniteLaw (40), 3b BlockCauchySchwarz (17), 3c MatrixTail split (8), 3d TracePowerConvexity split (4), 3e small helpers (8) | ~70 | yes, 5 independent sources | low |
| 4 | namespace flattening with the rule map: `namespace`/`end` in 108 files, 222 `open` lines, qualified refs; ship docs/renames/<date>-sparse-sketch.json | ~120 | scripted; can be split by directory if every agent uses the same map; one build | medium (ambiguity from `open`) |
| 5 | directory rename: TREE update, mapping table → `scripts/reorg.py --apply` (98 git mv, ~290 import lines in ~120 files), aggregators, AuditNewProofs, docs | ~125 | no: single agent, freeze Sketching/Sparse | low (no Lean name changes) |

Concurrency note: Matrix/Spectral/TraceEigenvalues.lean was edited at 20:44 by another agent and now holds the trace keepers. Phases 1C and 3c must import it and must not recreate those lemmas.

## 5. Atlas

**Existing tags.** The 9 `atlas: sparse-ose` tags stay on the public wrappers in SparseEmbedding, SparseEmbeddingTransport and SparseFiniteIndex; their names do not change. `sync_atlas.py` regenerates `uses_defs`, which today lists 15 `SparseFock.*` names and will list the D5 names afterwards.

**Proposals (D7), human side only:**
1. Split `sparse-ose` into two results:
   - `countsketch-ose`: the 4 CountSketch declarations that today carry `sparse-ose (partial)` become full tags of the new result (sources cw13 Thm 2.2, nn13);
   - `sparse-ose`: SparseStack and OSNAP.
2. Add a source entry for the TeX manuscript and a repo entry for SparseFockFormal. The owner needs to supply the bibliographic data.
3. Add `candidate` entries. Tag each one only once its statement is restated in library vocabulary (Measure, `HasOrthonormalCols`, `specNorm`):
   - `sparse-limited-independence` (theorem): the 4q-wise SparseStack and OSNAP results;
   - `sparse-iid-moment-comparison` (lemma): E tr G_sparse^{2q} ≤ c*^{2q} E tr G_iid^{2q};
   - `sparse-trace-moment-bound` (bound): the explicit moment bound with envelope 3+√2;
   - `trace-power-convexity` (lemma, area matrix-trace): its statement is general, so it can be tagged right after Phase 3d.

**What stays untagged.** Fock, band and parameter lemmas stay as helpers that mention sparse-ose in prose only.

## 6. Decisions needed from the owner

| id | question | recommendation |
|---|---|---|
| D1 | FiniteLaw: keep, make internal, or replace by PMF/Measure | keep as `NLAlib.FiniteLaw` in Probability/Sampling, with a documented "computational view of PMF" rule |
| D2 | Frame vs `HasOrthonormalCols` | keep `SparseSketch.Frame` internal and add bridges; no redefinition |
| D3 | directory layout and the TREE change | Sparse + MomentMethod / IIDComparison / FockModel / Bands{Directional, Heavy, Light, Mixed} |
| D4 | internal namespace | `NLAlib.SparseSketch` with 5 sub-namespaces; keep "Fock" only for Fock-space objects |
| D5 | public names | sparseMomentOrder, sparseColumnSparsity, sparseBlockRows, sparseRows; SparseStack* / UniformSparse* |
| D6 | the two-valued `Sign` type | optional: switch to `Bool` + `rademacherBoolSign` (14 files) |
| D7 | atlas split, source entry, candidates | yes; the owner supplies the manuscript's bibliographic data |
| D8 | optional generalisations | defer until after the integration |
| D9 | sum-of-squares vocabulary | `x ⬝ᵥ x` and `‖x‖^2`, through one interim `sumSq` |

## Appendix: file table

Paths are shortened: `SF/` = Sketching/Sparse/SparseFock/ and `Sparse/` = Sketching/Sparse/. The columns are old path, new path, role, action, lines and notes.

| old | new | role | action | lines | notes |
|---|---|---|---|---|---|
| SF/DirectionalConcrete.lean | — | S | delete-shim | 12 | repoint importers ['HeavyMarkedSites', 'DirectionalNormalized'] to DirectionalRestrictedBounds; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/ExactSparseEmbedding.lean | — | S | delete-shim | 12 | repoint importers ['SparseEmbedding', 'ExactSparseMomentMatching'] to ExactSparseMatrixEmbedding; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/HeavyBandsConcrete.lean | — | S | delete-shim | 12 | repoint importers ['LightRowFactorization'] to HeavyNormalizedBands; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/LightBandsConcrete.lean | — | S | delete-shim | 12 | repoint importers ['MixedRowFactorization'] to LightNormalizedBands; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/LightSectorConcrete.lean | — | S | delete-shim | 13 | repoint importers ['LightRowFactorization'] to LightZeroBlock; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/MixedBandsConcrete.lean | — | S | delete-shim | 12 | repoint importers ['ConcreteBandEnvelope'] to MixedNormalizedBands; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/PaperParameters.lean | — | S | delete-shim | 12 | repoint importers ['SparseIIDFiniteLaws', 'BandEnvelope'] to SparseMomentParameters; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/SparseIIDCoupling.lean | — | S | delete-shim | 12 | repoint importers ['UniformExactSModel', 'SparseIIDTransfer'] to SparseIIDConditionalBarycenter; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/UniformExactSBarycenter.lean | — | S | delete-shim | 12 | repoint importers ['ExactIIDMatrixError'] to ExactConditionalBarycenter; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/UniformExactSSymmetry.lean | — | S | delete-shim | 12 | repoint importers ['ExactConditionalSupport'] to ExactColumnMarginals; drop from aggregator and scripts/AuditNewProofs.lean |
| SF/UniformExactSTransfer.lean | — | S | delete-shim | 12 | repoint importers ['ExactSparseProjectionTail'] to ExactMomentTransfer; drop from aggregator and scripts/AuditNewProofs.lean |
| ForMathlib/Probability/FiniteLaw.lean | — | S | delete-shim | 12 | re-export of FiniteLawIndependent; repoint 6 importers (FiniteProductLaw, FiniteLawMeasure, FiniteLocalMoments, TernaryJacobi, SparseStackDistribution |
| ForMathlib/Probability/FiniteLawBasics.lean | Probability/Sampling/FiniteLaw.lean | G | move-out | 306 | D1 option (a). Also receives FiniteLaw.uniform/map/ext_weight (from UniformExactSFiniteLaw) and expect_sum/expect_finset_sum/expect_mul_const/barycent |
| ForMathlib/Probability/FiniteLawIndependent.lean | Probability/Sampling/FiniteLawIndependent.lean | G | move-out | 189 |  |
| ForMathlib/Probability/FiniteProductLaw.lean | Probability/Sampling/FiniteLawProduct.lean | G | move-out | 112 |  |
| ForMathlib/Probability/FiniteLawMeasure.lean | Probability/Sampling/FiniteLawMeasure.lean | G | move-out | 85 | bridge toPMF/toMeasure/integral_toMeasure/real_toMeasure; delete unused toMeasure_singleton |
| SF/UniformExactSFiniteLaw.lean | — | G | merge-out | 126 | 7 decls (ext_weight, uniform, map, map_expect, map_uniform_equiv, ...) merged into Probability/Sampling/FiniteLaw.lean; file deleted |
| SF/FiniteLocalMoments.lean | Probability/Sampling/FiniteLawLocalMoments.lean | G | move-out | 266 | k-wise marginal matching (MatchesUpTo, HasLocalDegree, DependsOn) is general; names become FiniteLaw.MatchesUpTo, NLAlib.HasLocalDegree, NLAlib.Depend |
| SF/TypedBlockCS.lean | ForMathlib/Analysis/InnerProductSpace/BlockCauchySchwarz.lean | G | move-out | 228 | Mathlib-only; typed_block_cs -> norm_sum_comp_sq_le, typed_block_cs_with_projections -> norm_sum_comp_sq_le_of_projections; drop `open TypedBlockCS` i |
| SF/TracePowerConvexity.lean | Matrix/Functions/TracePowerConvexity.lean | G | split-out | 428 | general ~20 decls (traceEvenPower, convexOn_traceEvenPower, convexOn_tracePowerAlong, traceHessianKernel*, geomKernel*, tracePowerSecondAlong*) + symm |
| SF/MatrixTail.lean | Sparse/MomentMethod/GramTail.lean | G | split-out | 441 | general: opNorm_even_pow_le_trace(+_of_nonempty) -> specNorm_pow_two_mul_le_trace_pow and trace_even_pow_nonneg -> trace_pow_nonneg_of_even in Matrix/ |
| ForMathlib/Probability/FiniteL2.lean | Sparse/FockModel/WeightedBasis.lean | C | move-in | 297 | Fock-space machinery, only SparseFock users; WeightedONBasis takes a FiniteLaw parameter instead of repeating its fields; delete dead chain vacuum_mom |
| SF/SparseStackModel.lean | Sparse/SparseStack.lean | M | move | 444 | model: SparseStackSample, sparseStackMatrix; Gram/embedded-Gram/gramError/hollowGram (stated with Frame) move to MomentMethod/GramError.lean after the |
| SF/SparseStackDistribution.lean | Sparse/SparseStackLaw.lean | M | move | 158 | RawSample -> SparseStackSelectors, toSample -> SparseStackSelectors.toSample, rawSampleLaw -> sparseStackSelectorLaw |
| SF/UniformExactSModel.lean | Sparse/UniformSparse.lean | M | move | 353 | ExactSupport/ExactColumn/ExactSample -> UniformSparseSupport/Column/Sample, sketchMatrix -> uniformSparseMatrix, exactSampleLaw -> uniformSparseSample |
| Sparse/SparseLaws.lean | Sparse/SparseLaws.lean | M | keep | 64 | measures; instances renamed with the types |
| Sparse/SparseEmbedding.lean | Sparse/SparseEmbedding.lean | T | keep | 154 | atlas sparse-ose wrappers (5 tags); restate measure_*_gram_failure_le with Sᵀ*S instead of sketchGram |
| Sparse/SparseEmbeddingTransport.lean | Sparse/SparseEmbeddingTransport.lean | T | keep | 77 | 2 sparse-ose tags |
| Sparse/SparseFiniteIndex.lean | Sparse/SparseFiniteIndex.lean | T | keep | 114 | 2 sparse-ose tags |
| Sparse/SparseFrameBridge.lean | — | T | delete-after-2h | 47 | isMatrixSparseStackOSE_iff_isSubspaceEmbedding disappears with IsMatrixSparseStackOSE; isSubspaceEmbedding_iff_applyRectMatrix_bounds is replaced by i |
| Sparse/CountSketch.lean | Sparse/CountSketch.lean | M | keep | 112 | already library vocabulary |
| Sparse/CountSketchMoments.lean | Sparse/CountSketchMoments.lean | C | keep | 113 |  |
| Sparse/CountSketchExpectation.lean | Sparse/CountSketchExpectation.lean | T | keep | 106 | 1 partial tag |
| Sparse/CountSketchTail.lean | Sparse/CountSketchTail.lean | T | keep | 96 | 3 partial tags |
| SF/ParsevalFrame.lean | Sparse/MomentMethod/Frame.lean | M | move | 299 | SparseSketch.Frame (structure kept, D2); normSq -> ‖x‖^2, outer -> vecMulVec, EVec -> EuclideanSpace ℝ (Fin d) |
| SF/MatrixFrameBridge.lean | Sparse/MomentMethod/FrameOfMatrix.lean | M | move | 117 | frameOfMatrix -> Frame.ofMatrix; add Frame.hasOrthonormalCols |
| SF/SparseParameterConstants.lean | Sparse/MomentMethod/ParameterConstants.lean | M | move | 204 | cStar/Cband/L/M0/Dq renamed descriptively; failureOrder/roundedS/roundedB/roundedM become public flat names |
| SF/SparseFailureOrder.lean | Sparse/MomentMethod/MomentOrder.lean | M | move | 112 | lemmas about sparseMomentOrder |
| SF/SparseRoundedScales.lean | Sparse/MomentMethod/RoundedScales.lean | M | move | 318 |  |
| SF/SparseMomentParameters.lean | Sparse/MomentMethod/MomentParameters.lean | M | move | 229 | main_parameter_package |
| SF/ConcreteMomentEndgame.lean | Sparse/MomentMethod/Endgame.lean | C | move | 288 | moment + Markov endgame |
| SF/EmbeddingAssembly.lean | Sparse/MomentMethod/Assembly.lean | C | move | 130 | MainConclusions bundle deleted (2j); namespace MainTheoremAssembly -> SparseSketch |
| SF/IndependentFrameAssembly.lean | Sparse/MomentMethod/IndependentFrame.lean | C | move | 89 | frame sampled independently of the sketch |
| SF/FullyIndependentSparseStack.lean | Sparse/MomentMethod/SparseStackTheorem.lean | T | move | 172 | internal endpoint (TeX Thm 1.1); IsMatrixSparseStackOSE + MatrixMainConclusions deleted |
| SF/ExactSparseProjectionTail.lean | Sparse/MomentMethod/UniformSparseTail.lean | C | move | 234 | IsUniformExactSOSE deleted |
| SF/ExactSparseRoundedBounds.lean | Sparse/MomentMethod/UniformSparseRoundedBounds.lean | C | move | 226 |  |
| SF/ExactSparseMatrixEmbedding.lean | Sparse/MomentMethod/UniformSparseTheorem.lean | T | move | 186 | IsMatrixUniformExactSOSE + UniformExactSMainConclusions deleted |
| SF/SparseMomentMatching.lean | Sparse/MomentMethod/SparseStackLimitedIndependence.lean | T | move | 426 | 4q-wise independent SparseStack; candidate atlas result |
| SF/ExactSparseMomentMatching.lean | Sparse/MomentMethod/UniformSparseLimitedIndependence.lean | T | move | 380 | whole-column 4q-wise OSNAP; candidate atlas result |
| — | Sparse/MomentMethod/GramError.lean | C | new |  | S-parametrised Gram layer (sketchGram/embeddedGram/gramError/hollowGram for a sketch matrix S and Frame F); replaces the SparseStackModel and UniformE |
| SF/SparseIIDFiniteLaws.lean | Sparse/IIDComparison/TernaryCoordinateLaws.lean | C | move | 247 |  |
| SF/SparseIIDSelectionKernel.lean | Sparse/IIDComparison/SelectionKernel.lean | C | move | 122 |  |
| SF/SparseIIDSelectorMarginals.lean | Sparse/IIDComparison/SelectorMarginals.lean | C | move | 275 |  |
| SF/SparseIIDConditionalBarycenter.lean | Sparse/IIDComparison/ConditionalBarycenter.lean | C | move | 360 | coordinateLaw deleted (= ternaryLaw) |
| SF/SparseIIDTransfer.lean | Sparse/IIDComparison/IndependentCopyLift.lean | C | move | 424 | FiniteLaw helpers, barycenter, finite_jensen -> FiniteLaw; symmetricMatrices -> Matrix/Functions; matrixExpectation deleted |
| SF/SparseIIDUnconditional.lean | Sparse/IIDComparison/ConvexOrder.lean | C | move | 195 | unconditional_convex_order via FiniteLaw.expect_convex_le_of_barycenter (2k) |
| SF/MomentTransfer.lean | Sparse/IIDComparison/MomentTransfer.lean | C | move | 169 | trace_pow_smul deleted (Mathlib smul_pow, trace_smul) |
| SF/DistributionBridges.lean | Sparse/IIDComparison/DistributionBridges.lean | C | move | 274 |  |
| SF/UniformExactSCoupling.lean | Sparse/IIDComparison/FillThinCoupling.lean | C | move | 447 |  |
| SF/ExactSignActions.lean | Sparse/IIDComparison/ExactSignActions.lean | C | move | 293 |  |
| SF/ExactSelectionSymmetry.lean | Sparse/IIDComparison/ExactSelectionSymmetry.lean | C | move | 272 |  |
| SF/ExactColumnMarginals.lean | Sparse/IIDComparison/ExactColumnMarginals.lean | C | move | 170 |  |
| SF/ExactConditionalSupport.lean | Sparse/IIDComparison/ExactConditionalSupport.lean | C | move | 325 |  |
| SF/ExactCoordinateSymmetry.lean | Sparse/IIDComparison/ExactCoordinateSymmetry.lean | C | move | 271 |  |
| SF/ExactConditionalBarycenter.lean | Sparse/IIDComparison/ExactConditionalBarycenter.lean | C | move | 196 |  |
| SF/ExactIIDMatrixError.lean | Sparse/IIDComparison/ExactIIDMatrixError.lean | C | move | 331 |  |
| SF/ExactConditionalMatrixTransfer.lean | Sparse/IIDComparison/ExactConditionalMatrixTransfer.lean | C | move | 242 |  |
| SF/ExactMomentTransfer.lean | Sparse/IIDComparison/ExactMomentTransfer.lean | C | move | 237 | unconditional_convex_order via the shared lemma (2k) |
| — | Sparse/IIDComparison/TraceMomentOrder.lean | C | new |  | sparse corollary conditional_traceEvenPower_order split from TracePowerConvexity |
| SF/Pattern.lean | Sparse/FockModel/OccupationPattern.lean | C | move | 241 | Level, Site, Pattern (+dot API) |
| SF/LocalOperators.lean | Sparse/FockModel/LadderMatrices.lean | C | move | 211 | Op -> LevelOp; Homogeneous -> IsGradeShift (2f) |
| SF/BandInventory.lean | Sparse/FockModel/LadderWords.lean | C | move | 347 | Leg, Word, Shift, Heaviness |
| SF/FiniteSiteOperators.lean | Sparse/FockModel/SiteKernels.lean | C | move | 258 | FockOp; Homogeneous/gradeZ -> IsGradeShift, Pattern.gradeZ |
| SF/ExternalOperators.lean | Sparse/FockModel/TensorOperators.lean | C | move | 123 | FullOp; outer -> vecMulVec; Homogeneous/gradeZ -> IsGradeShift, fullGradeZ |
| SF/FockHilbert.lean | Sparse/FockModel/FockSpace.lean | C | move | 356 | FullSpace, gradeProjection; normSq -> dotProduct; fiber family unified here as fockFiber |
| SF/TernaryJacobi.lean | Sparse/FockModel/TernaryJacobi.lean | C | move | 336 | EtaOutcome -> TernaryOutcome; law -> ternaryLaw; weightedInner/weightedONBasis -> ternaryWeightedInner/ternaryONBasis |
| SF/ProductFock.lean | Sparse/FockModel/ProductBasis.lean | C | move | 389 | Configuration; weightedInner/weightedONBasis -> productWeightedInner/productONBasis |
| SF/VacuumMoment.lean | Sparse/FockModel/VacuumMoment.lean | C | move | 190 | add module docstring |
| SF/GlobalBands.lean | Sparse/Bands/GlobalBands.lean | C | move | 325 |  |
| SF/NamedBands.lean | Sparse/Bands/NamedBands.lean | C | move | 234 | Physical abbrev deleted |
| SF/ConcreteLadder.lean | Sparse/Bands/Ladder.lean | C | move | 260 |  |
| SF/ConcreteLadderIteration.lean | Sparse/Bands/LadderIteration.lean | C | move | 425 | abs_entry_le_l2_opNorm -> NLAlib.abs_apply_le_specNorm (Matrix/Norms/EuclideanOperatorBounds) |
| SF/BandEnvelope.lean | Sparse/Bands/EnvelopeArithmetic.lean | C | move | 186 |  |
| SF/BandCoefficientBounds.lean | Sparse/Bands/CoefficientBounds.lean | C | move | 200 |  |
| SF/ScalarBounds.lean | Sparse/Bands/ScalarBounds.lean | C | move | 169 | two_mul_le_sq_add_sq -> Mathlib two_mul_le_add_sq |
| SF/ConcreteBandAssembly.lean | Sparse/Bands/BandAssembly.lean | C | move | 193 |  |
| SF/ConcreteBandEnvelope.lean | Sparse/Bands/BandEnvelope.lean | C | move | 112 | main band theorem (concrete_band_envelope) |
| SF/DirectionalBounds.lean | Sparse/Bands/Directional/OccupationProfiles.lean | C | move | 281 |  |
| SF/DirectionalSiteTransitions.lean | Sparse/Bands/Directional/SiteTransitions.lean | C | move | 340 | frameRows -> Frame.rows; sum_ordered_swap deleted |
| SF/DirectionalMarkedCoefficients.lean | Sparse/Bands/Directional/MarkedCoefficients.lean | C | move | 440 | fiber -> fockFiber; sum_erase_comm -> ForMathlib/Algebra/DiagonalSums |
| SF/DirectionalMarkedReindexing.lean | Sparse/Bands/Directional/MarkedReindexing.lean | C | move | 434 | fullFiber -> fockFiber; normSq_sum_le_card -> norm_sum_sq_le_card_mul (ForMathlib); sum_subtype_eq_filter -> Finset.sum_subtype_eq_sum_filter |
| SF/DirectionalOccupationEnergy.lean | Sparse/Bands/Directional/OccupationEnergy.lean | C | move | 317 |  |
| SF/DirectionalOutputEnergy.lean | Sparse/Bands/Directional/OutputEnergy.lean | C | move | 443 |  |
| SF/DirectionalRestrictedBounds.lean | Sparse/Bands/Directional/RestrictedBounds.lean | C | move | 197 |  |
| SF/DirectionalNormalized.lean | Sparse/Bands/Directional/NormalizedBands.lean | C | move | 354 | l2_norm_transpose -> specNorm_transpose / Matrix.l2_opNorm_conjTranspose; keeper of norm_normalized_directional_term_eq |
| SF/HeavyMarkedSites.lean | Sparse/Bands/Heavy/MarkedSites.lean | C | move | 344 |  |
| SF/HeavyAnalysisOperators.lean | Sparse/Bands/Heavy/AnalysisOperators.lean | C | move | 229 | fiber -> fockFiber (delete copy); fockNormSq -> dotProduct |
| SF/HeavyCreationEnergy.lean | Sparse/Bands/Heavy/CreationEnergy.lean | C | move | 118 |  |
| SF/HeavyDemotionEnergy.lean | Sparse/Bands/Heavy/DemotionEnergy.lean | C | move | 158 |  |
| SF/HeavyRowFactorization.lean | Sparse/Bands/Heavy/RowFactorization.lean | C | move | 251 | frameRows copy deleted -> Frame.rows; RowFock kept (single copy) |
| SF/HeavyGradeProjections.lean | Sparse/Bands/Heavy/GradeProjections.lean | C | move | 185 |  |
| SF/HeavyRaisingBound.lean | Sparse/Bands/Heavy/RaisingBound.lean | C | move | 233 | coordNormSq -> dotProduct; norm_transpose_real -> specNorm_transpose; matrix_norm_le_of_coord_energy -> Matrix/Norms |
| SF/HeavyLoweringBound.lean | Sparse/Bands/Heavy/LoweringBound.lean | C | move | 173 |  |
| SF/HeavyPreservingGram.lean | Sparse/Bands/Heavy/PreservingGram.lean | C | move | 256 |  |
| SF/HeavyDiagonalEnergy.lean | Sparse/Bands/Heavy/DiagonalEnergy.lean | C | move | 236 |  |
| SF/HeavyOccupationIdentity.lean | Sparse/Bands/Heavy/OccupationIdentity.lean | C | move | 187 |  |
| SF/HeavyPreservingBound.lean | Sparse/Bands/Heavy/PreservingBound.lean | C | move | 305 | quadratic -> quadForm (dotProduct_comm) |
| SF/HeavyNormalizedBands.lean | Sparse/Bands/Heavy/NormalizedBands.lean | C | move | 134 |  |
| SF/LightSectorAbstract.lean | Sparse/Bands/Light/AbstractContraction.lean | C | move | 166 | sum_erase_univ_eq_sub -> Finset.sum_erase_eq_sub |
| SF/LightOperators.lean | Sparse/Bands/Light/SharedLegOperators.lean | C | move | 379 | energy -> dotProduct; quadratic -> quadForm |
| SF/LightLabelledSlots.lean | Sparse/Bands/Light/LabelledSlots.lean | C | move | 283 |  |
| SF/LightCrossCoordinates.lean | Sparse/Bands/Light/CrossCoordinates.lean | C | move | 184 | coordinateEnergy -> dotProduct |
| SF/LightCrossContraction.lean | Sparse/Bands/Light/CrossContraction.lean | C | move | 308 |  |
| SF/LightGramQuadratic.lean | Sparse/Bands/Light/GramQuadratic.lean | C | move | 141 |  |
| SF/LightSynthesisBounds.lean | Sparse/Bands/Light/SynthesisBounds.lean | C | move | 446 | coordinateQuadratic -> quadForm |
| SF/LightPatternWords.lean | Sparse/Bands/Light/PatternWords.lean | C | move | 363 |  |
| SF/LightHardCoreEmbedding.lean | Sparse/Bands/Light/HardCoreEmbedding.lean | C | move | 278 |  |
| SF/LightLegalTransitions.lean | Sparse/Bands/Light/LegalTransitions.lean | C | move | 248 |  |
| SF/LightMoveOrbits.lean | Sparse/Bands/Light/MoveOrbits.lean | C | move | 243 |  |
| SF/LightOrbitCompression.lean | Sparse/Bands/Light/OrbitCompression.lean | C | move | 341 |  |
| SF/LightBlockDecomposition.lean | Sparse/Bands/Light/BlockDecomposition.lean | C | move | 241 |  |
| SF/LightGradeNorm.lean | Sparse/Bands/Light/GradeNorm.lean | C | move | 290 | coordinateEnergy_mulVec_le_of_norm_le -> Matrix/Norms (dotProduct form) |
| SF/LightZeroBlock.lean | Sparse/Bands/Light/ZeroBlock.lean | C | move | 110 |  |
| SF/LightRowFactorization.lean | Sparse/Bands/Light/RowFactorization.lean | C | move | 369 | RowFock abbrev deleted (use Heavy RowFock) |
| SF/LightAnalysisGram.lean | Sparse/Bands/Light/AnalysisGram.lean | C | move | 390 |  |
| SF/LightPreservingDiagonal.lean | Sparse/Bands/Light/PreservingDiagonal.lean | C | move | 421 |  |
| SF/LightMixedFactorization.lean | Sparse/Bands/Light/MixedFactorization.lean | C | move | 411 | DELETE the 12-lemma LightBandsConcrete block (Light/Mixed verbatim copies) |
| SF/LightNormalizedBands.lean | Sparse/Bands/Light/NormalizedBands.lean | C | move | 329 |  |
| SF/MixedRowFactorization.lean | Sparse/Bands/Mixed/RowFactorization.lean | C | move | 442 | keeper of the 12 Light/Mixed lemmas |
| SF/MixedRestrictedBounds.lean | Sparse/Bands/Mixed/RestrictedBounds.lean | C | move | 217 |  |
| SF/MixedNormalizedBands.lean | Sparse/Bands/Mixed/NormalizedBands.lean | C | move | 376 | norm_normalized_mixed_term_eq deleted (= Directional) |
| Sparse/SparseFock.lean | — | S | delete-aggregator | 118 | regenerated aggregators Sketching/Sparse/{MomentMethod,IIDComparison,FockModel,Bands}.lean and Bands/{Directional,Heavy,Light,Mixed}.lean replace it |