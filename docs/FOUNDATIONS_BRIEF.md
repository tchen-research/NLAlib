# Foundations brief: what this repository does before the move to `NLA-lib/NLAlib`

Written 2026-10-13 after a design review of the whole tree. Read this before `docs/STANDARDS.md`;
where they disagree, this file wins and STANDARDS is updated in the PR that makes the change.

## 0. What this repository is now

This checkout is no longer where the library grows. A fresh public repository
(`github.com/NLA-lib/NLAlib`) will be built by porting files from here, one area at a time,
against new infrastructure (Mathlib linters, headers, `mk_all`, doc-gen4). This repository has
two remaining jobs:

1. Land three **foundation changes** in the core, where CI and the full consumer set can verify
   them. They are F1, F2 and F3 below. Nothing else changes in Lean files here.
2. Produce the **port manifest** (§5) that tells the port which files to keep, merge, drop or
   rebuild.

### Freeze rules (apply to every agent and every PR here)

- No new theorems, definitions, files or atlas results, except what F1–F3 need.
- No generalisation of leaf files. If a leaf breaks because the core changed, fix the call site
  minimally; if a leaf is a `Complex*`/`Real*` twin of a core theorem that F1 makes generic,
  delete the twin and repoint its users.
- No cosmetic cleanup (renames for style, header additions, file splitting, option removal).
  All of that happens at port time in the new repository, and only for files that are ported.
- No work on `NLAlib/Sketching/Sparse/` beyond F3.
- One foundation change per PR. Each PR passes the full check list in §6.
- Before anything else: get `main` green. 178 files are newer than their oleans and 16 files
  (including the import hubs `Matrix/Norms/Core`, `Matrix/Norms/Frobenius`,
  `Matrix/Basic/Pseudoinverse`) are uncommitted. Build, fix, commit, then start F1.

## 1. F1: the matrix core over `RCLike` and `Fintype`

**Goal.** Every definition and theorem in the *spectral core* is stated once, over
`{𝕜 : Type*} [RCLike 𝕜]` and `{m n : Type*} [Fintype m] [Fintype n]` (plus `DecidableEq`
where Mathlib needs it). No `Fin` in layer 0, no ℝ-only or ℂ-only copy of a core theorem.

**The spectral core is exactly these files** (nothing else is in scope for F1):
`Matrix/Norms/{Frobenius,Core}.lean`, `Matrix/Subspaces/Projections.lean`,
`Matrix/Basic/{Pseudoinverse,PenroseIdentities,MoorePenrose*,QuadForm}.lean`,
`Matrix/Spectral/{Core,SVD,CourantFischer,Weyl,EckartYoung}.lean`, `Matrix/Inequalities/Mirsky.lean`,
and the `Complex*` twins of these (`ComplexVariationalPrinciple`, `ComplexRectangularSVD`,
`ComplexBestRankApproximation`, `ComplexGramTruncation`, `ComplexEckartYoung`, `ComplexVolumeSpectrum`,
`ComplexSingularTransport`, `RealComplexNorm`, `ComplexFrobenius`, `RealComplexCFC`,
`ComplexEmbedding`, `FiniteIndexTransport`).

**Decisions already made; do not reopen.**

- `IsSVD A U V` becomes `Fintype`-indexed. `rectDiag` becomes
  `rectDiag (σ : ℕ → ℝ) : Matrix m n 𝕜 := Matrix.of fun i j =>
  if (Fintype.equivFin m i : ℕ) = Fintype.equivFin n j then (σ (Fintype.equivFin m i) : 𝕜) else 0`,
  with a `@[simp]` lemma recovering today's `Fin` form. `exists_isSVD` is proved once over `𝕜`
  and `Fintype`. Then delete every private `*_fin` lemma, `FiniteIndexTransport.lean`, and
  `exists_complex_rectangular_svd`.
- Eckart–Young, Courant–Fischer, Weyl, Mirsky, interlacing: one statement each over `𝕜`.
  Delete the ℂ copies. Courant–Fischer gets an equational form a user can `rw` with
  (`eigenvalues₀ k = ⨆ … ⨅ …`) in addition to the two inequalities. Interlacing gets a
  principal-submatrix form (`A.submatrix e e`) as well as the compression form.
- Transpose twins (decision D1) are **removed**: a lemma is stated with `ᴴ`; real users get
  `ᵀ` through the simp lemma `Matrix.conjTranspose_eq_transpose_of_trivial`. Keep a
  `@[deprecated] alias` for each removed `ᵀ` name only if it is used outside the core; otherwise
  just delete and record in `docs/renames/2026-10-F1.json`.
- One spelling each. Frobenius: `frobSq`/`frobNorm`/`frobInner`, with a *generic* bridge
  `frobNorm_eq_norm` to Mathlib's `Matrix.frobeniusNormedAddCommGroup` in `Norms/Frobenius.lean`;
  delete `Norms/ComplexFrobenius.lean`. Smallest eigenvalue: Mathlib's
  `IsHermitian.eigenvalues₀` with index `card - 1` (delete `lamMin`; `lambdaMin` from the
  concentration layer is F2's problem and stays for now). Loewner order: `≤` under
  `open scoped MatrixOrder`; rewrite `(B - A).PosSemidef` hypotheses in the core files.
- `specNorm` drops the `[DecidableEq m] [DecidableEq n]` arguments if Mathlib's
  `instL2OpNormedAddCommGroup` does not need them (it does not); check nothing else forces them.
- Lemmas about `Matrix.IsHermitian`, `Matrix.PosSemidef` go in those namespaces so dot notation
  works (`hA.eigenvalues₀_add_le`). Only in the core files; leaves are repointed at port time.

**Acceptance.** All of these are zero after F1: `grep -rl "Matrix (Fin" NLAlib/Matrix/Spectral
NLAlib/Matrix/Norms NLAlib/Matrix/Subspaces/Projections.lean NLAlib/Matrix/Basic`;
`grep -rn "_fin\b" NLAlib/Matrix`; `ls NLAlib/Matrix/Spectral/Complex*` for the files listed
above. `grep -rl "ℂ" NLAlib/Matrix/Spectral` contains no file that has an ℝ sibling.

## 2. F2: random matrices live on `Matrix`, with one law interface

**Goal.** A random matrix is `X : Ω → Matrix m n 𝕜` with a `MeasurableSpace` instance on
`Matrix`, its law is stated with Mathlib's `HasLaw`, and `gaussianMatrix` is a measure on
`Matrix`. The ℝ Gaussian world and the ℂ concentration world share the same instance.

**Decisions already made; do not reopen.**

- New file `NLAlib/ForMathlib/MeasureTheory/Matrix.lean`:
  ```lean
  instance Matrix.instMeasurableSpace {m n α} [MeasurableSpace α] : MeasurableSpace (Matrix m n α) :=
    MeasurableSpace.pi
  instance Matrix.instBorelSpace {m n α} [Fintype m] [Fintype n] [TopologicalSpace α]
      [MeasurableSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
    Pi.borelSpace   -- check: the pi topology is the one Matrix carries, also under L2Operator
  ```
  plus `measurable_of`/`measurable_entry`, `Measurable.matrix_mul`, `measurable_conjTranspose`,
  `Matrix.of` as a `MeasurableEquiv`, and the bridge from entrywise measurability
  (`Matrix/Structured/Measurable.lean`), which then shrinks to corollaries. This is a global
  instance, not scoped: Mathlib has none, and this is the one Mathlib would add.
- Delete `matrixMeasurableSpace`/`matrixBorelSpace` in
  `Probability/Concentration/Basic/MatrixStatistics.lean` and the `orthogonalGroup` Borel
  instance in `Matrix/Subspaces/Stiefel.lean`; the concentration layer must build on the new
  instance unchanged (the σ-algebras are propositionally equal; expect `rfl` proofs about
  measurability to need `Measurable.of_comap_le`-style arguments in a few places).
- `gaussianMatrix (m n : Type*) [Fintype m] [Fintype n] : Measure (Matrix m n ℝ)` :=
  `(Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1).map Matrix.of` (or the pi measure
  on the Matrix type directly if the instance unfolds cleanly; pick the one whose basic API,
  entry law, independence of entries, moments, is shortest). The `Fin p`/`Fin m` version is the
  special case; no separate definition.
- The single law interface is `HasLaw X (gaussianMatrix m n) μ`
  (`Mathlib/Probability/HasLaw.lean`; fields `aemeasurable`, `map_eq`). Rewrite every
  `μ.map X = gaussianMatrix …` and every `μ.map (fun ω => Matrix.of.symm (G ω)) = …` hypothesis
  to it. `IsStandardGaussian`, `IsRademacher`: redefine as `HasLaw` with the named measure, or
  make them `abbrev`s of it. `IsGaussian`/`HasGaussianLaw` for vectors stay (they are Mathlib's).
- Theorems currently stated by integrating against `gaussianMatrix` directly (InverseMoments,
  Gordon, SpectralSecondMoment, Invariance, Wishart) keep that form as the *primary* statement
  (it is the most general), and get a `HasLaw` corollary in the same file, named
  `<name>_of_hasLaw`, so downstream never pushes forward by hand again. Delete the
  `_of_map_eq` wrappers.
- Tails: `μ.real s ≤ …` everywhere in files F2 touches. Do not chase the rest; record the
  convention in STANDARDS §3.
- Orthonormal hypotheses in `RandomMatrix` are `HasOrthonormalCols V`, not `Vᵀ * V = 1`.

**Acceptance.** `grep -rn "Matrix.of.symm" NLAlib` is zero outside
`ForMathlib/MeasureTheory/Matrix.lean`. `grep -rn "μ.map .* = gaussianMatrix\|\.map .* = gaussianMatrix" NLAlib`
is zero. `grep -rn "instance.*MeasurableSpace\|instance.*BorelSpace" NLAlib` finds only the two
instances in the new ForMathlib file. `grep -rn "_of_map_eq" NLAlib` is zero.

## 3. F3: the sparse-stack work, repointed

**Stop** integrating `Sketching/Sparse` cosmetically (bundles, names, `FiniteLaw` bridges). It
will be rebuilt in the new repository on `PMF`/`Measure` and on a sketch abstraction that does
not exist yet. The 28k lines stay here, untouched, as a quarry.

**Do** produce `docs/SKETCH_INTERFACE.md`, which answers, with file:line evidence:

1. What the OSE moment method needs from a sketch distribution, as a list of named hypotheses a
   `structure`/`class` could carry (e.g. a bound on `E tr (SᵀS − I)^{2q}` restricted to a
   `d`-dimensional subspace; isotropy `E SᵀS = I`; independence structure; sign symmetry).
   Say which of these Gaussian, SRHT, CountSketch, OSNAP and leverage sampling satisfy, with
   constants.
2. The three or four genuinely reusable lemmas inside Sparse, stated in library vocabulary
   (`IsSubspaceEmbedding`, `frobSq`, `specNorm`, Mathlib `PMF`), with their current names and
   lines: the Markov step from a trace-power moment to `IsSubspaceEmbedding`, trace-power
   convexity, the iid-versus-sparse comparison, and the net/union argument if there is one.
3. For every other file in `Sparse/`, one line: `rebuild` (needed for the two headline theorems)
   or `drop` (proof scaffolding specific to the port). The two headline theorems are
   `measure_sparseStack_embedding_success_ge` and `measure_uniformSparse_embedding_success_ge`.

**Also do**, in `Sketching/Properties/`, state (not necessarily prove) the single conclusion
shape every sketch theorem will target:
`μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U ε} ≤ δ`. Convert the Gaussian, CountSketch and SRHT
endpoints to it (SRHT currently stops at a Gram bound and never reaches `IsSubspaceEmbedding`).
Leverage sampling stays ℂ and is out of scope.

## 4. Things that are explicitly *not* this repository's job

Headers and licensing, Mathlib linters, `mk_all`, doc-gen4, deleting `*Toolkit.lean` and
`*_properties` bundles, Mathlib-style renames, file consolidation, removing file-level
`maxHeartbeats`/`respectTransparency`/`open Classical`, the Krylov executability question, the
sorry policy, splitting the atlas out, archiving the `ROUND*`/`DEDUP*`/`REORG*` briefs. All
of it happens in `NLA-lib/NLAlib` at port time. If you find yourself doing one of these here,
stop and note it in the manifest instead.

Exception: fix `scripts/sync_atlas.py` so a result is `proved` only if *every* non-partial
formalization is sorry-free (today three results show `proved` over sorried declarations). It is
a small change and the status is being read by people.

## 5. The port manifest

Deliver `docs/port/manifest.json`: one entry per Lean content file (aggregators excluded):

```json
{"module": "NLAlib.Matrix.Spectral.InterlacingReindex",
 "lines": 43, "action": "merge", "target": "NLAlib/Matrix/Spectral/Interlacing.lean",
 "field": "ℝ", "index": "Fin", "sorry": false,
 "note": "reindex transport; dies with F1"}
```

`action` is one of `keep` (port as a file, generalising at port time), `merge` (fold into
`target`, which should end up 300–500 lines), `drop` (bundle, twin, transport, or proof
scaffolding with no consumer), `rebuild` (Sparse, Solvers' finite-sum probability, anything
whose foundation changes). Draft it mechanically from the import graph, sizes and names, then
review the `drop`s by hand: a `drop` must name the file that makes it redundant. Target for the
whole tree: roughly a third of today's file count. This manifest is the port's work list and the
rename ledger's seed; it is the most valuable thing this repository produces after F1 and F2.

## 6. Checks for every PR

```
lake build
lake env lean scripts/Audit.lean          # sorries must be the catalogued scaffolds, no new ones
lake env lean scripts/ExtractDecls.lean && python3 scripts/sync_atlas.py
python3 scripts/check_layers.py && python3 scripts/check_names.py && python3 scripts/check_atlas.py
```

plus the F-specific `grep` acceptance lines above, pasted into the PR description, and the
STANDARDS.md edits that record the new convention (§3 index types and probability bullet, the
stale `Concentration/Matrix/Defs/Probability.lean` path, the D1 paragraph).

## 7. Order

Green `main` → F1 (one PR, or `Norms`+`Projections`+`Pseudoinverse` then `SVD`+spectral theorems
as two PRs if the diff is unreviewable) → F2 (ForMathlib instance PR first, then `gaussianMatrix`
+ `HasLaw` PR) → F3 and the manifest, which can run in parallel with F2 since they touch disjoint
files. When F1 and F2 are merged, this repository is frozen except for the manifest, and the port
begins in `NLA-lib/NLAlib`.
