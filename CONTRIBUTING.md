# Contributing

The library grows by pull requests, one result per PR. This file is the workflow; `docs/STANDARDS.md` is
the style contract (names, files, statements, docstrings, metadata) that CI enforces.

## 1. Pick a target

Read [`atlas/TARGETING.md`](atlas/TARGETING.md). Open an issue with the "Formalization target"
template titled with the atlas id, assign yourself, and set that result's `status` to `planned`
in `atlas/atlas.json` in your first PR (a one-line change is fine).

## 2. Where things go

| Layer | Directory | May import |
|---|---|---|
| 0 | `NLAlib/Matrix/`, `NLAlib/Polynomial/` | Mathlib, `ForMathlib` |
| 1 | `NLAlib/Concentration/`, `NLAlib/Krylov/` | layer 0 |
| 2 | `NLAlib/Gaussian/` | layers 0–1 |
| 3 | `NLAlib/Sketching/` | layers 0–2 |
| 4 | `NLAlib/LowRank/`, `NLAlib/Estimation/` | layers 0–3 |
| 5 | `NLAlib/Solvers/` | everything |

- **`Basic.lean` in each area holds definitions only** (plus the trivial lemmas that make them
  usable). It is the area's public interface. Theorem files import it.
- **One concept per file**, under about 500 lines. Name the file after the mathematics
  (`EckartYoung.lean`), not the source (`HornJohnson749.lean`).
- **Namespace `NLAlib`** everywhere, including the matrix concentration files under
  `NLAlib/Concentration/Matrix/` (ported from Tropp 2015; their theorem names keep a `chN_`
  prefix for now).

## 3. Statement conventions

The statement is the product; a proof can be replaced, a statement nobody can apply is wasted.

- Matrices are `Matrix (Fin m) (Fin n) ℝ` when a Gaussian law is involved (the product measure is
  over `Fin p → Fin m → ℝ`), and over `[Fintype ι]` index types when that costs nothing.
- Norms: `NLAlib.specNorm` (= Mathlib's ℓ₂ operator norm, bridge `specNorm_eq_norm`) and
  `NLAlib.frobSq` / `frobNorm` (explicit sums). Do not introduce another spelling.
- Gaussian matrices: `NLAlib.gaussianMatrix p m`; random objects on an abstract probability space
  `{Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]`, expectations as Bochner
  integrals.
- Order and functional calculus: `open scoped MatrixOrder`, `Matrix.PosSemidef`, `cfc`.
- Prefer Mathlib's definition. If you must define your own, ship the bridge lemma to Mathlib's
  notion in the same file.
- Every hypothesis explicit. No `axiom`, no `native_decide`. A cited fact you do not prove enters
  either as a named hypothesis of your theorem (atlas `status: assumed`) or as a named scaffold
  declaration with a `sorry` body and docstring `SCAFFOLD: <atlas id>` (atlas `status: scaffold`);
  never as a global assumption or an inline `sorry`.
- **Assuming is encouraged.** When we are confident of a theorem's statement (a textbook result,
  a published theorem with a clean formulation), scaffold or assume it and build downstream. The
  point of the atlas is to fill in the tree below an open node, not to block on the node. The
  accepted risk: if an assumed statement turns out wrong, every consumer below it is revisited;
  the dependency graph is what makes that propagation tractable. Spend the care on getting the
  *statement* right (source, label, degenerate cases, constants), not on avoiding the `sorry`.
- Constants explicit, never `∃ C`. Degenerate cases match the source (Mathlib's real division by
  zero is zero; write tail expressions piecewise where the source has a side condition).
- Give the general form, then corollaries. Two-sided results as two theorems.
- Docstring on every public declaration: the source and its label (`Horn–Johnson Thm 7.4.9.1`)
  and any deviation from the printed statement. A declaration that *is* the formal statement of
  an atlas result ends its docstring with a tag line `atlas: <id>` (several ids comma-separated;
  `atlas: <id> (partial)` for a declaration that covers only part of the statement, which is
  listed but does not make the result proved); helpers mention the id in prose but carry no tag. The tag is what puts the declaration in the
  atlas: `scripts/sync_atlas.py` rewrites each result's `formalizations`, its status and its
  `uses_defs` from the tags, so the Lean side of `atlas/atlas.json` is never edited by hand.

## 3a. Scaffolds: where `sorry` is allowed

A **scaffold** is a statement whose proof is deferred so that downstream results can be stated
and proved against it now. Rules:

- Every `sorry` lives in its own named declaration, never inline in a larger proof. Its docstring
  starts with `SCAFFOLD: <atlas id>` and says why the proof is deferred.
- The `SCAFFOLD: <atlas id>` docstring doubles as the atlas tag: after a sync the result has
  `status: "scaffold"` and a `formalizations` entry for the declaration with `status: "scaffold"`.
- A theorem proved only modulo scaffold lemmas is itself recorded as `scaffold` (its axioms
  include `sorryAx`). The audit lists every declaration that depends
  on `sorry`; `scripts/check_atlas.py` fails if one of them is catalogued as proved, or if a
  catalogued scaffold no longer depends on `sorry` (promote it).
- Scaffolds are for lower-level facts that are genuinely planned (a Gaussian moment, Eckart–Young),
  not for skipping the hard part of the result you are claiming.

## 4. Changing a definition

A change to any `Basic.lean` or to an existing public definition is an **api-change** PR: label
it, update every user in the same PR, and get two reviews. Deprecate rather than delete:
`@[deprecated (since := "YYYY-MM-DD")] alias old := new`, removed after one release.

## 5. Pull request checklist

- `lake build` passes with no new warnings.
- `lake env lean scripts/Audit.lean` reports no axioms beyond `propext`, `Classical.choice`, `Quot.sound`; every `sorry` it lists is a catalogued scaffold.
- `python3 scripts/check_layers.py` and `python3 scripts/check_atlas.py` pass.
- Every theorem that formalizes an atlas result carries its `atlas: <id>` tag, and
  `atlas/declarations.json` and `atlas/atlas.json` are regenerated
  (`lake env lean scripts/ExtractDecls.lean && python3 scripts/sync_atlas.py`). For a new result
  the hand-written entry (title, `informal`, `hypotheses`, `conclusion` in KaTeX, `sources`,
  `depends_on`, `aliases`, `variants`) is added to `atlas/atlas.json` first; the sync fills in
  the rest. Results whose statement is already in Mathlib are not atlas entries: cite the Mathlib
  declaration in the consumer's `mathlib_prereqs` instead.
- Read-back in the PR description: what the Lean statement says, written from the Lean alone.

CI runs all of this on every PR. A green CI plus one reviewer merges a theorem; two reviewers for
an api-change. Mathlib bumps are their own PRs, tagged as releases.

## 6. Porting from other Lean libraries

External libraries (HighDimProb, AI4SLT, …) are proof sources, not dependencies: the package
requires Mathlib only. Restate the result in our conventions, translate the proof, and cite the
library and commit in the docstring. All the libraries we port from are Apache-2.0; keep their
copyright line in the file header.

## 7. Migrations in flight

- The matrix concentration theorems still carry chapter-prefixed names (`ch3_…`, `ch8_…`);
  renaming them after the mathematics is a pending api-change.
- The LRA project (`One- and Two-Pass Algorithms for Low-Rank Approximation`) moves into
  `NLAlib/LowRank/` and `NLAlib/Gaussian/`, its Gaussian `Prop` hypotheses replaced by imports
  as the corresponding results land.
- The Gaussian Random Matrices I–III solutions (Prove2me workspace) move into `NLAlib/Gaussian/`.
