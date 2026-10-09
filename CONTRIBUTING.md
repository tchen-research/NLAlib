# Contributing

The library grows by pull requests, one result per PR. This file is the contract: how code is
laid out, how statements are written so they compose, and what CI checks.

## 1. Pick a target

Read [`atlas/TARGETING.md`](atlas/TARGETING.md). Open an issue with the "Formalization target"
template titled with the atlas id, assign yourself, and set that result's `status` to `planned`
in `atlas/atlas.json` in your first PR (a one-line change is fine).

## 2. Where things go

| Layer | Directory | May import |
|---|---|---|
| 0 | `NLAlib/Matrix/` | Mathlib only |
| 1 | `NLAlib/Concentration/`, `TroppMatrixConcentration/` | layer 0 |
| 2 | `NLAlib/Gaussian/` | layers 0–1 |
| 3 | `NLAlib/Sketching/` | layers 0–2 |
| 4 | `NLAlib/LowRank/`, `NLAlib/Estimation/`, `NLAlib/Krylov/` | layers 0–3 |
| 5 | `NLAlib/Solvers/` | everything |

- **`Basic.lean` in each area holds definitions only** (plus the trivial lemmas that make them
  usable). It is the area's public interface. Theorem files import it.
- **One concept per file**, under about 500 lines. Name the file after the mathematics
  (`EckartYoung.lean`), not the source (`HornJohnson749.lean`).
- **Namespace `NLAlib`** everywhere. `TroppMatrixConcentration` keeps its namespace; new code
  in that directory is discouraged, put real-matrix specialisations in `NLAlib/Concentration/`.

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
- Every hypothesis explicit. No `axiom`, no `sorry`, no `native_decide`. A cited fact you do not
  prove enters as a named hypothesis of your theorem, never as a global assumption; record it in
  the atlas as `status: assumed`.
- Constants explicit, never `∃ C`. Degenerate cases match the source (Mathlib's real division by
  zero is zero; write tail expressions piecewise where the source has a side condition).
- Give the general form, then corollaries. Two-sided results as two theorems.
- Docstring on every public declaration: the source and its label (`Horn–Johnson Thm 7.4.9.1`),
  the atlas id, and any deviation from the printed statement.

## 3a. Scaffolds: where `sorry` is allowed

A **scaffold** is a statement whose proof is deferred so that downstream results can be stated
and proved against it now. Rules:

- Every `sorry` lives in its own named declaration, never inline in a larger proof. Its docstring
  starts with `SCAFFOLD: <atlas id>` and says why the proof is deferred.
- The atlas entry has `status: "scaffold"` and a `formalizations` entry with
  `library: "nlalib"`, the full declaration name and `status: "scaffold"`.
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
- `atlas/atlas.json` updated for every result touched: `status`, a `formalizations` entry with
  `library: "nlalib"` and the full declaration name, new `depends_on` edges, `updated_at`.
- Read-back in the PR description: what the Lean statement says, written from the Lean alone.

CI runs all of this on every PR. A green CI plus one reviewer merges a theorem; two reviewers for
an api-change. Mathlib bumps are their own PRs, tagged as releases.

## 6. Porting from other Lean libraries

External libraries (HighDimProb, AI4SLT, …) are proof sources, not dependencies: the package
requires Mathlib only. Restate the result in our conventions, translate the proof, and cite the
library and commit in the docstring. All the libraries we port from are Apache-2.0; keep their
copyright line in the file header.

## 7. Migrations in flight

- The LRA project (`One- and Two-Pass Algorithms for Low-Rank Approximation`) moves into
  `NLAlib/LowRank/` and `NLAlib/Gaussian/`, its Gaussian `Prop` hypotheses replaced by imports
  as the corresponding results land.
- The Gaussian Random Matrices I–III solutions (Prove2me workspace) move into `NLAlib/Gaussian/`.
