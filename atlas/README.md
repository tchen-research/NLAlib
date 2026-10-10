# NLAlib Atlas

A catalogue of the reusable theorems of randomized numerical linear algebra, which of them
have been machine-checked in Lean 4 (and where), and how they depend on each other. The purpose
is to pick *foundations*: statements other people's arguments will cite, not end-to-end
algorithm guarantees. Algorithm guarantees appear only as `kind: "application"` consumers so
the graph shows what each foundation unlocks.

## Files

| File | What |
|---|---|
| `atlas.json` | The data. Four flat collections keyed by slug ids: `areas`, `results`, `sources`, `libraries`. |
| `schema.json` | JSON Schema (draft 2020-12) for `atlas.json`. Validate with `python3 -c "import json,jsonschema; jsonschema.validate(json.load(open('atlas.json')), json.load(open('schema.json')))"`. |
| `viewer.template.html` | The visualizer with `/*ATLAS_JSON*/` and `/*KATEX_CSS*/` placeholders. Statements are typeset with KaTeX (`$…$` inline, `$$…$$` display) when a result is opened. |
| `vendor/katex.inline.css` | KaTeX 0.16.11 stylesheet with its woff2 fonts inlined as data URIs, so the page needs no external stylesheet (generated; MIT). |
| `viewer.html` | Local build of the page (gitignored); `scripts/build_site.py` renders the deployed copy into `site/`. |

Rebuild the page:

```sh
python3 scripts/build_viewer.py   # atlas/viewer.html, the artifact mirror
python3 scripts/build_site.py     # site/index.html, deployed to GitHub Pages
```

## Data model

Designed so the same shape can live in a file today and in a shared database (one collection per
array, document id = slug) or on Prove2me later.

- **`areas`** — topic tree. `parent: null` for the top level, `order` for display, optional
  `priority` (`now` / `next` / `later`).
- **`results`** — one entry per statement or definition. Key fields:
  - `status`: `proved` (machine-checked and sorry-free in a listed library) ·
    `scaffold` (stated in NLAlib with a `sorry` proof, or proved only modulo scaffold lemmas) ·
    `assumed` (consumed as an explicit hypothesis by a proved result; like `scaffold`, a deliberate
    way to build downstream of a confidently stated but unproved theorem) ·
    `stated` (formal statement exists, proof open; Prove2me `Open`) ·
    `planned` (chosen target, not yet stated) · `candidate` (identified, not committed).
    The status is the atlas's judgement of the statement *as written*; an external library proving a
    variant is recorded under `formalizations` with its own status but does not promote the result.
  - `formalizations[]`: `{library, decl, module?, status, usage?, note?}`. **Generated for
    `library: nlalib`**: a declaration whose docstring ends with the tag line `atlas: <id>` is a
    formalization of that result (`atlas: <id> (partial)` lists it with `partial: true` without
    promoting the result), and `scripts/sync_atlas.py` rewrites these entries, the result's
    `status` and its `uses_defs` from `atlas/declarations.json` (`usage`/`note` are kept by
    declaration name). Entries for other libraries are hand-written. A statement that Mathlib
    already has is not a result of this atlas; consumers cite it under `mathlib_prereqs`.
  - `uses_defs[]`: generated; the NLAlib definitions occurring in the Lean statements.
  - `depends_on[]`: ids whose proofs this one consumes. In-degree of this graph is the reuse score
    the viewer ranks by.
  - `mathlib_prereqs[]`: `{decl, present, note?}` — what Mathlib has or lacks for this statement.
    `scripts/ExtractDecls.lean` writes the signatures of the cited Mathlib declarations to
    `atlas/external.json`, so the viewer shows their Lean statements too.
  - `sources[]`: `{source, label?}` into `sources`.
  - `kind`: `definition | lemma | theorem | bound | identity | algorithm | application`.
  - `difficulty` 1–5, `priority`, `tags`, `notes`, `updated_at`, `updated_by` (opaque id, never a name).
- **`sources`** — papers, books, surveys, repos, with `role` saying why they matter.
- **`libraries`** — Lean codebases, including Mathlib, with toolchain and Mathlib pins and `ours: bool`.

### Mapping to Prove2me

| Atlas | Prove2me |
|---|---|
| `result` with `status: stated` | theorem with `status: "Open"` |
| `result` with `status: proved` | theorem with `status: "Proved"` (or a local sorry-free build) |
| `depends_on` | the decomposition graph (`GET /theorems/:id/graph`), inverted |
| `formalizations[].prove2me_theorem_id` | `theorem_id` |
| top-level `area` | a mission series sharing a definition bundle and namespace |

### Conventions for ids

Lower-case kebab slugs, stable forever. Rename by adding a new id and leaving a `notes` pointer,
never by editing an existing id, so links from other people's documents keep working.

## Status today (2026-10-09)

110 results · 40 proved · 12 stated · 3 assumed · 55 candidates.
Proved work comes from three of our own libraries (Tropp Ch. 3–8, the Gaussian Random Matrices
series on Prove2me, the LRA project) plus Mathlib and HighDimProb.
