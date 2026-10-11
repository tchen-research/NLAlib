# Book coverage round

Goal: for each book, a complete index of its numbered statements and, for every one, our status:
already in NLAlib, partially in NLAlib, in Mathlib, a candidate to add, or out of scope. The index
is the evidence behind "NLAlib covers this book"; it must be complete (every numbered theorem,
corollary, lemma, proposition, definition and observation; exercises only when they state a named
classical result) and honest (no `nlalib` without a declaration that states it).

Inputs (read-only): the extracted text of the book (path given per group; it is plain text from
`pdftotext -layout`, with OCR noise in Horn–Johnson: read around each label with `grep -n` and
`sed -n`, never the whole file at once), `atlas/atlas.json` (results with `sources[].label`, so grep
the source id to see what the atlas already cites), `atlas/declarations.json` (every NLAlib
declaration with signature and docstring; grep it before claiming coverage), `atlas/external.json`,
and Mathlib under `.lake/packages/mathlib/Mathlib` (grep it before claiming `mathlib`).

## Statuses
- `nlalib`: an NLAlib declaration states the result as printed (same generality up to real vs
  complex scalars, same or stronger conclusion). Give the atlas id(s) and the declaration name(s).
- `partial`: NLAlib has a special case or one direction. Say in `note` exactly what is missing.
- `mathlib`: Mathlib states it (declaration name required; grep to confirm). By project policy a
  statement that is in Mathlib is not an atlas result, but it still counts as covered.
- `candidate`: relevant to randomized NLA foundations and absent from both. Also write a
  candidate atlas entry for it (see Output 2) with the exact label.
- `out-of-scope`: not something this library will state (purely combinatorial, Perron–Frobenius,
  Jordan form over ℂ, historical remarks, complex-analytic machinery with no NLA consumer, …).
  `note` gives the reason in a few words. Be strict about `out-of-scope`: when in doubt it is a
  low-priority `candidate` with `priority: later`.

## Output 1: `docs/coverage/<file>.json`
```json
{"source": "<atlas source id>", "edition_note": "which edition/PDF, numbering caveats",
 "items": [{"label": "Thm 4.3.17", "kind": "theorem", "chapter": "4.3", "page": 242,
            "name": "Cauchy interlacing", "statement": "one or two sentences, paraphrased, with the hypotheses",
            "status": "nlalib", "atlas": ["cauchy-interlacing"], "decls": ["NLAlib.eigenvalues₀_submatrix_le"],
            "note": ""}]}
```
Labels: `Thm`, `Cor`, `Lem`, `Prop`, `Def`, `Obs`, `Ex` + the book's number, exactly as numbered.
`statement` is a paraphrase in your words (KaTeX allowed), never copied text. Validate with
`python3 scripts/coverage.py <source>`; it must print no problems (it checks atlas ids, declaration
names and the required fields, and writes the Markdown report).

## Output 2: `docs/coverage/<file>.candidates.json`
`{"results": [...], "sources": [...]}` in the format of `docs/TARGETS_ROUND7_BRIEF.md` (atlas
schema, `status: "candidate"`, `sources: [{"source": "<id>", "label": "<label>"}]`, `depends_on`
existing ids, `difficulty`, `priority`, `notes` with the consumer), one entry per candidate item
(group closely related items into one entry when the book itself treats them together, and list
every label in `sources`). Ids must not collide with existing atlas ids.

## Rules
- Do not edit Lean files or `atlas/atlas.json`; write only your two output files.
- Work chapter by chapter; keep a running count; finish the whole book (completeness is the point).
  If a chapter is entirely out of scope, still list its items with a one-line reason each (a
  shared reason is fine).
- Never mark `nlalib` from memory: cite the declaration you found in `declarations.json`.
- Final message: path of the two files, the per-chapter counts by status, the ten most valuable
  candidates, and any atlas label for this source that the index shows to be wrong.
