# Book coverage

One index per book (`<source>.json`, one record per numbered statement, paraphrased), the report it generates (`<source>.md`: theorem number, summary, status, atlas id / declaration), and the candidate entries it produced (`<source>.candidates.json`, merged into the atlas). Built by `scripts/coverage.py` from the extracted text of the books (not in the repo); process in `docs/COVERAGE_BRIEF.md`.

Statuses: **nlalib** an NLAlib declaration states it · **partial** a special case or one direction (note says what is missing) · **mathlib** Mathlib states it (covered, but by policy not an atlas result) · **candidate** relevant and absent, now an atlas entry with the book label · **out of scope** with a reason.

| book | items | nlalib | partial | mathlib | candidate | out of scope | report |
|---|---|---|---|---|---|---|---|
| Horn & Johnson, *Matrix Analysis* (2nd ed., 2013) | 607 | 39 | 44 | 166 | 159 | 199 | [`hj13.md`](hj13.md) |
| Trefethen, *Approximation Theory and Approximation Practice* (2013/2019) | 88 | 8 | 8 | 11 | 34 | 27 | [`trefethen19.md`](trefethen19.md) |
| Gautschi, *Orthogonal Polynomials: Computation and Approximation* (2004) | 131 | 2 | 22 | 2 | 64 | 41 | [`gautschi04.md`](gautschi04.md) |

"Covered" = nlalib + partial + mathlib; the candidate column is the queue, ranked inside each report and in the atlas by `priority`. A statement that appears in several books is one atlas entry with every book's label under `sources` (the merge dedupes by id and title).

## Reading the per-book reports

Each report is grouped by chapter with a status tally in the heading; the table gives the label as the book numbers it, a one-line paraphrase, the status glyph, the atlas ids and the first declarations, and a note (what is missing for partial items, the reason for out-of-scope ones). Entries whose atlas label the index could not match are listed at the end of the report for verification.

## Conventions

- Labels: `Thm 4.3.17`, `Cor 7.3.5`, `Lem`, `Prop`, `Def`, `Obs`, `Ex` (exercise stating a named result), `§0.6.5` (unnumbered passages), `Alg. 2.5`.
- Real vs complex: NLAlib proves the real-symmetric form of Hermitian statements; that counts as `nlalib` with the scalar field noted where it matters.
- Gautschi's general-measure theory is stated in NLAlib only for the spectral measure of a vector (finitely supported); those items are `partial` until the general-measure layer exists (`orthogonal-polynomials-measure-def` and its dependents).

## Adding a book

`pdftotext -layout book.pdf book.txt` (keep the PDF and text outside the repo), add the source to `atlas/atlas.json`, run a coverage agent per ~300 statements with `docs/COVERAGE_BRIEF.md`, merge the candidates, run `python3 scripts/coverage.py`.
