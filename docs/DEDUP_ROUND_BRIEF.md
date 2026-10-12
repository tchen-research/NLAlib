# Dedup round: brief for edit agents

You execute part of the merge plan produced by the review round (`docs/DEDUP_BRIEF.md`; findings in
the scratch `review_*.json` files). Your task file lists the findings you own, in full. Read every
finding before editing: they were written by reviewers who did not compile anything, so verify each
claim against the source before acting, and skip (and report) a finding that turns out to be wrong.

## Rules

1. **Ownership.** You may freely edit the files listed as yours. In any other file you may make only
   mechanical reference edits (replace a dropped name by its keeper, add or drop an `import`),
   re-reading the file immediately before each edit because other agents work concurrently. Never
   restructure, move or reprove anything in a file you do not own. If a finding needs more than
   that in a foreign file, do what you can and report the rest.
2. **Keep names stable where the plan says so.** A dropped declaration is deleted outright (no
   `deprecated` aliases: the library has no external users yet). Record every dropped name in your
   rename table `docs/renames/2026-10-12-dedup-<agent>.json` as `{"NLAlib.old": "NLAlib.keeper"}`
   (use the Mathlib name as the value when the keeper is in Mathlib; a definition replaced by an
   expression maps to a short description string).
3. **Atlas tags travel.** If a dropped declaration's docstring carries `atlas: <id>` or a
   `SCAFFOLD: <id>` line, move the tag (and the source citation) to the keeper's docstring; a keeper
   may carry several ids (comma-separated). Never edit `atlas/atlas.json`.
4. **Generalising a keeper** (Fin → Fintype, ℝ → RCLike/field): keep the body so that existing uses
   still elaborate, keep the name, update the docstring; then delete the losers.
5. **Moving a helper**: cut and paste verbatim (docstring included) into the target file, in a
   section that fits; fix imports at both ends; the target file must stay at or below the source's
   layer (`scripts/check_layers.py` rule: ForMathlib −1 · Matrix, Polynomial 0 · Probability,
   Krylov 1 · RandomMatrix 2 · Sketching 3 · LowRank, Estimation 4 · Solvers 5). Never edit a
   generated aggregator `<Dir>.lean`; if you create or delete a file, run
   `python3 scripts/reorg.py --gen-aggregators` (or note it in your report if the flag does not exist:
   the coordinator regenerates them).
6. **Conventions** (`docs/STANDARDS.md` §1–§4): Mathlib naming, one concept per file, docstrings on
   every public declaration, `Basic.lean` holds definitions and simp API only, imports are specific
   Mathlib files, `private` only for proof-local scaffolding, no `sorry`.
7. **Compiling.** Run at most one Lean process at a time. Check a single file with
   `lake env lean NLAlib/Path/File.lean` when its imports are unchanged; when you changed an
   upstream file, run `lake build NLAlib.Path.Module` for the specific modules you touched (and their
   direct dependants you know of). Never run a bare `lake build`, never `import Mathlib` in scratch
   files. Memory is shared with other agents: no parallel Lean processes.
8. **Done means compiled.** Every file you edited or that references a name you changed must compile
   before you report. If a dependant you did not own breaks on your change, fix the reference (rule 1)
   and compile it. If a proof adaptation is beyond reach, revert that finding and report it as
   skipped with the reason.

## Report

Append `docs/dedup/<agent>.md` with: findings executed (keeper, dropped names, files touched),
findings skipped and why, generalisations made, files created or deleted, anything the coordinator
must do (aggregators, atlas, follow-ups). Finish your final message with a short summary.
