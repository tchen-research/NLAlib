# Round 1 brief for proof agents

Repository: `/home/tyler/Documents/prove2me/lean` (package `NLAlib`, Lean v4.33.1, Mathlib pinned;
Mathlib and all current modules are already built). Read `CONTRIBUTING.md` §2–§3 and `AGENTS.md`
first. Then the files named in your task.

## Hard rules
- Work ONLY in the files your task names. Do not edit other files (several agents work in parallel).
  Helper lemmas you need go in your own file; note in your report which ones belong in `Basic.lean`.
- Do not edit `atlas/atlas.json` (the coordinator does it from your report).
- Do not run a full `lake build`. Check single files with
  `cd /home/tyler/Documents/prove2me/lean && lake env lean NLAlib/<Area>/<File>.lean`
  (10–30 s per run; importing Mathlib is the cost). If a file you wrote imports another file you
  wrote, run `lake build NLAlib.<Area>.<Module>` for the imported one once; if Lake reports a lock
  held by another process, wait and retry.
- No `axiom`, no `native_decide`, no new instances that could be unsound. `sorry` is allowed ONLY
  for statements your task marks as scaffold, and every `sorry` must be in its own named
  declaration (never inline inside a larger proof), with docstring `SCAFFOLD: <atlas id>` and the
  mathematical reason it is deferred. A proved theorem may use a scaffold lemma.
- Conventions: `noncomputable section`, `namespace NLAlib`, `open scoped Matrix`, real matrices,
  `NLAlib.frobSq/frobNorm/frobInner/specNorm` from `NLAlib.Matrix.Norms`, `HasOrthonormalCols`,
  `residual`, `IsBestRankApprox` from `NLAlib.Matrix.Projections`, `pinvL/pinvR` from
  `NLAlib.Matrix.Pseudoinverse`, `gaussianMatrix` from `NLAlib.Gaussian.Basic`. Import the
  specific Mathlib files you need; `import Mathlib` is acceptable if you cannot find them quickly.
- Docstring on every public declaration: the source and label (e.g. "HMT 2011, Thm 9.1") and the
  atlas id. State deviations from the printed statement.
- Mathlib search: `grep -rn "theorem name" .lake/packages/mathlib/Mathlib`, and `exact?`,
  `apply?`, `rw?`, `simp?` in a scratch file under `/tmp`.
- Finish within your budget: a smaller set of fully proved, cleanly stated results beats a large
  set of half-finished ones. If a proof is not closing, convert that step into a named scaffold
  lemma with `sorry` and move on, and say so in the report.

## Report (your final message)
1. Files written/changed.
2. Every public declaration: full name, one-line statement, status `proved` or `scaffold`
   (contains sorry) or `uses-scaffold` (proved modulo named scaffold lemmas it invokes), the atlas
   id it realises, and the atlas ids of results its proof invokes (these become dependency edges).
3. Exact check command(s) run and the final output (no errors; warnings fine).
4. Helper lemmas that should move to a `Basic.lean`, and anything you noticed about Mathlib
   (names that exist, names that are missing).
