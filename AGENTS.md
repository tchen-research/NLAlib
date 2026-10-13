# Instructions for agents working in this repository

Read `docs/STANDARDS.md`, `CONTRIBUTING.md` and `atlas/TARGETING.md` first.

## Finding what exists

- `atlas/declarations.json` (generated): every public declaration with `name`, `kind`, `module`,
  `line`, `signature`, `doc`, `sorry`. Search it before proving anything:
  `python3 -c "import json;[print(x['name'],'::',x['signature'].replace(chr(10),' ')) for x in json.load(open('atlas/declarations.json')) if 'pinv' in x['name']]"`.
  Regenerate after a build with `lake env lean scripts/ExtractDecls.lean` (CI checks it is current).
- `atlas/atlas.json`: results with `aliases`, `hypotheses`, `conclusion`, `uses_defs` (the
  definitions a statement is written with), `formalizations[].usage` (how to apply the Lean
  declaration), `depends_on`, `variants`. `docs/llms.txt` summarises the conventions.
- Mathlib: `rg "theorem name" .lake/packages/mathlib/Mathlib`, `exact?`, `apply?`.

Then:

1. **Check a single file** while iterating (fast): `lake env lean NLAlib/<Area>/<File>.lean`.
   Imports of other `NLAlib` modules need their `.olean`, so run `lake build NLAlib.<Area>.<Mod>`
   for those first. Do not run a full `lake build` while another agent is building in the same
   checkout (the build lock serialises you).
2. **Before opening a PR**, run in order:
   ```
   lake build NLAlib NLAlib.Experimental
   python3 scripts/import_surface.py --check
   lake env lean scripts/AuditTrusted.lean
   lake env lean scripts/Lint.lean
   lake env lean scripts/Audit.lean
   lake env lean Examples/Downstream.lean
   lake env lean Examples/Probability.lean
   python3 scripts/check_layers.py
   python3 scripts/check_names.py
   python3 scripts/check_atlas.py
   ```
   All checks must pass. Paste the audit output into the PR.
3. **Search before defining.** `rg "theorem foo" .lake/packages/mathlib/Mathlib` and
   `exact?` / `apply?` / `rw?` in a scratch file. If Mathlib has it, use it; if an area
   `Basic.lean` has it, import it; otherwise prove a small lemma in your own file.
4. **Never** add an `axiom`, use `native_decide`, or weaken a statement to make it provable.
   `sorry` is allowed only in a named scaffold declaration (docstring `SCAFFOLD: <atlas id>`),
   catalogued in the atlas with `status: "scaffold"` and excluded from the default import;
   see CONTRIBUTING §2. The declaration index records the transitive status of all helpers.
5. **Tag and sync the atlas** for catalogued results: the declaration that formalizes a result ends its
   docstring with `atlas: <id>`; for a new result write the hand side of the `atlas/atlas.json`
   entry (title, `informal`, `hypotheses`, `conclusion`, `sources`, `depends_on`, `aliases`,
   `variants`). Then `lake env lean scripts/ExtractDecls.lean && python3 scripts/sync_atlas.py`
   (fills `formalizations`, `status`, `uses_defs` from the tags) and `python3 scripts/check_atlas.py`.
   A `usage` sentence on a formalization is hand-written and survives the sync.
6. **Style**: `noncomputable section` where needed, Mathlib naming conventions, and docstrings
   citing the source label and atlas id when applicable. Use NLAlib's domain namespaces for its
   objects and Mathlib's owning namespaces for extensions to Mathlib objects. `autoImplicit` is off.
