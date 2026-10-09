# Instructions for agents working in this repository

Read `CONTRIBUTING.md` and `atlas/TARGETING.md` first. Then:

1. **Check a single file** while iterating (fast): `lake env lean NLAlib/<Area>/<File>.lean`.
   Imports of other `NLAlib` modules need their `.olean`, so run `lake build NLAlib.<Area>.<Mod>`
   for those first. Do not run a full `lake build` while another agent is building in the same
   checkout (the build lock serialises you).
2. **Before opening a PR**, run in order:
   ```
   lake build
   lake env lean scripts/Audit.lean
   python3 scripts/check_layers.py
   python3 scripts/check_atlas.py
   ```
   All four must pass. Paste the audit output into the PR.
3. **Search before defining.** `grep -rn "theorem foo" .lake/packages/mathlib/Mathlib` and
   `exact?` / `apply?` / `rw?` in a scratch file. If Mathlib has it, use it; if an area
   `Basic.lean` has it, import it; otherwise prove a small lemma in your own file.
4. **Never** leave `sorry`, add an `axiom`, use `native_decide`, or weaken a statement to make
   it provable. If stuck, open the PR as draft with the `sorry` clearly marked and listed in the
   description.
5. **Update the atlas** (`atlas/atlas.json`) in the same PR: status, formalization entry with the
   full declaration name, new dependency edges. `scripts/check_atlas.py` verifies the declaration
   exists.
6. **Style**: `noncomputable section`, `namespace NLAlib`, Mathlib naming conventions,
   docstrings citing the source label and atlas id, `autoImplicit` is off.
