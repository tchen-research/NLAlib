## What this PR adds

- Atlas id(s): <!-- e.g. `eckart-young` -->
- Source and label: <!-- e.g. Horn–Johnson Thm 7.4.9.1 -->
- Kind: <!-- definition (Basic.lean change) / theorem / port from <library@commit> / infrastructure -->

## Read-back

<!-- One paragraph, in plain mathematics, of what the Lean statement says, written from the Lean alone. -->

## Checklist

- [ ] `lake build` passes with no new warnings
- [ ] `lake env lean scripts/Audit.lean` reports only propext / Classical.choice / Quot.sound
- [ ] `python3 scripts/check_layers.py` and `python3 scripts/check_atlas.py` pass
- [ ] `atlas/atlas.json` updated: `status`, `formalizations` (library `randnla`, full `decl` name), new `depends_on` edges, `updated_at`
- [ ] Docstring on every public declaration names the source item; deviations from the source are stated
- [ ] If this changes a `Basic.lean`: every user updated, label `api-change`, two reviewers
