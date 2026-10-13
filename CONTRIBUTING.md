# Contributing

Use [`docs/STANDARDS.md`](docs/STANDARDS.md) as the current policy for mathematical statements,
names, files, and public API. Older briefs describe past decisions and migrations; they do not add
current requirements where they conflict with the standards. The [`atlas/TARGETING.md`](atlas/TARGETING.md)
guide offers advice for selecting and stating RandNLA work.

## 1. Find the right place

Search the local library and Mathlib before adding a declaration. Use the atlas to find existing
formalizations, dependencies, and likely downstream users. Add an atlas entry and `atlas:` tag
when formalizing a catalogued research result; helper lemmas and API bridges do not need an atlas
entry of their own.

The broad dependency layers are:

| Layer | Directory | May import |
|---|---|---|
| 0 | `NLAlib/Matrix/`, `NLAlib/Polynomial/` | Mathlib, `ForMathlib` |
| 1 | `NLAlib/Probability/`, `NLAlib/Krylov/` | layer 0 |
| 2 | `NLAlib/RandomMatrix/` | layers 0–1 |
| 3 | `NLAlib/Sketching/` | layers 0–2 |
| 4 | `NLAlib/LowRank/`, `NLAlib/Estimation/` | layers 0–3 |
| 5 | `NLAlib/Solvers/` | layers 0–4 |

Place content with its mathematical topic and dependencies. A `Basic.lean` file may contain
definitions, foundational API, and substantive theorems that naturally belong with those objects.
Use other topic files for developments that do not fit there. Follow existing aggregator-file
conventions when adding or moving modules.

## 2. State and prove the result

Read the cited source and settle the mathematical statement before optimizing for proof convenience.
Check domains, hypotheses, dimensions, constants, and degenerate cases. Do not weaken a theorem to
make it easier to prove. When a declaration describes a particular algorithm, establish its link
to the mathematical specification and say which cases and guarantees are covered.

Use Mathlib's standard objects where they fit and provide bridges for useful NLAlib adapters.
Choose generic or specialized index types according to the mathematics; `Fin` is suitable when its
structure supports an algorithm or proof. State actual probability laws and expectations where
they are useful, while retaining finite or bundled interfaces when they serve a real purpose.

Prefer a direct proof from existing results. Do not add axioms or use `native_decide`. A deferred
proof belongs in a named, documented scaffold whose trust status is recorded accurately. Cite the
source and explain meaningful differences from it in public declaration docstrings.

Unfinished proofs belong outside the default import. Register their module in
`scripts/experimental_modules.txt` and regenerate aggregators; the generator excludes its import
dependants too. `import NLAlib.Experimental` includes the full development. The strict default
audit checks every reachable declaration, while the complete audit and declaration index record
experimental proof dependencies. A helper need not become an artificial atlas result to record
its trust status.

## 3. Atlas and checks

For a new catalogued result, add its human-authored atlas entry, tag the formal statement in its
docstring, and synchronize the generated declaration index and atlas fields:

```sh
lake env lean scripts/ExtractDecls.lean
python3 scripts/sync_atlas.py
python3 scripts/check_atlas.py
```

Do not add atlas entries for routine helper lemmas or adapters. When changing a catalogued result,
keep its statement, status, dependencies, and usage information accurate.

Run the relevant module build and repository checks for the change. Before a pull request, the
standard checks are:

```sh
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

For changes to Ritz or subspace results, also run the focused checks in
`scripts/AuditRitz.lean` or `scripts/AuditSubspaces.lean`, as applicable.

## 4. Porting proofs

External Lean libraries may be used as proof sources, but are not package dependencies. Restate
the result using NLAlib and Mathlib interfaces, translate the proof, and preserve required
attribution and license notices.
