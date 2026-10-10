#!/usr/bin/env python3
"""Sync the Lean side of atlas/atlas.json from the generated declaration index.

Lean is the source of truth for *which declarations formalize which result*: a declaration whose
docstring carries an `atlas: <id>, <id>` line (or starts with `SCAFFOLD: <id>`) is a formalization
of those results. This script rewrites, for every result,
  * `formalizations` with library `nlalib` (one per tagged declaration; `usage`/`note` written by
    hand are kept, keyed by declaration name; formalizations of other libraries are untouched),
  * each such formalization's `status` (`proved` if sorry-free, `scaffold` if it depends on sorry
    and its docstring starts with `SCAFFOLD:`, `stated` otherwise) and `partial: true` when the
    tag reads `atlas: <id> (partial)` (the declaration covers only part of the statement),
  * the result's `status` (`proved` / `scaffold` / `stated` from its non-partial NLAlib
    formalizations; a result with none keeps its hand-set `candidate` / `planned` / `assumed`),
  * `uses_defs`: the NLAlib definitions occurring in the statements of its formalizations.
The human-written fields (title, informal statement, hypotheses, sources, depends_on, …) are
never touched. Run after `lake env lean scripts/ExtractDecls.lean`.

  python3 scripts/sync_atlas.py          # rewrite atlas/atlas.json, print the changes
  python3 scripts/sync_atlas.py --check  # exit 1 if a rewrite would change anything
"""
import datetime, json, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ATLAS = ROOT / "atlas/atlas.json"
check = "--check" in sys.argv
atlas = json.load(open(ATLAS))
decls = json.load(open(ROOT / "atlas/declarations.json"))
by_id = {r["id"]: r for r in atlas["results"]}
errors, changes = [], []

# id -> [declaration records], in source order
tagged = {}
for d in decls:
    for i in d["atlas"]:
        if i not in by_id:
            errors.append(f"{d['name']} ({d['module']}:{d['line']}): unknown atlas id `{i}`")
            continue
        tagged.setdefault(i, []).append(d)
if errors:
    print("sync problems:\n  " + "\n  ".join(errors)); sys.exit(1)

def f_status(d):
    if not d["sorry"]: return "proved"
    return "scaffold" if d["doc"].lstrip().startswith("SCAFFOLD") else "stated"

is_def = {d["name"] for d in decls if d["kind"] in ("def", "inductive", "opaque", "axiom")}
today = datetime.date.today().isoformat()
for r in atlas["results"]:
    old = {f["decl"]: f for f in r["formalizations"] if f["library"] == "nlalib" and f.get("decl")}
    others = [f for f in r["formalizations"] if not (f["library"] == "nlalib" and f.get("decl"))]
    ds = sorted(tagged.get(r["id"], []), key=lambda d: (d["module"], d["line"]))
    new = []
    for d in ds:
        f = {"library": "nlalib", "decl": d["name"], "module": d["module"], "status": f_status(d)}
        if r["id"] in d.get("atlas_partial", []): f["partial"] = True
        for k in ("usage", "note"):
            if k in old.get(d["name"], {}): f[k] = old[d["name"]][k]
        new.append(f)
    forms = new + others
    sts = {f["status"] for f in new if not f.get("partial")}
    status = r["status"]
    if "proved" in sts: status = "proved"
    elif "scaffold" in sts: status = "scaffold"
    elif "stated" in sts: status = "stated"
    elif r["status"] in ("proved", "scaffold", "stated"):
        status = "candidate"   # lost its Lean side: nothing tagged any more
    uses = sorted({u for d in ds for u in d["uses"] if u in is_def})
    diff = []
    if forms != r["formalizations"]:
        dropped = sorted(set(old) - {d["name"] for d in ds}); added = sorted({d["name"] for d in ds} - set(old))
        diff.append("formalizations" + (f" +{added}" if added else "") + (f" -{dropped}" if dropped else ""))
    if status != r["status"]: diff.append(f"status {r['status']} → {status}")
    if uses != sorted(r.get("uses_defs", [])): diff.append("uses_defs")
    if diff:
        changes.append(f"{r['id']}: " + ", ".join(diff))
        r["formalizations"], r["status"], r["uses_defs"], r["updated_at"] = forms, status, uses, today
    if not new and others and r["status"] == "proved":
        errors.append(f"{r['id']}: proved only in another library; a result needs an NLAlib declaration or a non-proved status")

if changes: print("changes:\n  " + "\n  ".join(changes))
if errors: print("sync problems:\n  " + "\n  ".join(errors))
if check:
    if changes or errors: print("atlas is out of sync with the Lean sources: run scripts/sync_atlas.py"); sys.exit(1)
    print("atlas in sync"); sys.exit(0)
if changes:
    with open(ATLAS, "w") as fh: json.dump(atlas, fh, ensure_ascii=False, indent=1); fh.write("\n")
print(f"synced {len(tagged)} tagged results, {sum(len(v) for v in tagged.values())} formalizations; {len(changes)} results changed")
sys.exit(1 if errors else 0)
