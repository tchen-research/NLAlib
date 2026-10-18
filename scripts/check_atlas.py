#!/usr/bin/env python3
"""Atlas consistency. Validates atlas/atlas.json against the schema, checks referential integrity,
and checks that every formalization marked `proved` or `stated` in one of this repo's libraries
names a declaration that exists in the Lean sources."""
import json, pathlib, re, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
atlas = json.loads((ROOT / "atlas/atlas.json").read_text(encoding="utf-8"))
errors = []
try:
    import jsonschema
    jsonschema.validate(atlas, json.loads((ROOT / "atlas/schema.json").read_text(encoding="utf-8")))
except ImportError:
    print("note: jsonschema not installed, skipping schema validation")
except Exception as e:
    errors.append(f"schema: {e.message if hasattr(e, 'message') else e}")
ids = {r["id"] for r in atlas["results"]}
areas = {a["id"] for a in atlas["areas"]}
srcs = {s["id"] for s in atlas["sources"]}
libs = {l["id"]: l for l in atlas["libraries"]}
LOCAL = {l["id"] for l in atlas["libraries"] if l.get("repo_dir")}
decls = set()
for f in ROOT.glob("NLAlib/**/*.lean"):
    ns = []
    for line in f.read_text(encoding="utf-8").splitlines():
        m = re.match(r"\s*namespace\s+([\w.]+)", line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r"\s*end\s+([\w.]+)\s*$", line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = re.match(r"\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?(?:theorem|lemma|def|abbrev|instance|structure)\s+([\w.']+)", line)
        if m:
            name = m.group(1)
            decls.add(".".join(ns + [name]) if ns else name)
            decls.add(name)
index_file = ROOT / "atlas/declarations.json"
index = {}
if index_file.exists():
    index = {x["name"]: x for x in json.loads(index_file.read_text(encoding="utf-8"))}
    decls |= set(index)   # exact names from the generated index take precedence
else:
    errors.append("atlas/declarations.json is missing: run ExtractDecls.lean")
for r in atlas["results"]:
    for v in r.get("variants", []):
        if v not in ids: errors.append(f"{r['id']}: unknown variant {v}")
    if r["area"] not in areas: errors.append(f"{r['id']}: unknown area {r['area']}")
    for d in r["depends_on"]:
        if d not in ids: errors.append(f"{r['id']}: unknown dependency {d}")
    for s in r["sources"]:
        if s["source"] not in srcs: errors.append(f"{r['id']}: unknown source {s['source']}")
    for f in r["formalizations"]:
        if f["library"] not in libs: errors.append(f"{r['id']}: unknown library {f['library']}"); continue
        if f["library"] in LOCAL and f.get("decl") and f["status"] in ("proved", "stated"):
            d = f["decl"]
            if d not in decls and not any(x.startswith(d + ".") or x.endswith("." + d) for x in decls):
                errors.append(f"{r['id']}: declaration not found in sources: {d}")
    st = {f["status"] for f in r["formalizations"]}
    if r["status"] == "proved" and "proved" not in st:
        errors.append(f"{r['id']}: status proved but no proved formalization listed")
    if r["status"] == "scaffold" and not any(f["library"] in LOCAL and f["status"] == "scaffold" for f in r["formalizations"]):
        errors.append(f"{r['id']}: status scaffold but no scaffold formalization in this repo listed")
# Every public descendant is visible in the declaration index, even when it is a
# helper rather than a separately catalogued mathematical result.
surface_file = ROOT / "atlas/import_surface.json"
excluded = set()
if surface_file.exists():
    excluded = set(json.loads(surface_file.read_text(encoding="utf-8"))["excluded_modules"])
else:
    errors.append("atlas/import_surface.json is missing: regenerate aggregators")
for name, declaration in index.items():
    if declaration["sorry"] and declaration["module"] not in excluded:
        errors.append(f"{name}: sorry-dependent declaration is exposed by the default import")
# An audit is required; a missing output cannot silently disable the trust check.
sorry_file = ROOT / ".lake/sorries.txt"
if sorry_file.exists():
    sorried = {l.strip() for l in sorry_file.read_text(encoding="utf-8").splitlines() if l.strip()}
    scaffold_decls = {f["decl"] for r in atlas["results"] for f in r["formalizations"]
                      if f["library"] in LOCAL and f["status"] == "scaffold" and f.get("decl")}
    proved_decls = {f["decl"] for r in atlas["results"] for f in r["formalizations"]
                    if f["library"] in LOCAL and f["status"] == "proved" and f.get("decl")}
    for d in sorried:
        if d in proved_decls:
            errors.append(f"{d} is listed as proved in the atlas but depends on sorry")
    for d in scaffold_decls:
        if d not in sorried:
            errors.append(f"{d} is listed as scaffold in the atlas but no longer depends on sorry: promote it")
    indexed_sorries = {name for name, d in index.items() if d["sorry"]}
    for name in (sorried & set(index)) ^ indexed_sorries:
        errors.append(f"{name}: audit and declaration index disagree about sorry dependency")
    for name in sorried - set(index):
        errors.append(f"{name}: audited sorry-dependent public theorem is absent from the index")
    for name in indexed_sorries:
        d = index[name]
        if d["doc"].lstrip().startswith("SCAFFOLD:") and name not in scaffold_decls:
            errors.append(f"{name}: direct scaffold has no atlas scaffold entry")
    direct_file = ROOT / ".lake/direct-sorries.txt"
    if direct_file.exists():
        for name in direct_file.read_text(encoding="utf-8").splitlines():
            if name and name not in scaffold_decls:
                errors.append(f"{name}: direct sorry must be a named, catalogued scaffold")
    else:
        errors.append(".lake/direct-sorries.txt is missing: run scripts/Audit.lean")
    print(f"experimental proof inventory: {len(indexed_sorries)} sorry-dependent declarations "
          "indexed and excluded from the default import")
else:
    errors.append(".lake/sorries.txt is missing: run scripts/Audit.lean")
if errors:
    print("Atlas problems:\n  " + "\n  ".join(errors)); sys.exit(1)
# the Lean side of every result must agree with the `atlas:` tags in the sources
import subprocess
sync = subprocess.run([sys.executable, str(ROOT / "scripts/sync_atlas.py"), "--check"],
                      capture_output=True, text=True, encoding="utf-8")
if sync.returncode != 0:
    print(sync.stdout.strip())
    if sync.stderr.strip(): print(sync.stderr.strip(), file=sys.stderr)
    sys.exit(1)
print(f"atlas OK: {len(atlas['results'])} results, {len(decls)} declarations scanned; {sync.stdout.strip()}")
