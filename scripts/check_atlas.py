#!/usr/bin/env python3
"""Atlas consistency. Validates atlas/atlas.json against the schema, checks referential integrity,
and checks that every formalization marked `proved` or `stated` in one of this repo's libraries
names a declaration that exists in the Lean sources."""
import json, pathlib, re, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
atlas = json.load(open(ROOT / "atlas/atlas.json"))
errors = []
try:
    import jsonschema
    jsonschema.validate(atlas, json.load(open(ROOT / "atlas/schema.json")))
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
for f in list(ROOT.glob("NLAlib/**/*.lean")) + list(ROOT.glob("TroppMatrixConcentration/**/*.lean")):
    ns = []
    for line in f.read_text().splitlines():
        m = re.match(r"\s*namespace\s+([\w.]+)", line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r"\s*end\s+([\w.]+)\s*$", line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = re.match(r"\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?(?:theorem|lemma|def|abbrev|instance|structure)\s+([\w.']+)", line)
        if m:
            name = m.group(1)
            decls.add(".".join(ns + [name]) if ns else name)
            decls.add(name)
for r in atlas["results"]:
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
if errors:
    print("Atlas problems:\n  " + "\n  ".join(errors)); sys.exit(1)
print(f"atlas OK: {len(atlas['results'])} results, {len(decls)} declarations scanned")
