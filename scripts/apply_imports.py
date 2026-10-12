#!/usr/bin/env python3
"""Apply the import suggestions of `atlas/import_usage.json` (from `scripts/ImportUsage.lean`).

For every listed module: drop the `removed` import lines and append the `added` ones after the last
import. `--revert M1 M2 …` restores the original import block of those modules from git (used for
files that fail to build after the change). Generated aggregators are never listed."""
import json, re, subprocess, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
usage = json.load(open(ROOT / "atlas" / "import_usage.json"))["imports"]

def path(mod): return ROOT / (mod.replace(".", "/") + ".lean")

def apply(mod, info):
    p = path(mod); src = p.read_text()
    lines = src.split("\n")
    removed = set(info["removed"]); out = []; last_import = -1
    for i, l in enumerate(lines):
        m = re.match(r"^import\s+(\S+)\s*$", l)
        if m and m.group(1) in removed: continue
        if m: last_import = len(out)
        out.append(l)
    for a in info["added"]:
        out.insert(last_import + 1, f"import {a}"); last_import += 1
    p.write_text("\n".join(out))

if len(sys.argv) > 1 and sys.argv[1] == "--revert":
    for mod in sys.argv[2:]:
        p = path(mod); orig = subprocess.run(["git", "show", f"HEAD:{p.relative_to(ROOT)}"], capture_output=True, text=True, cwd=ROOT).stdout
        oimp = [l for l in orig.split("\n") if l.startswith("import ")]
        cur = p.read_text().split("\n")
        first = next(i for i, l in enumerate(cur) if l.startswith("import "))
        last = max(i for i, l in enumerate(cur) if l.startswith("import "))
        p.write_text("\n".join(cur[:first] + oimp + cur[last + 1:]))
        print("reverted", mod)
    sys.exit()

n = 0
for mod, info in usage.items():
    if path(mod).exists(): apply(mod, info); n += 1
print("applied to", n, "files")
