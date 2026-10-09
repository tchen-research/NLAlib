#!/usr/bin/env python3
"""Import-layer lint. Fails if a NLAlib module imports a module from a higher layer.

Layers (a module may import its own layer and lower):
  0 Matrix          1 Concentration      2 Gaussian
  3 Sketching       4 LowRank, Estimation, Krylov      5 Solvers
TroppMatrixConcentration counts as layer 1. Anything outside NLAlib/Tropp (Mathlib, Std) is layer -1.
"""
import pathlib, re, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
LAYER = {"Matrix": 0, "Concentration": 1, "Gaussian": 2, "Sketching": 3,
         "LowRank": 4, "Estimation": 4, "Krylov": 4, "Solvers": 5}
def layer(mod):
    parts = mod.split(".")
    if parts[0] == "TroppMatrixConcentration": return 1
    if parts[0] != "NLAlib": return -1
    if len(parts) == 1: return 99          # the root module may import everything
    return LAYER.get(parts[1], 99)
bad = []
for f in sorted(ROOT.glob("NLAlib/**/*.lean")) + [ROOT / "NLAlib.lean"]:
    mod = ".".join(f.relative_to(ROOT).with_suffix("").parts)
    for line in f.read_text().splitlines():
        m = re.match(r"\s*import\s+([\w.«»]+)", line)
        if not m: continue
        imp = m.group(1)
        if layer(imp) > layer(mod) and layer(mod) != 99:
            bad.append(f"{mod} (layer {layer(mod)}) imports {imp} (layer {layer(imp)})")
if bad:
    print("Layer violations:\n  " + "\n  ".join(bad)); sys.exit(1)
print("import layers OK")
