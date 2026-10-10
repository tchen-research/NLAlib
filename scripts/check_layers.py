#!/usr/bin/env python3
"""Import-layer lint. Fails if a NLAlib module imports a module from a higher layer.

Layers (a module may import its own layer and lower):
  -1 ForMathlib     0 Matrix, Polynomial   1 Concentration, Krylov      2 Gaussian
  3 Sketching       4 LowRank, Estimation      5 Solvers
Anything outside NLAlib (Mathlib, Std) is layer -1.
"""
import pathlib, re, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
LAYER = {"ForMathlib": -1, "Matrix": 0, "Polynomial": 0, "Concentration": 1, "Gaussian": 2, "Sketching": 3,
         "Krylov": 1, "LowRank": 4, "Estimation": 4, "Solvers": 5}
def layer(mod):
    parts = mod.split(".")
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
