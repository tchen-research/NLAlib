#!/usr/bin/env python3
"""Norm-spelling lint (STANDARDS §3 "Norms", F4 decision N1/N2).

Matrix norms in public statements are the named functions (`specNorm`, `frobNorm`, `frobSq`,
`nuclearNorm`, `schattenNorm`, `kyFanNorm`); `‖A‖` on a matrix is allowed in statements only in
the exempt directories. Checks:
  1. no file-level `open scoped … Matrix.Norms.*` outside the exempt directories (a proof that
     needs Mathlib's normed API writes `open scoped Matrix.Norms.L2Operator in` before the one
     declaration);
  2. in non-exempt files, no `‖` applied to a capitalised identifier or a parenthesised matrix
     expression inside a declaration signature (heuristic; `‖WithLp.toLp 2 …‖` is the vector norm
     and is fine);
  3. no `Real.sqrt (x ⬝ᵥ x)` and no `{x // x ⬝ᵥ x = 1}` in signatures anywhere.
Exit 1 on any hit. `python3 scripts/check_norms.py [paths…]`.
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXEMPT = ("NLAlib/Matrix/Functions/", "NLAlib/ForMathlib/",
          "NLAlib/Sketching/Sparse/")  # Sparse: frozen quarry (F3)
BRIDGES = {"NLAlib/Matrix/Norms/Core.lean", "NLAlib/Matrix/Norms/Frobenius.lean"}
SIG_START = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|structure)\b")
OPEN_SCOPED = re.compile(r"^open scoped\b[^\n]*\bMatrix\.Norms\.")
NORM_ON_MATRIX = re.compile(r"‖\s*(?:\(?[A-Z][A-Za-z₀-₉']*(?:[ᵀᴴ⁻¹]|\s|\)|‖)|\(\s*(?:1 - |[A-Z]))")
SQRT_DOT = re.compile(r"Real\.sqrt \([^)]*⬝ᵥ|√\([^)]*⬝ᵥ|\{\s*\w+\s*//\s*\w+ ⬝ᵥ \w+ = 1\s*\}")

def signatures(text):
    """Yield (lineno, signature text) for each declaration: from the keyword line to `:=`/`where`/`|`."""
    lines = text.split("\n"); i = 0
    while i < len(lines):
        if SIG_START.match(lines[i]):
            start = i; buf = []
            while i < len(lines):
                l = lines[i]; buf.append(l)
                if re.search(r":=|\bwhere\b|^\s*\|", l) or (i > start and l.strip() == ""): break
                i += 1
            sig = "\n".join(buf)
            sig = sig.split(":=")[0]
            yield start + 1, sig
        i += 1

def main(paths):
    files = []
    for p in paths or [ROOT / "NLAlib"]:
        p = pathlib.Path(p)
        files += [p] if p.is_file() else sorted(p.rglob("*.lean"))
    hits = []
    for f in files:
        rel = f.relative_to(ROOT).as_posix() if f.is_absolute() else f.as_posix()
        text = f.read_text()
        exempt = rel.startswith(EXEMPT) or rel in BRIDGES
        if not exempt:
            for n, line in enumerate(text.split("\n"), 1):
                if OPEN_SCOPED.match(line) and not line.rstrip().endswith(" in"):
                    hits.append(f"{rel}:{n}: file-level `{line.strip()}` (use `open scoped … in` per declaration)")
            for n, sig in signatures(text):
                s = re.sub(r"‖WithLp\.toLp 2 [^‖]*‖", "", sig)
                if NORM_ON_MATRIX.search(s):
                    hits.append(f"{rel}:{n}: `‖·‖` on a matrix in a signature")
        for n, sig in signatures(text):
            if SQRT_DOT.search(sig):
                hits.append(f"{rel}:{n}: vector norm spelled with `⬝ᵥ` (use `‖WithLp.toLp 2 x‖`)")
    for h in hits: print(h)
    print(f"{len(hits)} norm-spelling hits in {len(files)} files")
    return 1 if hits else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
