#!/usr/bin/env python3
"""Docstring-noise lint (STANDARDS §3, F4 decision I7).

Docstrings cite published sources only. Flags, per line of a docstring or module docstring:
manuscript keys (`sa:`, `rt:`, `sh:`, "manuscript"), "operator re-derivation", 40-hex commit
hashes, "Audit G0"-style labels, "(label to verify)", "actual"/"genuine", "Prove2me",
"SparseFock" outside the frozen quarry. Exit 1 on any hit.
`python3 scripts/check_docstrings.py [paths…]`.
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
QUARRY = "NLAlib/Sketching/Sparse/"
PATTERNS = [
    (re.compile(r"\b(?:sa|rt|sh|cs|ap|gr|ec|vp|lv|rp|ht):[a-z][\w-]*"), "manuscript key"),
    (re.compile(r"\bmanuscript\b", re.I), "manuscript"),
    (re.compile(r"operator re-?derivation", re.I), "operator re-derivation"),
    (re.compile(r"\b[0-9a-f]{40}\b"), "commit hash"),
    (re.compile(r"\bAudit G[0-9]\b|\baudit G[0-9]\b"), "audit label"),
    (re.compile(r"\(label to verify\)"), "label to verify"),
    (re.compile(r"\b(?:the |an? )?(?:actual|genuine)\b", re.I), "actual/genuine"),
    (re.compile(r"\bProve2me\b"), "Prove2me"),
    (re.compile(r"\bSparseFock\w*"), "SparseFock"),
]

def doc_lines(text):
    """(lineno, line) pairs inside `/-- … -/` and `/-! … -/` comments."""
    inside = False
    for n, line in enumerate(text.split("\n"), 1):
        s = line
        if not inside and ("/--" in s or "/-!" in s):
            inside = True
        if inside:
            yield n, s
            if "-/" in s: inside = False

def main(paths):
    files = []
    for p in paths or [ROOT / "NLAlib"]:
        p = pathlib.Path(p)
        files += [p] if p.is_file() else sorted(p.rglob("*.lean"))
    hits = 0
    for f in files:
        rel = str(f.relative_to(ROOT)) if f.is_absolute() else str(f)
        if rel.startswith(QUARRY): continue
        for n, line in doc_lines(f.read_text()):
            for pat, what in PATTERNS:
                if pat.search(line):
                    print(f"{rel}:{n}: {what}: {line.strip()[:100]}"); hits += 1; break
    print(f"{hits} docstring-noise hits")
    return 1 if hits else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
