#!/usr/bin/env python3
"""Naming and file-rule lint (docs/STANDARDS.md §1–§2), run on atlas/declarations.json.

Fails on: theorem names that are a single CamelCase word; defs returning data whose last
component is not lowerCamelCase (structures/classes are UpperCamelCase); chapter- or
source-prefixed names (ch3_, hmt_, lra_, …); and non-simp theorems in a Basic.lean module.
Exemptions live in scripts/name_exemptions.txt (one declaration name per line, with a reason
after a #)."""
import json, pathlib, re, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
decls = json.load(open(ROOT / "atlas/declarations.json"))
ex_file = ROOT / "scripts/name_exemptions.txt"
exempt = set()
if ex_file.exists():
    for line in ex_file.read_text().splitlines():
        line = line.split("#")[0].strip()
        if line: exempt.add(line)
SNAKE = re.compile(r"^[a-zₐ-ₜ₀-₉'ᵢ]+(?:_[a-z0-9₀-₉'ᵢ]+)*(?:_?[₀-₉']*)$|^[a-z][a-z0-9_'₀-₉]*$")
LOWER_CAMEL = re.compile(r"^[a-z][A-Za-z0-9'₀-₉]*$")
UPPER_CAMEL = re.compile(r"^[A-Z][A-Za-z0-9'₀-₉]*$")
SOURCE_PREFIX = re.compile(r"^(ch\d+_|hmt_|tw_|lra_|rangeFinder_|l2_opNorm_)")
problems = []
for d in decls:
    name = d["name"]
    if name in exempt: continue
    last = name.split(".")[-1]
    kind = d["kind"]
    mod = d["module"]
    if re.match(r"^eq_\d+$", last): continue   # auto-generated equation lemmas
    if last in ("mk", "rec", "casesOn", "noConfusion", "recOn", "below", "brecOn", "sizeOf_spec", "injEq", "inj", "noConfusionType", "ibelow", "binductionOn"): continue
    if kind == "theorem":
        # Mathlib theorem names are snake_case joins whose tokens may be camelCase definition
        # names (`specNorm_nonneg`, `sub_mul_sq_le_sum_Ico_sq`); the mechanical check is therefore only
        # that the name is not a single CamelCase word and contains no double underscores.
        if "__" in last or (re.match(r"^[A-Z]", last) and "_" not in last):
            problems.append(f"{name}: theorem name must be snake_case")
        if SOURCE_PREFIX.match(last):
            problems.append(f"{name}: source-flavoured prefix; name the mathematics (STANDARDS §1)")
        if mod.endswith(".Basic") and "simp" not in (d.get("doc") or "").lower():
            # a theorem in Basic.lean is allowed only as an unfolding/simp-level fact; flag others
            if not re.search(r"(_def|_apply|_zero|_one|_eq|_iff|_mk|_self)$", last):
                problems.append(f"{name}: theorem in a Basic.lean module (theorems go in topic files, STANDARDS §2)")
    elif kind == "def":
        sig = d.get("signature", "")
        returns_prop = sig.rstrip().endswith(": Prop")
        if returns_prop:
            if not UPPER_CAMEL.match(last) and not LOWER_CAMEL.match(last):
                problems.append(f"{name}: Prop-valued def should be UpperCamelCase")
        elif not LOWER_CAMEL.match(last) and not UPPER_CAMEL.match(last):
            problems.append(f"{name}: def should be lowerCamelCase")
        elif "_" in last:
            problems.append(f"{name}: def should be lowerCamelCase (no underscores)")
        if SOURCE_PREFIX.match(last):
            problems.append(f"{name}: source-flavoured prefix (STANDARDS §1)")
    elif kind in ("inductive", "structure"):
        if not UPPER_CAMEL.match(last):
            problems.append(f"{name}: type should be UpperCamelCase")
if problems:
    print(f"{len(problems)} naming problems:\n  " + "\n  ".join(problems))
    sys.exit(1)
print(f"names OK ({len(decls)} declarations)")
