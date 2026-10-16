#!/usr/bin/env python3
"""Check the historical 33 polynomial and six matrix completion inventory.

Run after ExtractDecls.lean and sync_atlas.py. The scope is recorded in
docs/audit/2026-10-13-polynomial-matrix.json. The subsequent whole-library
statement review can reopen an overbroad completion claim with explicit evidence.
"""
import json
from pathlib import Path
from atlas_proof_status import proof_family_status

ROOT = Path(__file__).resolve().parent.parent


def main():
    scope = json.loads((ROOT / "docs/audit/2026-10-13-polynomial-matrix.json").read_text(encoding="utf-8"))
    atlas = json.loads((ROOT / "atlas/atlas.json").read_text(encoding="utf-8"))
    declarations = json.loads((ROOT / "atlas/declarations.json").read_text(encoding="utf-8"))
    review = json.loads((ROOT / "docs/audit/2026-10-14-library.json").read_text(encoding="utf-8"))
    reopened = review["scope_changes"]
    results = {r["id"]: r for r in atlas["results"]}
    indexed = {d["name"]: d for d in declarations}
    polynomial, matrix = scope["polynomial_ids"], scope["matrix_ids"]
    assert len(set(polynomial)) == len(polynomial) == 33
    assert len(set(matrix)) == len(matrix) == 6
    for rid in polynomial + matrix:
        result = results[rid]
        forms = [f for f in result["formalizations"] if f["library"] == "nlalib"]
        if rid in reopened:
            assert reopened[rid]["reason"].strip(), (rid, "missing reopening evidence")
            assert result["status"] != "proved", (rid, "overbroad completion claim")
            assert forms and all(f.get("partial") for f in forms), (rid, "missing partial tags")
        else:
            assert result["status"] == "proved", (rid, result["status"])
            assert (any(not f.get("partial") for f in forms) or
                    proof_family_status(result, indexed) == "proved"), (
                        rid, "no complete formalization or reviewed proof family")
        for form in forms:
            declaration = indexed[form["decl"]]
            assert form["status"] == "proved" and not declaration["sorry"], (rid, form["decl"])
    for rid in scope["excluded_ids"]:
        assert rid not in polynomial + matrix
    n = len(set(polynomial + matrix) & set(reopened))
    print(f"39/39 historical entries checked: {39 - n} proved, {n} scope claims reopened; "
          "linked declarations have no sorry dependencies.")


if __name__ == "__main__":
    main()
