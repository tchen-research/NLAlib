#!/usr/bin/env python3
"""Check the 33 polynomial and six matrix completions against the generated atlas.

Run after ExtractDecls.lean and sync_atlas.py. The scope is recorded in
docs/audit/2026-10-13-polynomial-matrix.json; counts do not infer proof completeness.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main():
    scope = json.loads((ROOT / "docs/audit/2026-10-13-polynomial-matrix.json").read_text(encoding="utf-8"))
    atlas = json.loads((ROOT / "atlas/atlas.json").read_text(encoding="utf-8"))
    declarations = json.loads((ROOT / "atlas/declarations.json").read_text(encoding="utf-8"))
    results = {r["id"]: r for r in atlas["results"]}
    indexed = {d["name"]: d for d in declarations}
    polynomial, matrix = scope["polynomial_ids"], scope["matrix_ids"]
    assert len(set(polynomial)) == len(polynomial) == 33
    assert len(set(matrix)) == len(matrix) == 6
    for rid in polynomial + matrix:
        result = results[rid]
        assert result["status"] == "proved", (rid, result["status"])
        forms = [f for f in result["formalizations"] if f["library"] == "nlalib"]
        assert any(not f.get("partial") for f in forms), (rid, "no complete formalization")
        for form in forms:
            declaration = indexed[form["decl"]]
            assert form["status"] == "proved" and not declaration["sorry"], (rid, form["decl"])
    for rid in scope["excluded_ids"]:
        assert rid not in polynomial + matrix
    print("39/39 requested entries proved: 33 polynomial + 6 matrix; no scoped sorry dependencies.")


if __name__ == "__main__":
    main()
