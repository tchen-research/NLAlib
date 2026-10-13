"""Validate reviewed theorem families and derive their proof dependency status."""


def proof_family_decls(result, declarations):
    """Return the tagged declarations covering every reviewed clause.

    Whether the clauses exhaust the mathematical statement is a human review, just
    like a full `atlas:` tag. Existence, linkage and proof dependencies are checked
    against the generated Lean index, never trusted from the coverage annotation.
    """
    if "proof_family" not in result:
        return []
    clauses = result["proof_family"].get("clauses", [])
    if not clauses:
        raise ValueError("proof_family must list the clauses of the full statement")
    names = set()
    for clause in clauses:
        if not clause.get("statement", "").strip() or not clause.get("decls"):
            raise ValueError("each proof_family clause needs a statement and declarations")
        if len(clause["decls"]) != len(set(clause["decls"])):
            raise ValueError("duplicate declarations in a proof_family clause")
        for name in clause["decls"]:
            declaration = declarations.get(name)
            if declaration is None:
                raise ValueError(f"proof_family declaration is absent from the index: {name}")
            if declaration["kind"] != "theorem":
                raise ValueError(f"proof_family declaration is not a theorem: {name}")
            if result["id"] not in declaration["atlas"]:
                raise ValueError(f"proof_family declaration has no tag for this result: {name}")
            names.add(name)
    return sorted(names)


def proof_family_status(result, declarations):
    """A complete family is proved only when all its indexed proofs are sorry-free."""
    names = proof_family_decls(result, declarations)
    if not names:
        return None
    return "scaffold" if any(declarations[name]["sorry"] for name in names) else "proved"
