"""Display unfinished proof dependencies consistently in book coverage and the atlas."""


def annotate_coverage(index, results, declarations):
    """Conservatively flag a coverage claim citing an unfinished result/declaration.

    The hand-authored index is not rewritten. A row citing several results still needs
    review if one is unfinished; the other proofs do not discharge that dependency.
    """
    for item in index["items"]:
        if item.get("status") not in ("nlalib", "partial"):
            continue
        unfinished = [d for d in item.get("decls", [])
                      if declarations.get(d, {}).get("sorry", False)]
        unfinished += [i for i in item.get("atlas", [])
                       if results.get(i, {}).get("status") == "scaffold"]
        if unfinished:
            item["status"] = "scaffold"
            note = "Unfinished proof dependencies: " + ", ".join(unfinished) + "."
            item["note"] = " ".join(filter(None, [item.get("note", ""), note]))
    return index
