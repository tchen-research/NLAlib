#!/usr/bin/env python3
"""Check the inventory and evidence of the 2026-10-14 whole-library review.

This validates review coverage and traceability, not mathematical equivalence.
Mathematical judgments are the human read-backs in the four referenced reports.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs/audit/2026-10-14-library.json"


def review_records(document):
    for key in ("records", "cards", "items"):
        if key in document:
            return document[key]
    raise ValueError("review report has no records")


def check_source_ledger(manifest, indexed):
    """Validate source accounting and proof anchors, not mathematical coverage."""
    ledger_path = ROOT / manifest["source_completion_ledger"]
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    source = (ROOT / ledger["source_document"]).read_text(encoding="utf-8")
    table = source.split("Catalogue identifier & Route or remaining boundary", 1)[1]
    table = table.split(r"\bottomrule", 1)[0]
    selected = re.findall(r"\\code\{([^}]+)\}", table)
    assert len(selected) == len(set(selected)), "duplicate source target"
    excluded = set(ledger["excluded_whole_targets"])
    assert excluded == {"truncation-lemma", "crouzeix-palencia"}
    targets = ledger["targets"]
    retained = [r["id"] for r in targets]
    assert len(retained) == len(set(retained)), "duplicate retained target"
    assert set(retained) == set(selected) - excluded, "source accounting mismatch"
    complete = 0
    deferred = 0
    partial = 0
    anchors = set()
    for target in targets:
        rid = target["id"]
        status = target["source_scope_status"]
        assert status in {"complete", "partial", "deferred"}, (rid, "unknown source status")
        assert target["retained_scope"].strip()
        if status == "deferred":
            deferred += 1
            assert rid in manifest["deferred_targets"], (rid, "missing deferral record")
            assert not target["clauses"], (rid, "deferred proof claims included in integration")
            assert target["remaining"] and target["local_archive"], (rid, "missing archive or open scope")
            continue
        assert target["clauses"]
        if status == "complete":
            complete += 1
            assert not target["remaining"], (rid, "complete target has open clauses")
        else:
            partial += 1
            assert target["remaining"], (rid, "partial target omits its open clauses")
        for clause in target["clauses"]:
            assert clause["statement"].strip() and clause["decls"]
            for name in clause["decls"]:
                assert name in indexed, (rid, name, "source proof anchor is absent")
                declaration = indexed[name]
                assert declaration["kind"] in {"theorem", "lemma"}, (
                    rid, name, "source proof anchor is not a theorem")
                assert not declaration["sorry"], (rid, name, "source proof uses sorry")
                anchors.add(name)
    assert ledger["counts"] == {
        "retained_targets": len(targets),
        "completed_source_scopes": complete,
        "active_targets": len(targets) - deferred,
        "open_source_scopes": partial,
        "deferred_source_scopes": deferred,
    }, "source completion count is stale"
    assert ledger["integration_status"] in {"pending", "passed"}
    assert "not a count of wholly proved atlas cards" in ledger["counting_rule"]
    print(f"Source ledger: {complete}/{len(targets) - deferred} active mathematical scopes "
          f"complete, {deferred} deferred; {len(anchors)} checked, sorry-free theorem anchors.")


def main():
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    atlas = json.loads((ROOT / "atlas/atlas.json").read_text(encoding="utf-8"))
    declarations = json.loads((ROOT / "atlas/declarations.json").read_text(encoding="utf-8"))
    results = {r["id"]: r for r in atlas["results"]}
    indexed = {d["name"]: d for d in declarations}
    reviewed = set()
    total = 0
    for path in manifest["reports"]:
        records = review_records(json.loads((ROOT / path).read_text(encoding="utf-8")))
        ids = [r["id"] for r in records]
        assert len(ids) == len(set(ids)), (path, "duplicate review id")
        for record in records:
            rid = record["id"]
            assert rid in results, (path, rid, "unknown card")
            assert record.get("audit_phase") == "final", (path, rid, "baseline readback presented as final")
            assert record.get("baseline_audit", {}).get("id") == rid, (path, rid, "baseline evidence not preserved")
            readback = (record.get("readback") or record.get("review_note") or
                        record.get("mathematical_and_correspondence_review"))
            assert readback and readback.strip(), (rid, "missing mathematical review")
            evidence = record.get("evidence", [])
            evidence += [d["decl"] for d in record.get("checked_declarations", [])]
            evidence += [d["name"] for d in record.get("decisive_signature_evidence", [])]
            for name in evidence:
                assert name in indexed, (rid, name, "reviewed declaration is absent")
            reviewed.add(rid)
        total += len(records)
    assert reviewed == set(results), {"missing": sorted(set(results) - reviewed),
                                      "unknown": sorted(reviewed - set(results))}
    for rid, change in manifest["scope_changes"].items():
        assert rid in reviewed and change["reason"].strip()
        result = results[rid]
        assert result["status"] != "proved", (rid, "unfinished clause advertised as proved")
        assert "proof_family" not in result, (rid, "unfinished clause has full proof family")
        forms = [f for f in result["formalizations"] if f["library"] == "nlalib"]
        assert forms and all(f.get("partial") for f in forms), (rid, "missing partial tag")
    assert manifest["formalization_exclusions"]["lra"] == "Chen–Persson items only"
    check_source_ledger(manifest, indexed)
    print(f"{len(reviewed)}/{len(results)} cards reviewed in {total} traceable records; "
          f"{len(manifest['scope_changes'])} overbroad proof-status claims reopened.")


if __name__ == "__main__":
    main()
