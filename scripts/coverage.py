#!/usr/bin/env python3
"""Book coverage: join docs/coverage/<source>.json (one record per numbered statement of a book)
with the atlas and the declaration index, validate it, and write docs/coverage/<source>.md.

  python3 scripts/coverage.py            # all indexes
  python3 scripts/coverage.py hj13       # one source

Record fields: label (as the book prints it, e.g. "Thm 4.3.17", "Cor 7.3.5", "Def 5.1.1"),
kind (theorem|corollary|lemma|proposition|definition|observation|exercise), chapter ("4.3"),
page (int), name (optional), statement (short paraphrase, never verbatim), status
(nlalib | partial | mathlib | candidate | out-of-scope), atlas (list of atlas ids), decls (NLAlib or
Mathlib declaration names that state it), note (reason for out-of-scope / what is missing for partial).
"""
import collections, json, pathlib, sys
from coverage_status import annotate_coverage
ROOT = pathlib.Path(__file__).resolve().parent.parent
atlas = json.load(open(ROOT / "atlas/atlas.json"))
by_id = {r["id"]: r for r in atlas["results"]}
src_ids = {s["id"] for s in atlas["sources"]}
declaration_index = {x["name"]: x for x in json.load(open(ROOT / "atlas/declarations.json"))}
decls = set(declaration_index)
ext = {x["name"] for x in json.load(open(ROOT / "atlas/external.json"))} if (ROOT / "atlas/external.json").exists() else set()
STATUSES = ["nlalib", "partial", "scaffold", "mathlib", "candidate", "out-of-scope"]
GLYPH = {"nlalib": "✓", "partial": "◐", "scaffold": "◧", "mathlib": "M", "candidate": "○", "out-of-scope": "–"}
want = sys.argv[1:]
problems = []
warnings = []
for p in sorted(q for q in (ROOT / "docs/coverage").glob("*.json") if not q.name.endswith(".candidates.json")):
    src = p.stem
    if want and src not in want: continue
    idx = annotate_coverage(json.load(open(p)), by_id, declaration_index)
    src_field = idx.get("source", "")
    if not src.startswith(src_field): problems.append(f"{p.name}: source field {src_field!r} does not match file name")
    if src_field not in src_ids: problems.append(f"{p.name}: unknown atlas source {src_field}")
    items = idx["items"]; seen = set()
    for it in items:
        lab = it.get("label", "?")
        if lab in seen: problems.append(f"{src} {lab}: duplicate label")
        seen.add(lab)
        for k in ("label", "kind", "chapter", "statement", "status"):
            if k not in it: problems.append(f"{src} {lab}: missing {k}")
        if it.get("status") not in STATUSES: problems.append(f"{src} {lab}: bad status {it.get('status')}")
        for i in it.get("atlas", []):
            if i not in by_id: problems.append(f"{src} {lab}: unknown atlas id {i}")
        for d in it.get("decls", []):
            if d not in decls and d not in ext and not d.startswith("Mathlib:"):
                problems.append(f"{src} {lab}: declaration not in the index: {d}")
        if it.get("status") in ("nlalib", "partial") and not it.get("atlas") and not it.get("decls"):
            problems.append(f"{src} {lab}: status {it['status']} needs an atlas id or a declaration")
        if it.get("status") == "out-of-scope" and not it.get("note"):
            problems.append(f"{src} {lab}: out-of-scope needs a note")
        # item status against atlas status (warnings: the Books tab must not contradict the atlas)
        sts = [by_id[i]["status"] for i in it.get("atlas", []) if i in by_id]
        if it.get("status") == "candidate" and sts and all(s == "proved" for s in sts):
            warnings.append(f"{src} {lab}: candidate, but every atlas id is proved ({', '.join(it['atlas'])})")
        if it.get("status") in ("nlalib", "partial") and sts and all(s == "candidate" for s in sts) and not it.get("decls"):
            warnings.append(f"{src} {lab}: {it['status']}, but every atlas id is a candidate ({', '.join(it['atlas'])})")
    # atlas labels for this source not present in the index (label verification)
    atlas_labels = collections.defaultdict(list)
    for r in atlas["results"]:
        for s in r["sources"]:
            if s["source"] == src_field and s.get("label"): atlas_labels[s["label"]].append(r["id"])
    index_labels = {it["label"] for it in items}
    import re
    def norm(l):
        l = re.sub(r"\(.*?\)", "", l); l = re.sub(r"^(cf\.|see)\s*", "", l.strip())
        for a, b in (("Theorem", "Thm"), ("Corollary", "Cor"), ("Lemma", "Lem"), ("Definition", "Def"), ("Proposition", "Prop"), ("Observation", "Obs"), ("Problem", "Ex"), ("Exercise", "Ex"), ("Example", "Ex"), ("Section", "§"), ("Sec", "§"), ("Ch", "§")):
            l = l.replace(a, b)
        return l.replace(".", "").replace(" ", "").lower()
    nl = {norm(l) for l in index_labels}
    unmatched = [(l, ids) for l, ids in atlas_labels.items() if not any(norm(part) in nl for part in re.split(r"[;,]", l) if part.strip())]
    # report
    by_ch = collections.OrderedDict()
    for it in items: by_ch.setdefault(it["chapter"].split(".")[0], []).append(it)
    tot = collections.Counter(it["status"] for it in items)
    title = next((s["title"] for s in atlas["sources"] if s["id"] == src_field), src)
    out = [f"# Coverage of {title} (`{src}`)", "", idx.get("edition_note", ""), "",
           "Legend: ✓ in NLAlib · ◐ partially in NLAlib · ◧ unfinished proof dependency · M in Mathlib · ○ candidate (to add) · – out of scope", "",
           "| status | count |", "|---|---|"] + [f"| {GLYPH[s]} {s} | {tot[s]} |" for s in STATUSES] + [f"| total | {len(items)} |", ""]
    for ch, its in by_ch.items():
        c = collections.Counter(it["status"] for it in its)
        out += [f"## Chapter {ch}  ({' · '.join(f'{GLYPH[s]} {c[s]}' for s in STATUSES if c[s])})", "", "| label | statement | status | atlas / declarations | note |", "|---|---|---|---|---|"]
        for it in its:
            links = ", ".join(f"`{i}`" for i in it.get("atlas", [])) + (" " if it.get("atlas") and it.get("decls") else "") + ", ".join(f"`{d}`" for d in it.get("decls", [])[:3])
            name = f"**{it['name']}.** " if it.get("name") else ""
            out.append(f"| {it['label']} | {name}{it['statement']} | {GLYPH[it['status']]} {it['status']} | {links} | {it.get('note', '')} |")
        out.append("")
    if unmatched:
        out += ["## Atlas labels for this source not found in the index (verify)", ""] + [f"- `{l}` ← {', '.join(ids)}" for l, ids in unmatched] + [""]
    (ROOT / f"docs/coverage/{src}.md").write_text("\n".join(out), encoding="utf-8", newline="\n")
    print(f"{src}: {len(items)} items; " + ", ".join(f"{s} {tot[s]}" for s in STATUSES) + f"; {len(unmatched)} atlas labels unmatched")
if warnings:
    print(f"warnings ({len(warnings)}; item status disagrees with the atlas):\n  " + "\n  ".join(warnings))
if problems:
    print("problems:\n  " + "\n  ".join(problems)); sys.exit(1)
