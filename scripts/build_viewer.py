#!/usr/bin/env python3
"""Build atlas/viewer.html (the artifact mirror) from the template, the atlas and the vendored KaTeX CSS."""
import json, pathlib
from coverage_status import annotate_coverage
ROOT = pathlib.Path(__file__).resolve().parent.parent
tpl = (ROOT / "atlas/viewer.template.html").read_text()
data = (ROOT / "atlas/atlas.json").read_text().replace("</", "<\\/")
katex_css = (ROOT / "atlas/vendor/katex.inline.css").read_text()
decls_path = ROOT / "atlas/declarations.json"
decls = decls_path.read_text().replace("</", "<\\/") if decls_path.exists() else "[]"
cov = {}
result_index = {r["id"]: r for r in json.loads((ROOT / "atlas/atlas.json").read_text())["results"]}
declaration_index = {d["name"]: d for d in json.loads(decls_path.read_text())}
for cp in sorted((ROOT / "docs/coverage").glob("*.json")):
    if cp.name.endswith(".candidates.json"): continue
    cov[cp.stem] = annotate_coverage(json.loads(cp.read_text()), result_index, declaration_index)
coverage = json.dumps(cov, ensure_ascii=False).replace("</", "<\\/")
ext_path = ROOT / "atlas/external.json"
ext = ext_path.read_text().replace("</", "<\\/") if ext_path.exists() else "[]"
out = ROOT / "atlas/viewer.html"
out.write_text(tpl.replace("/*ATLAS_JSON*/", data).replace("/*KATEX_CSS*/", katex_css).replace("/*DECLS_JSON*/", decls).replace("/*EXTERNAL_JSON*/", ext).replace("/*COVERAGE_JSON*/", coverage))
print(f"built {out} ({out.stat().st_size} bytes)")
