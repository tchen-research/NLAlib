#!/usr/bin/env python3
"""Build atlas/viewer.html (the artifact mirror) from the template, the atlas and the vendored KaTeX CSS."""
import pathlib
ROOT = pathlib.Path(__file__).resolve().parent.parent
tpl = (ROOT / "atlas/viewer.template.html").read_text()
data = (ROOT / "atlas/atlas.json").read_text().replace("</", "<\\/")
katex_css = (ROOT / "atlas/vendor/katex.inline.css").read_text()
decls_path = ROOT / "atlas/declarations.json"
decls = decls_path.read_text().replace("</", "<\\/") if decls_path.exists() else "[]"
out = ROOT / "atlas/viewer.html"
out.write_text(tpl.replace("/*ATLAS_JSON*/", data).replace("/*KATEX_CSS*/", katex_css).replace("/*DECLS_JSON*/", decls))
print(f"built {out} ({out.stat().st_size} bytes)")
