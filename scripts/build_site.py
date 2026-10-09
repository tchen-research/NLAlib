#!/usr/bin/env python3
"""Build the progress site (site/) from atlas/atlas.json and atlas/viewer.template.html.
The result is a self-contained static page, deployed to https://research.chen.pw/NLAlib/."""
import json, pathlib, shutil
ROOT = pathlib.Path(__file__).resolve().parent.parent
SITE = ROOT / "site"
tpl = (ROOT / "atlas/viewer.template.html").read_text()
data = (ROOT / "atlas/atlas.json").read_text().replace("</", "<\\/")
body = tpl.replace("/*ATLAS_JSON*/", data)
page = ("<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">"
        "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1,viewport-fit=cover\">"
        "<style>:root{color-scheme:light;padding-top:env(safe-area-inset-top,0px);padding-bottom:env(safe-area-inset-bottom,0px)}"
        "body{margin:0;font:14px system-ui,sans-serif}img{max-width:100%}[hidden]{display:none!important}</style>"
        "</head><body>" + body + "</body></html>")
SITE.mkdir(exist_ok=True)
(SITE / "index.html").write_text(page)
shutil.copy(ROOT / "atlas/atlas.json", SITE / "atlas.json")
shutil.copy(ROOT / "atlas/schema.json", SITE / "schema.json")
(SITE / ".nojekyll").write_text("")
print(f"built site/index.html ({len(page)} bytes)")
