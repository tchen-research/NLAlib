#!/usr/bin/env node
// Render every atlas/book math span with the site's KaTeX version (0.16.11).
// Usage: node scripts/check_site_math.cjs [path/to/katex]
// By default `katex` must be installed. CI installs it in a temporary directory,
// avoiding a package manifest or lockfile for this otherwise Python/Lean site.
const fs = require('node:fs');
const path = require('node:path');

const root = path.resolve(__dirname, '..');
const katex = require(process.argv[2] ? path.resolve(process.argv[2]) : 'katex');
let checked = 0, bad = 0;

function scan(text, label) {
  let i = 0;
  while (i < text.length) {
    if (text[i] === '\\') { i += 2; continue; }
    if (text[i] !== '$') { i++; continue; }
    const display = text[i + 1] === '$', width = display ? 2 : 1;
    let end = i + width;
    while (end < text.length) {
      if (text[end] === '\\') { end += 2; continue; }
      if (text[end] === '$' && (!display || text[end + 1] === '$')) break;
      end++;
    }
    if (end >= text.length) {
      console.error(`${label}: unclosed math delimiter at offset ${i}`);
      bad++;
      return;
    }
    checked++;
    try {
      // Match atlas/viewer.template.html; unsupported macros must still fail.
      katex.renderToString(text.slice(i + width, end), {
        throwOnError: true, strict: false, displayMode: display,
      });
    } catch (e) {
      console.error(`${label}: ${e.message}`);
      bad++;
    }
    i = end + width;
  }
}

function walk(value, label) {
  if (typeof value === 'string') scan(value, label);
  else if (Array.isArray(value)) value.forEach((x, i) => walk(x, `${label}[${i}]`));
  else if (value && typeof value === 'object') {
    const named = value.id ? `${label} (${value.id})` : label;
    for (const [key, x] of Object.entries(value)) walk(x, `${named}.${key}`);
  }
}

const files = ['atlas/atlas.json', ...fs.readdirSync(path.join(root, 'docs/coverage'))
  .filter(x => x.endsWith('.json') && !x.endsWith('.candidates.json'))
  .sort().map(x => `docs/coverage/${x}`)];
for (const file of files) walk(JSON.parse(fs.readFileSync(path.join(root, file), 'utf8')), file);
console.log(`KaTeX ${katex.version}: ${checked} math spans checked; ${bad} rendering problems`);
process.exitCode = bad ? 1 : 0;
