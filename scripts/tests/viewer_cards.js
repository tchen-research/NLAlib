// Execute the real card renderer without external browser/CDN dependencies.
// Every catalogued result must open, including sources with no named authors.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const root = path.resolve(__dirname, '../..');
const read = name => fs.readFileSync(path.join(root, name), 'utf8');
const template = read('atlas/viewer.template.html');
const nodes = new Map();
const node = id => {
  if (!nodes.has(id)) {
    const classes = new Set();
    nodes.set(id, {innerHTML: '', textContent: '', onclick: null, classList: {
      add: name => classes.add(name), remove: name => classes.delete(name),
      contains: name => classes.has(name),
    }});
  }
  return nodes.get(id);
};
for (const [id, file] of [['atlas-data', 'atlas/atlas.json'], ['decls-data', 'atlas/declarations.json'], ['external-data', 'atlas/external.json']]) node(id).textContent = read(file);
node('coverage-data').textContent = '{}';
const listeners = {};
const context = vm.createContext({
  document: {getElementById: node, querySelectorAll: () => []},
  window: {addEventListener: (event, handler) => { listeners[event] = handler; }},
  location: {hash: '', pathname: '/', search: ''},
  history: {replaceState: () => {}},
  applySelectionToGraph: () => {}, assert,
});
const start = template.indexOf('(function () {') + '(function () {'.length;
const setup = template.slice(start, template.indexOf('// ---------- tiles ----------', start));
const drawerStart = template.indexOf('  function select(id) {');
const drawer = template.slice(drawerStart, template.indexOf('// ---------- wiring ----------', drawerStart));
const hashStart = template.indexOf('  function selectHash() {');
const hash = template.slice(hashStart, template.indexOf('})();', hashStart));
assert(start > 0 && drawerStart > 0 && hashStart > 0);
vm.runInContext(setup + drawer + hash + `
  for (const r of A.results) {
    select(r.id);
    assert(document.getElementById('drawer').classList.contains('open'), r.id);
    assert(document.getElementById('dbody').innerHTML.includes(esc(r.title)), r.id);
    select(r.id);
    assert(!document.getElementById('drawer').classList.contains('open'), r.id);
  }
  for (const r of A.results.filter(r => r.proof_family)) {
    assert(hasFormalProof(r), r.id);
    const name = r.proof_family.clauses[0].decls[0];
    declByName[name].sorry = true;
    assert(!hasFormalProof(r), r.id + ' unfinished component');
    declByName[name].sorry = false;
  }
`, context);
// Follow deep links within an already loaded page, and clear a stale selection.
context.location.hash = '#slit-plane-analytic-approx';
listeners.hashchange();
assert(node('drawer').classList.contains('open'));
assert(node('dbody').innerHTML.includes('slit-plane-analytic-approx'));
context.location.hash = '#exp-polynomial-approx';
listeners.hashchange();
assert(node('dbody').innerHTML.includes('exp-polynomial-approx'));
context.location.hash = '';
listeners.hashchange();
assert(!node('drawer').classList.contains('open'));
console.log('All atlas cards, proof-family links and deep links passed.');
