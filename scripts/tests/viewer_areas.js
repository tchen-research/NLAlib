// Execute the actual area renderer: every matching card must appear exactly once,
// including cards assigned directly to a parent that also has subsections.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const root = path.resolve(__dirname, '../..');
const read = name => fs.readFileSync(path.join(root, name), 'utf8');
const template = read('atlas/viewer.template.html');
function element() {
  let html = '';
  const el = {children: [], dataset: {}, textContent: '', className: '',
    appendChild(child) { this.children.push(child); },
    querySelector(selector) {
      assert.equal(selector, '.chips');
      assert(this.innerHTML.includes('class="chips"'));
      if (!this.chips) { this.chips = element(); this.appendChild(this.chips); }
      return this.chips;
    },
  };
  Object.defineProperty(el, 'innerHTML', {
    get() { return html; },
    set(value) { html = value; el.children = []; delete el.chips; },
  });
  return el;
}
const nodes = new Map();
const node = id => { if (!nodes.has(id)) nodes.set(id, element()); return nodes.get(id); };
node('atlas-data').textContent = read('atlas/atlas.json');
for (const id of ['decls-data', 'external-data']) node(id).textContent = '[]';
node('coverage-data').textContent = '{}';
const context = vm.createContext({document: {getElementById: node, createElement: element}, window: {}, assert});
const start = template.indexOf('(function () {') + '(function () {'.length;
const setup = template.slice(start, template.indexOf('// ---------- tiles ----------', start));
const areaStart = template.indexOf('  function renderAreas() {');
const renderer = template.slice(areaStart, template.indexOf('// ---------- graph ----------', areaStart));
assert(start > 0 && areaStart > 0);
vm.runInContext(setup + renderer + `
  function verifyAreas(label) {
    renderAreas();
    const expected = A.results.filter(matches);
    const actual = [];
    for (const sec of document.getElementById('areas').children) {
      const rows = expected.filter(r => topArea(r).id === sec.dataset.area);
      const ids = sec.children.flatMap(row => row.querySelector('.chips').children.map(b => b.dataset.id));
      assert.equal(JSON.stringify(ids.slice().sort()), JSON.stringify(rows.map(r => r.id).sort()), label + ': ' + sec.dataset.area);
      actual.push(...ids);
      assert(sec.innerHTML.includes('Status of ' + rows.length + ' results'), label + ': visible count');
      const total = A.results.filter(r => topArea(r).id === sec.dataset.area).length;
      if (rows.length !== total) assert(sec.innerHTML.includes('shown · ' + total + ' total'), label + ': total count');
      for (const s of STATUS) {
        const n = rows.filter(r => r.status === s.id).length;
        assert.equal(sec.innerHTML.includes('title="' + s.label + ': ' + n + '"'), n > 0,
          label + ': status count ' + s.id);
      }
    }
    assert.equal(JSON.stringify(actual.slice().sort()), JSON.stringify(expected.map(r => r.id).sort()), label + ': every matching card');
    assert.equal(new Set(actual).size, actual.length, label + ': no duplicate cards');
  }
  function resetFilters() { state.status.clear(); state.pri = ''; state.q = ''; state.hideapps = false; }
  verifyAreas('all current cards');
  for (const status of STATUS) {
    state.status = new Set([status.id]);
    verifyAreas('status ' + status.id);
  }
  resetFilters();
  for (const pri of ['now', 'next', 'later']) { state.pri = pri; verifyAreas('priority ' + pri); }
  resetFilters();
  state.hideapps = true;
  verifyAreas('hide applications');
  for (const q of ['hutchinson', 'residual', 'kaczmarz', 'not-a-result-query-xyz']) {
    resetFilters(); state.q = q; verifyAreas('search ' + q);
  }
  state.q = 'residual'; state.pri = 'next'; state.status = new Set(['candidate']);
  verifyAreas('combined filters');
  resetFilters();
  // The schema allows deeper trees. Keep direct Solvers cards and add both a
  // child and a grandchild with results to exercise each level of one subtree.
  for (const [id, parent] of [['fixture-child', 'solvers'], ['fixture-grandchild', 'fixture-child']]) {
    const a = {id, parent, name: id, order: 100};
    A.areas.push(a); areaById[id] = a;
    const r = {...A.results[0], id: id + '-result', title: id, area: id,
      status: 'candidate', formalizations: [], depends_on: []};
    A.results.push(r); byId[r.id] = r;
  }
  verifyAreas('mixed parent, child and grandchild');
  state.q = 'fixture-grandchild-result';
  verifyAreas('deep descendant search');
`, context);
console.log('All area cards and visible status counts passed, including filters and nested subsections.');
