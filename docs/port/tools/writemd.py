import json,collections,re
ROOT='/home/tyler/Documents/prove2me/lean'
R=json.load(open('/tmp/port/manifest.json')); A={r['module']:r for r in R}
GR=json.load(open('/tmp/port/graph.json'))
R.sort(key=lambda r:r['module'])
json.dump(R,open(ROOT+'/docs/port/manifest.json','w'),ensure_ascii=False,indent=1)
mod=lambda p:p[:-5].replace('/','.')
s=lambda m:m[7:]
fin=collections.defaultdict(list)
for r in R:
    if r['action']=='keep': fin[r['module']].insert(0,r['module'])
for r in R:
    if r['action']=='merge': fin[mod(r['target'])].append(r['module'])
sz={t:sum(A[m]['lines'] for m in ms) for t,ms in fin.items()}
cnt=collections.Counter(r['action'] for r in R)
L=[]
w=L.append
w('# Port manifest (draft)\n')
w('Generated 2026-10-13 for `docs/FOUNDATIONS_BRIEF.md` §5. Machine-readable: `docs/port/manifest.json` (one entry per Lean content file; aggregators and the declaration-free shim `Probability/Concentration/Matrix/LiebJensen.lean` are excluded). '
  'Inputs: `atlas/declarations.json` (signatures, sorry flags, atlas tags), the `import` graph (resolved through aggregators), file sizes and names, `docs/dedup/*.md`, `docs/rclike/*.md`, `docs/DEDUP_FOLLOWUP.md`, `docs/SPARSE_INTEGRATION.md`. No Lean file was edited and no Lean/lake process was run.\n')
w('Entry schema: `{"module","lines","action","target"(merge/drop),"field","index","sorry","note"}`. For a `keep` that absorbs merges the note starts with `topic file: absorbs …`.\n')
w('## Totals\n')
w(f'- Content files: **{len(R)}** ({sum(r["lines"] for r in R)} lines).')
w(f'- `keep` **{cnt["keep"]}**, `merge` **{cnt["merge"]}**, `drop` **{cnt["drop"]}**, `rebuild` **{cnt["rebuild"]}**.')
w(f'- Files ported as files (keep, each absorbing its merges): **{cnt["keep"]}** = {cnt["keep"]*100//len(R)}% of today\'s count. Median topic-file size {sorted(sz.values())[len(sz)//2]} lines (before ℝ/ℂ dedup); {sum(1 for v in sz.values() if v>600)} exceed 600 lines, seven are single files already over 600 lines, two are `LogSobolevHerbst` (+58-line `LipschitzConcentration`) and `ProjectionGaps` (+ the ℂ projection files).')
w(f'- Rebuild set: {cnt["rebuild"]} files (115 Sketching/Sparse, 5 Solvers, {cnt["rebuild"]-120} F2 law/measurability files), rewritten in the new repository rather than copied.\n')
w('## Per top-level directory\n')
w('| directory | files | lines | keep | merge | drop | rebuild | files after port |')
w('|---|---:|---:|---:|---:|---:|---:|---:|')
T=collections.defaultdict(collections.Counter)
def key(m):
    p=m.split('.')
    return p[1]
for r in R:
    k=key(r['module']); T[k][r['action']]+=1; T[k]['files']+=1; T[k]['lines']+=r['lines']
tot=collections.Counter()
for k in sorted(T):
    t=T[k]; tot.update(t)
    w(f"| {k} | {t['files']} | {t['lines']} | {t['keep']} | {t['merge']} | {t['drop']} | {t['rebuild']} | {t['keep']} (+{t['rebuild']} rebuild) |")
w(f"| **total** | {tot['files']} | {tot['lines']} | {tot['keep']} | {tot['merge']} | {tot['drop']} | {tot['rebuild']} | {tot['keep']} (+{tot['rebuild']}) |\n")
w('Matrix by subdirectory:\n')
w('| Matrix/… | files | keep | merge | drop | rebuild |')
w('|---|---:|---:|---:|---:|---:|')
M=collections.defaultdict(collections.Counter)
for r in R:
    p=r['module'].split('.')
    if p[1]=='Matrix': M[p[2]][r['action']]+=1; M[p[2]]['files']+=1
for k in sorted(M):
    t=M[k]; w(f"| {k} | {t['files']} | {t['keep']} | {t['merge']} | {t['drop']} | {t['rebuild']} |")
w('')
w('## Method\n')
w('1. **rebuild** (mechanical): every file under `Sketching/Sparse/` (F3); every file under `Solvers/` (expectations are finite weighted path sums, `expErr`); every file that `grep` finds using `Matrix.of.symm`, stating a law as `….map … = gaussianMatrix …`, or defining an `_of_map_eq` wrapper (F2); plus the three definition files F2 rewrites (`IsStandardGaussian`, `IsRademacher`, and the `Matrix ℂ` measurable-space instances in `MatrixStatistics`).')
w('2. **drop** (mechanical candidates, then reviewed by hand): single-theorem `*Toolkit` bundles (the target is the file holding most of the bundled components, computed from the theorem names the bundle cites); the ℂ/ℝ twins of the F1 spectral core and of the Norms/Subspaces/Functions vocabulary that F1 or the RCLike round makes generic; Fin→Fintype transport files; two leaves with no importer that duplicate another file. Every drop names the file that makes it redundant (`target`), and if that file is itself merged, the note says where it ends up.')
w('3. **merge**: the remaining files are clustered per directory (ForMathlib per second-level area; Estimation and the non-Sparse Sketching per top level), within hand-written topic groups for the large Matrix directories (`Interlacing*`, `Gershgorin*`/diagonal dominance, real Schur, `Sylvester*`, `Schatten*`, CS/oblique, `LeastSquares*`, `Pseudoinverse*`, `SimpleEigenvalue*`, `DavisKahan*`, `Wedin*`, `Hadamard*`, `Majorization*`, Cholesky/QR/rank-revealing/polar, …). Clusters grow by joining a cluster under 200 lines to a neighbour (import edge first, then same topic) while the result stays ≤ 500 lines; leftovers under 120 lines join an import neighbour up to 700. Every join is checked against the import graph so that no merged file creates an import cycle (the final quotient graph is acyclic). The target of a cluster is its largest file (×1.5 if it carries an atlas tag; `Basic`/`Core` files win; toolkits/transports never). ℝ/ℂ twin pairs that are merged rather than dropped are pre-joined and counted at half size.')
w('4. **keep**: the cluster targets, which absorb their merges.')
w('5. `field` from the declaration signatures (`RCLike`/`𝕜` → 𝕜; ℂ in ≥ 40% of signatures, or more often than ℝ → ℂ; else ℝ; none). `index`: `Fin` if signatures use `Matrix (Fin …)`/`(Fin n) →` and no `Fintype` binder, `Fintype` for the converse, `mixed` for both. `sorry`: the file itself contains `sorry` (11 files, all catalogued scaffolds).\n')
w('## Rebuild list\n')
groups=collections.defaultdict(list)
for r in R:
    if r['action']!='rebuild': continue
    m=r['module']
    if '.Sketching.Sparse.' in m: groups['F3 (Sketching/Sparse)'].append(r)
    elif '.Solvers.' in m: groups['Solvers finite-sum probability'].append(r)
    else: groups['F2 (random matrices on `Matrix`, one `HasLaw` interface)'].append(r)
for g in ['F2 (random matrices on `Matrix`, one `HasLaw` interface)','Solvers finite-sum probability']:
    w(f'### {g}: {len(groups[g])} files\n')
    w('| file | lines | what changes |'); w('|---|---:|---|')
    for r in groups[g]:
        w(f"| `{s(r['module'])}` | {r['lines']} | {r['note'].split('; ')[0] if g.startswith('Solvers') else r['note']} |")
    w('')
sp=groups['F3 (Sketching/Sparse)']
sub=collections.Counter(); subl=collections.Counter()
for r in sp:
    p=r['module'].split('.'); k='/'.join(p[3:5]) if len(p)>5 else p[3]+' (top)'
    sub[k]+=1; subl[k]+=r['lines']
w(f'### F3 (Sketching/Sparse): {len(sp)} files, {sum(r["lines"] for r in sp)} lines\n')
w('All marked `rebuild`; `docs/SKETCH_INTERFACE.md` (F3) will split them into rebuild vs drop and name the 3–4 reusable lemmas. By subdirectory:\n')
w('| Sparse/… | files | lines |'); w('|---|---:|---:|')
for k in sorted(sub): w(f'| {k} | {sub[k]} | {subl[k]} |')
w('\nNon-Sparse files whose only importers are in Sparse (kept, flagged in their notes): '+', '.join('`'+s(r['module'])+'`' for r in R if 'only consumers are in Sketching/Sparse' in r['note'] and r['action']!='drop')+'.\n')
w('Files that mention `gaussianMatrix` but integrate against it directly are `keep` with the F2 note "primary statement kept, add `_of_hasLaw` corollary" (brief §2): '+', '.join('`'+s(r['module']).split('.')[-1]+'`' for r in R if 'add `_of_hasLaw`' in r['note'])+'.\n')
w('## Drops (all reviewed by hand)\n')
w('| file | lines | redundant because of | reason |'); w('|---|---:|---|---|')
for r in R:
    if r['action']=='drop':
        w(f"| `{s(r['module'])}` | {r['lines']} | `{r['target'][7:]}` | {r['note']} |")
w('')
w('Not dropped although the mechanical rules flagged them:\n')
for k,why in [('Matrix.Spectral.InterlacingReindex','reindex transport, but `InterlacingSymmetricConverse` consumes it: merged into that topic file, to disappear when the construction is stated over Fintype (the brief\'s own example)'),
('Matrix.Spectral.NormalToolkit','three genuine normal-matrix characterizations besides the bundle'),
('Matrix.Spectral.SingularInterlacingToolkit','delete-row/column corollaries, not a bundle'),
('Matrix.Inequalities.HermitianPartToolkit','genuine characterization besides the bundle'),
('Matrix.Inequalities.MajorizationProperties','six genuine `sumLargest`/majorization lemmas despite the name; six importers'),
('Matrix.Perturbation.LeastSquaresToolkit','genuine relative-error corollaries besides the bundle'),
('Matrix.Norms.Reindex','reindex *invariance* lemmas (`specNorm_reindex`, …) are API, not transport'),
('Matrix.Structured.WalshFin','Fin-label Walsh transform that SRHT uses'),
('Matrix.Spectral.RealSchur*, RealNormal*, RealQZ, RealSimilarityDescent, ComplexQZ','genuinely real (or complex) theory, not twins of a generic theorem'),
('Matrix.Subspaces.Complex{CS,Oblique,Gram}* , LowRank complex stacks','ℝ/ℂ twin families whose ℂ file carries content the ℝ file lacks: `merge` into the ℝ sibling (CS, oblique, Gram isometry, subspace iteration, polynomial filter) or kept as the 𝕜 keeper with the ℝ file dropped (RPCholesky, volume sampling, rclike D12)'),
('proof scaffolding consumed only inside its directory','folded into its topic file (merge), never dropped: dropping it would orphan the theorem it proves')]:
    w(f'- `{k}`: {why}.')
w('')
w('## Twenty largest `keep` files\n')
w('| file | own lines | after merges | absorbs | note |'); w('|---|---:|---:|---:|---|')
for r in sorted([r for r in R if r['action']=='keep'],key=lambda r:-r['lines'])[:20]:
    n=len(fin[r['module']])-1
    nt=[x for x in r['note'].split('; ') if not x.startswith('topic file')]
    w(f"| `{s(r['module'])}` | {r['lines']} | {sz[r['module']]} | {n} | {'; '.join(nt)} |")
w('')
w('## Items for the port (brief §4), noticed while drafting\n')
w('- Bundle theorems inside non-toolkit files: '+', '.join('`'+s(r['module']).split('.')[-1]+'`' for r in R if 'bundle theorem' in r['note'])+'. Delete at port; move their full atlas tags to the main theorem (DEDUP_FOLLOWUP, "atlas-tag policy").')
w('- Atlas tags carried by dropped files must move: every drop note that says "move tag …" lists the id.')
w(f"- Sorry scaffolds ({sum(1 for r in R if r['sorry'])} files): "+', '.join('`'+s(r['module'])+'`' for r in R if r['sorry'])+'.')
w('- The real `CholeskyHistories`/`RandomPivotedCholesky`/`VolumeSampling` drops assume the 𝕜 keeper is built from the ℂ stacks (rclike D12); the ℂ files then lose their `Complex` prefix.')
w('- `ForMathlib/*` clusters follow Mathlib areas; upstreaming candidates named in DEDUP_FOLLOWUP (GramSchmidt, Fourier*, InterlacingInterpolation, NonnegativeSupermartingale, BoundedDifferences, Matrix/Order) should be checked against Mathlib before porting.')
w('- The Schur-triangularisation re-derivations in `ForMathlib/Analysis/*` (OrderedSchur, SchurTriangularization, PencilTriangularization, SimultaneousTriangularization, OrderedSimultaneousSchur) and `Matrix/Spectral` (SchurTriangularization, OrderedSchur, PrimaryTriangularization) should come from one induction (DEDUP_FOLLOWUP); the manifest keeps them as separate topic files.\n')
w('## Caveats\n')
w('- Merge targets are mechanical: topic files are named after their largest member, so several targets want a rename at port time (for example `ComplexVolumeSamplingError` absorbs `VolumeCounting`; `RealDilation` absorbs `Eigenframes`). The rename ledger seed is the `target` column.')
w('- Acyclicity was checked on today\'s import graph. F1/F2 will move a few lemmas between core files; re-run the acyclicity check on the quotient graph (keep/merge/rebuild targets) after F1 and F2 land.')
w('- `field`/`index` are signature heuristics. Files that state ℂ results with ℝ eigenvalues may show ℝ; files in the F1 core show their *current* field and index, which F1 changes to 𝕜/Fintype.')
w('- The drop rationale for each ℝ/ℂ twin is taken from the dedup/rclike reports; the complex and real statements were not compared lemma by lemma. Where a twin might carry a statement the generic file lacks, it was made a `merge` instead.\n')
w('## Topic files (keep targets and what they absorb)\n')
cur=None
for t in sorted(fin):
    d='/'.join(t.split('.')[1:-1])
    if d!=cur:
        cur=d; w(f'\n**{d}/**\n')
    ms=fin[t][1:]
    w(f"- `{t.split('.')[-1]}` ({sz[t]})"+(': '+', '.join(f"{m.split('.')[-1]} ({A[m]['lines']})" for m in sorted(ms,key=lambda m:-A[m]['lines'])) if ms else ''))
open(ROOT+'/docs/port/MANIFEST.md','w').write('\n'.join(L)+'\n')
print(len(L))
