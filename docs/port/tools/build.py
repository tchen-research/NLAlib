import json,re,collections,sys
sys.path.insert(0,'/tmp/port')
from overrides import O
from groups import G as GROUPS
ROOT='/home/tyler/Documents/prove2me/lean'
inv=json.load(open('/tmp/port/inv.json')); GR=json.load(open('/tmp/port/graph.json'))
decls=json.load(open(ROOT+'/atlas/declarations.json'))
by=collections.defaultdict(list)
for x in decls: by[x['module']].append(x)
content=sorted(GR)
short=lambda m:m.split('.')[-1]
rel=lambda m:m[len('NLAlib.'):]
path=lambda m:m.replace('.','/')+'.lean'
def mdir(m): return m.rsplit('.',1)[0]
CAP=int(sys.argv[1]) if len(sys.argv)>1 else 500
SMALL=int(sys.argv[2]) if len(sys.argv)>2 else 200

# ---------- attributes ----------
def field_index(m):
    sigs=[x['signature'] for x in by[m]]
    K=sum(1 for s in sigs if re.search(r'RCLike|𝕜',s)); C=sum(1 for s in sigs if 'ℂ' in s); R=sum(1 for s in sigs if 'ℝ' in s)
    n=max(len(sigs),1)
    if K: f='𝕜'
    elif C>=2 and C/n>=0.4 or (C and C>=R): f='ℂ'
    elif R or C: f='ℝ' if R>=C else 'ℂ'
    else: f='none'
    fin=sum(1 for s in sigs if re.search(r'Matrix \(Fin |\(Fin [^()]*\) → |Matrix \(Fin [^()]*\)|: Fin [a-z0-9]+ → (ℝ|ℂ)|\{[a-z ]+ : ℕ\}.*Matrix \(Fin',s))
    ft=sum(1 for s in sigs if '[Fintype' in s or 'Fintype ' in s)
    idx='mixed' if fin and ft else 'Fin' if fin else 'Fintype' if ft else 'none'
    return f,idx

# ---------- rebuild ----------
f2=set()
for fn in ['f2_map','f2_ofsymm','f2_ofmapeq']:
    for l in open(f'/tmp/port/{fn}.txt'):
        f2.add(l.strip()[:-5].replace('/','.'))
F2_DEF={'NLAlib.Probability.Gaussian.Basic.StandardGaussian':'IsStandardGaussian becomes HasLaw/abbrev (F2)',
        'NLAlib.Probability.Rademacher.Core':'IsRademacher becomes HasLaw/abbrev (F2)',
        'NLAlib.Probability.Concentration.Basic.MatrixStatistics':'F2 deletes matrixMeasurableSpace/matrixBorelSpace; the concentration layer rebuilds on the global Matrix instance'}
gm=set(l.strip()[:-5].replace('/','.') for l in open('/tmp/port/f2_gm.txt'))
action={}; target={}; note=collections.defaultdict(list)
for m in content:
    r=rel(m)
    if r.startswith('Sketching.Sparse.'):
        action[m]='rebuild'; note[m].append('F3: Sparse is rebuilt on PMF/Measure and a sketch interface; docs/SKETCH_INTERFACE.md decides rebuild vs drop per file')
    elif r.startswith('Solvers.'):
        action[m]='rebuild'; note[m].append('Solvers finite-sum probability (expErr as weighted path sums): rebuild on Measure/PMF')
    elif m in f2:
        action[m]='rebuild'
        why=[]
        if 'NLAlib/'+r.replace('.','/')+'.lean' in open('/tmp/port/f2_ofsymm.txt').read(): why.append('uses Matrix.of.symm')
        if 'NLAlib/'+r.replace('.','/')+'.lean' in open('/tmp/port/f2_map.txt').read(): why.append('states laws as μ.map X = gaussianMatrix')
        if 'NLAlib/'+r.replace('.','/')+'.lean' in open('/tmp/port/f2_ofmapeq.txt').read(): why.append('has _of_map_eq wrappers')
        lawy=any('law' in x or '_of_map_eq' in x for x in why)
        extra={'NLAlib.Matrix.Structured.Measurable':'; F2 moves its entrywise-measurability bridge into ForMathlib/MeasureTheory/Matrix.lean and this file shrinks to corollaries',
               'NLAlib.Matrix.Subspaces.Stiefel':'; F2 deletes its orthogonalGroup Borel instance'}.get(m,'')
        note[m].append('F2: '+', '.join(why)+('; restate hypotheses as HasLaw X (gaussianMatrix m n) μ with X : Ω → Matrix m n ℝ' if lawy else '; arrays `Fin p → Fin m → ℝ` give way to `Matrix` with the global measurable-space instance')+extra)
    elif m in F2_DEF:
        action[m]='rebuild'; note[m].append(F2_DEF[m])
# ---------- overrides ----------
for k,(a,t,n) in O.items():
    m='NLAlib.'+k
    assert m in GR, m
    if m in action: continue
    note[m].append(n)
    if a=='pending': continue
    action[m]=a; target[m]=t
# ---------- toolkit bundles ----------
name2mod=collections.defaultdict(set)
for x in decls:
    nm=x['name'][len('NLAlib.'):] if x['name'].startswith('NLAlib.') else x['name']
    name2mod[nm].add(x['module'])
thm_mods=collections.defaultdict(set)
for x in decls:
    if x['kind']=='theorem':
        nm=x['name'][len('NLAlib.'):] if x['name'].startswith('NLAlib.') else x['name']
        thm_mods[nm].add(x['module'])
for m in content:
    if m in action: continue
    s=short(m)
    if s.endswith('Toolkit') and not any('toolkit with' in x or 'not a bundle' in x for x in note[m]):
        src=open(ROOT+'/'+path(m)).read()
        ids=set(re.findall(r"[A-Za-z_][A-Za-z0-9_'₀-₉.]*",src))
        comp=collections.Counter()
        for i in ids:
            i=i.replace('NLAlib.','').lstrip('@')
            for mm in name2mod.get(i,[]):
                if mm!=m and mm in thm_mods.get(i,()): comp[mm]+=1
        imps=sorted(comp,key=lambda x:(mdir(x)!=mdir(m),-comp[x]))[:4] or GR[m]['imports']
        action[m]='drop'; target[m]=path(imps[0])
        tags=GR[m]['atlas']
        note[m].append('bundle of `@NLAlib.*` components (brief §4); components are in '+', '.join(short(i) for i in imps)+('; move atlas tag '+', '.join(tags)+' to the main theorem' if tags else ''))
# targets of overrides must exist
for m,t in target.items():
    assert t is None or t[:-5].replace('/','.') in GR, (m,t)

# ---------- clustering ----------
pending=[m for m in content if m not in action]
def scope(m):
    r=rel(m).split('.')
    if r[0]=='ForMathlib': return 'ForMathlib.'+r[1] if len(r)>2 else 'ForMathlib'
    if r[0] in ('Estimation','Sketching'): return r[0]
    return '.'.join(r[:-1])
def group(m):
    sc=scope(m)
    rp=m[len('NLAlib.'+sc)+1:]
    for lab,rx in GROUPS.get(sc,[]):
        if re.match(rx,short(m)) or re.match(rx,rp): return sc+':'+lab
    return sc+(':*' if sc not in GROUPS else ':none')
cl={m:m for m in content}   # module -> cluster id
members={m:{m} for m in content}
size={m:inv[m]['lines'] for m in content}
# quotient adjacency (cluster -> set of clusters it imports)
out=collections.defaultdict(set); inn=collections.defaultdict(set)
for m in content:
    for i in GR[m]['imports']:
        out[m].add(i); inn[i].add(m)
def reach(a,b,skip_direct):
    # is there a path a -> ... -> b in quotient graph (length>=2 if skip_direct)
    st=[x for x in out[a] if not (skip_direct and x==b)]
    seen=set(st)
    while st:
        x=st.pop()
        if x==b: return True
        for y in out[x]:
            if y not in seen: seen.add(y); st.append(y)
    return False
def join(a,b):  # merge cluster b into a
    for x in members[b]: cl[x]=a
    members[a]|=members.pop(b); size[a]+=size.pop(b)
    for y in out.pop(b,set()):
        inn[y].discard(b)
        if y!=a: out[a].add(y); inn[y].add(a)
    for y in inn.pop(b,set()):
        out[y].discard(b)
        if y!=a: out[y].add(a); inn[a].add(y)
    out[a].discard(a); inn[a].discard(a)
def can(a,b):
    return not reach(a,b,True) and not reach(b,a,True)
# pre-join override merges (twins counted at half size)
for m in content:
    if action.get(m)=='merge':
        t=target[m][:-5].replace('/','.')
        a,b=cl[t],cl[m]
        if a!=b:
            if not can(a,b): print('CYCLE override',m,t)
            s=size[b]; join(a,b); size[a]-=s//2
excluded={m for m in content if action.get(m) in ('drop','rebuild')}
# merge loop per group
grp={m:group(m) for m in content}
pend=set(pending)
def cluster_group(c):
    gs={grp[x] for x in members[c] if x in pend or action.get(x)=='merge'}
    return gs
changed=True
while changed:
    changed=False
    cands=[]
    cids={cl[m] for m in pend}
    bydir=collections.defaultdict(list)
    for c in cids: bydir[scope(c)].append(c)
    for sc,cs in bydir.items():
        for i,a in enumerate(cs):
            for b in cs[i+1:]:
                if min(size[a],size[b])>=SMALL: continue
                if size[a]+size[b]>CAP: continue
                ga,gb=cluster_group(a),cluster_group(b)
                same=bool(ga&gb) and not any(g.endswith(':none') for g in ga&gb)
                edge=(b in out[a]) or (a in out[b])
                ungrouped=sc not in GROUPS
                if not (same or (edge and (ungrouped or same)) or (ungrouped)):
                    # in grouped dirs, files in ':none' may join along edges
                    if not (edge and (any(g.endswith(':none') for g in ga|gb))): continue
                pri=(0 if same and edge else 1 if same else 2 if edge else 3)
                cands.append((pri,size[a]+size[b],a,b))
    cands.sort(key=lambda x:(x[0],x[1]))
    for pri,s,a,b in cands:
        if a not in members or b not in members: continue
        if not can(a,b): continue
        if size[a]<size[b]: a,b=b,a
        join(a,b); changed=True
        break
# second pass: tiny leftovers join an import neighbour in the same scope even past the cap
for m in sorted(pend,key=lambda m:inv[m]['lines']):
    c=cl[m]
    if size[c]>=120 or len(members[c])>1: continue
    nb=[x for x in (out[c]|inn[c]) if x in members and scope(x)==scope(c) and any(y in pend for y in members[x]) and size[x]+size[c]<=700]
    nb.sort(key=lambda x:size[x])
    for x in nb:
        if can(x,c):
            join(x,c); break
# ---------- targets ----------
for c,ms in members.items():
    live=[m for m in ms if m not in excluded]
    if not live: continue
    cand=[m for m in live if action.get(m)!='merge'] or live
    t=max(cand,key=lambda m:(short(m) in ('Basic','Core','Defs'),not re.search(r'Toolkit|Properties|Transport|Reindex|FiniteIndex',short(m)),inv[m]['lines']*(1.5 if GR[m]['atlas'] and not m.startswith('NLAlib.ForMathlib') else 1),len(GR[m]['importers'])))
    for m in live:
        if m==t: action[m]='keep'; target.pop(m,None)
        else:
            if action.get(m)!='merge': note[m].append('small file folded into its topic file')
            action[m]='merge'; target[m]=path(t)
# merged override targets that were themselves merged: resolve chains
for m in content:
    if action[m]=='merge':
        t=target[m][:-5].replace('/','.')
        while action[t]=='merge': t=target[t][:-5].replace('/','.')
        target[m]=path(t)
# drops pointing to merged files: point at final target, keep note
for m in content:
    if action[m]=='drop':
        t=target[m][:-5].replace('/','.')
        if action.get(t)=='merge':
            note[m].append('(redundant via '+short(t)+', folded into '+short(target[t][:-5].replace('/','.'))+')')
            target[m]=target[t]
# ---------- extra notes ----------
CORE={'Matrix.Norms.Frobenius','Matrix.Norms.Core','Matrix.Subspaces.Projections','Matrix.Basic.Pseudoinverse','Matrix.Basic.PenroseIdentities','Matrix.Basic.QuadForm','Matrix.Spectral.Core','Matrix.Spectral.SVD','Matrix.Spectral.CourantFischer','Matrix.Spectral.Weyl','Matrix.Spectral.EckartYoung','Matrix.Inequalities.Mirsky'}
for m in content:
    r=rel(m)
    if r in CORE or r.startswith('Matrix.Basic.MoorePenrose'): note[m].append('F1 spectral core: generic over 𝕜 and Fintype after F1')
    if inv[m]['sorry']: note[m].append('contains catalogued sorry scaffold')
    if m in gm and action[m]!='rebuild': note[m].append('F2: gaussianMatrix becomes a Measure on Matrix; primary statement kept, add `_of_hasLaw` corollary')
    imps=GR[m]['importers']
    if imps and all('.Sketching.Sparse.' in i for i in imps) and action[m]!='rebuild': note[m].append('only consumers are in Sketching/Sparse (rebuild)')
for m in content:
    if action[m] in ('keep','merge'):
        bs=[x['name'].split('.')[-1] for x in by[m] if re.search(r'(_properties|_toolkit|_contract)$',x['name'])]
        if bs: note[m].append('contains bundle theorem(s) '+', '.join('`'+x+'`' for x in bs)+': delete at port, tag moves to the main theorem')
absorb=collections.defaultdict(list)
for m in content:
    if action[m]=='merge': absorb[target[m][:-5].replace('/','.')].append(m)
for t,ms in absorb.items():
    tot=inv[t]['lines']+sum(inv[x]['lines'] for x in ms)
    note[t].insert(0,f'topic file: absorbs {len(ms)} file(s) ('+', '.join(short(x) for x in sorted(ms))+f'), {tot} lines before dedup')
out_rows=[]
for m in content:
    f,idx=field_index(m)
    row={'module':m,'lines':inv[m]['lines'],'action':action[m]}
    if action[m] in ('merge','drop'): row['target']=target[m]
    row.update(field=f,index=idx,sorry=inv[m]['sorry'],note='; '.join(note[m]))
    out_rows.append(row)
json.dump(out_rows,open('/tmp/port/manifest.json','w'),ensure_ascii=False,indent=1)
cnt=collections.Counter(r['action'] for r in out_rows)
keeps=sum(1 for r in out_rows if r['action']=='keep')
print(cnt, 'targets(keep)=',keeps)
