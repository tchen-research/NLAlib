import json,re,collections,os
d=json.load(open('atlas/declarations.json'))
inv=json.load(open('/tmp/port/inv.json'))
by=collections.defaultdict(list)
for x in d: by[x['module']].append(x)
name2mod={}
for x in d: name2mod.setdefault(x['name'].split('.')[-1],[]).append(x['module'])
def norm(n):
    n=n.split('.')[-1]
    n=re.sub(r'^complex_','',n); n=re.sub(r'_complex\b','',n)
    n=re.sub(r'^complex([A-Z])',lambda m:m.group(1).lower(),n)
    n=n.replace('Complex','').replace('unitary','orthogonal').replace('conjTranspose','transpose')
    return n
allnames=collections.defaultdict(set)
for x in d:
    allnames[norm(x['name'])].add(x['module'])
for m in sorted(inv):
    short=m.split('.')[-1]
    if not short.startswith('Complex') or 'Sparse' in m or inv[m]['ndecl']==0: continue
    sib=m.rsplit('.',1)[0]+'.'+short[len('Complex'):]
    names=[x['name'] for x in by[m]]
    hits=collections.Counter()
    nh=0
    for n in names:
        mods=allnames[norm(n)]-{m}
        mods={mm for mm in mods if 'Complex' not in mm.split('.')[-1]}
        if mods: nh+=1
        for mm in mods: hits[mm]+=1
    print(m.replace('NLAlib.',''), inv[m]['lines'], 'sib' if sib in inv else '-', f'{nh}/{len(names)}', hits.most_common(3))
