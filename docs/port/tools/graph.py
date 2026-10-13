import json,collections
inv=json.load(open('/tmp/port/inv.json'))
d=json.load(open('atlas/declarations.json'))
by=collections.defaultdict(list)
for x in d: by[x['module']].append(x)
content={m for m,v in inv.items() if v['ndecl']>0}
agg={m for m in inv if m not in content}
# resolve imports through aggregators
def resolve(m,seen=None):
    out=set()
    for i in inv.get(m,{}).get('imports',[]):
        if i in content: out.add(i)
        elif i in agg:
            out|=resolve(i)
    return out
imp={m:resolve(m) for m in content}
importers=collections.defaultdict(set)
for m,s in imp.items():
    for i in s: importers[i].add(m)
G={}
for m in content:
    v=inv[m]
    tags=sorted({t for x in by[m] for t in x.get('atlas',[])})
    ptags=sorted({t for x in by[m] for t in x.get('atlas_partial',[])})
    G[m]=dict(imports=sorted(imp[m]),importers=sorted(importers[m]),
      atlas=tags, atlas_partial=ptags, nd=len(by[m]), sorry_dep=any(x['sorry'] for x in by[m]))
json.dump(G,open('/tmp/port/graph.json','w'),ensure_ascii=False)
def dirof(m): return m.rsplit('.',1)[0]
leaf=[m for m in content if not importers[m]]
print('leaves',len(leaf),'untagged leaves',sum(1 for m in leaf if not G[m]['atlas']))
print('agg importing aggs?', sum(1 for m in agg for i in inv[m]['imports'] if i in agg))
