import json,collections,sys
rows=json.load(open('manifest.json')); inv=json.load(open('inv.json')); GR=json.load(open('graph.json'))
A={r['module']:r for r in rows}
def fin(m):
    r=A[m]
    if r['action'] in ('keep','rebuild'): return m
    if r['action']=='merge': return r['target'][:-5].replace('/','.')
    return None
# acyclicity of final graph over keep/rebuild/merge (drops: their imports pass through)
nodes=set(fin(m) for m in A if fin(m))
E=collections.defaultdict(set)
for m in A:
    a=fin(m)
    if not a: continue
    for i in GR[m]['imports']:
        b=fin(i)
        if b and b!=a: E[a].add(b)
# cycle detection
color={}
def dfs(u,stack):
    color[u]=1
    for v in E[u]:
        if color.get(v)==1: print('CYCLE',u,v); return True
        if not color.get(v) and dfs(v,stack): return True
    color[u]=2; return False
import sys; sys.setrecursionlimit(10000)
print('cycle?',any(dfs(u,[]) for u in list(nodes) if not color.get(u)))
cl=collections.defaultdict(list)
for m,r in A.items():
    if r['action']=='keep': cl[m].append(m)
    elif r['action']=='merge': cl[r['target'][:-5].replace('/','.')].append(m)
sz={t:sum(A[m]['lines'] for m in ms) for t,ms in cl.items()}
import statistics
print('final targets',len(cl),'median size',statistics.median(sz.values()),'>600:',sum(1 for v in sz.values() if v>600),'<150:',sum(1 for v in sz.values() if v<150))
if len(sys.argv)>1:
    pref='NLAlib.'+sys.argv[1]
    for t in sorted(cl):
        if t.startswith(pref):
            print(f"{sz[t]:5d} {t[len(pref)+1:]} <= "+', '.join(f"{m.split('.')[-1]}:{A[m]['lines']}" for m in sorted(cl[t]) if m!=t))
    for m,r in sorted(A.items()):
        if m.startswith(pref) and r['action'] in ('drop','rebuild'): print('  ',r['action'],m[len(pref)+1:],'->',r.get('target',''))
