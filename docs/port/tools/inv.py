import os,re,json,collections
root='/home/tyler/Documents/prove2me/lean'
files=[]
for dp,dn,fn in os.walk(os.path.join(root,'NLAlib')):
    for f in fn:
        if f.endswith('.lean'): files.append(os.path.join(dp,f))
files.append(os.path.join(root,'NLAlib.lean'))
DECL=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|example|opaque|axiom|irreducible_def|alias|notation|infix|infixl|infixr|prefix|postfix|macro|syntax|elab|macro_rules|abbrev)\b',re.M)
def strip_comments(s):
    # remove block comments (nested approx) and line comments
    out=[];i=0;depth=0;n=len(s)
    while i<n:
        if s.startswith('/-',i): depth+=1;i+=2;continue
        if depth and s.startswith('-/',i): depth-=1;i+=2;continue
        if depth: 
            if s[i]=='\n': out.append('\n')
            i+=1;continue
        if s.startswith('--',i):
            j=s.find('\n',i); i = n if j<0 else j; continue
        out.append(s[i]);i+=1
    return ''.join(out)
inv={}
for p in files:
    rel=os.path.relpath(p,root)
    mod=rel[:-5].replace('/','.')
    s=open(p,encoding='utf8').read()
    c=strip_comments(s)
    imports=re.findall(r'^import\s+(\S+)',s,re.M)
    decls=DECL.findall(c)
    inv[mod]=dict(path=rel,lines=s.count('\n')+(0 if s.endswith('\n') else 1),imports=imports,
        ndecl=len(decls),kinds=dict(collections.Counter(decls)),
        sorry=bool(re.search(r'\bsorry\b',c)),
        hasR='ℝ' in c, hasC='ℂ' in c, hasRC=bool(re.search(r'RCLike|𝕜',c)),
        fin=len(re.findall(r'\bFin\b',c)), fintype=len(re.findall(r'\bFintype\b',c)),
        ofsymm='Matrix.of.symm' in c or 'of.symm' in c,
        mapgauss=bool(re.search(r'\.map\b[^\n]*=\s*(?:gaussianMatrix|stdGaussian|gaussian)',c)),
        mapeq=bool(re.search(r'\bμ\.map\b|Measure\.map\b|\.map\s+\(?fun',c)),
        instMS=bool(re.search(r'instance[^\n:]*(MeasurableSpace|BorelSpace)',c)) or bool(re.search(r'MeasurableSpace\s*\(Matrix',c)),
        gaussianMatrix='gaussianMatrix' in c,
        finiteLaw='FiniteLaw' in c,
        )
json.dump(inv,open('/tmp/port/inv.json','w'),ensure_ascii=False,indent=0)
agg=[m for m,v in inv.items() if v['ndecl']==0]
print(len(inv),'files', len(agg),'no-decl')
for m in agg:
    v=inv[m]
    if not (os.path.isdir(os.path.join(root,v['path'][:-5]))): print('nodecl non-dir',m,v['lines'],len(v['imports']))
