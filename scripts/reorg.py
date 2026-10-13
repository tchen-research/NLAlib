#!/usr/bin/env python3
"""Reorganise the NLAlib tree from mapping tables (docs/reorg/mapping/*.json).

  python3 scripts/reorg.py --check docs/reorg/mapping/M1.json   # one table: structure checks
  python3 scripts/reorg.py --check-all                           # all tables: coverage, layers, cycles
  python3 scripts/reorg.py --apply                               # git mv, rewrite imports, aggregators

Content files live only in leaf directories of TREE; every `<Dir>.lean` is a generated aggregator.
Declaration names never change (one flat `namespace NLAlib`); only paths and import lines do.
"""
import json, pathlib, re, subprocess, sys, collections
ROOT = pathlib.Path(__file__).resolve().parent.parent
TREE = """ForMathlib/Algebra ForMathlib/Analysis ForMathlib/MeasureTheory ForMathlib/Probability ForMathlib/Topology ForMathlib/LinearAlgebra ForMathlib/Order ForMathlib/Logic ForMathlib/Data ForMathlib/Combinatorics
Matrix/Basic Matrix/Norms Matrix/Spectral Matrix/Subspaces Matrix/Factorizations Matrix/Perturbation Matrix/Inequalities Matrix/OperatorTheory Matrix/Functions Matrix/Structured Matrix/Calculus
Polynomial/Chebyshev Polynomial/Interpolation Polynomial/BestApproximation Polynomial/FunctionApproximation
Probability/Basic Probability/Moments Probability/Sampling Probability/SubGaussian Probability/Rademacher Probability/ChiSquare
Probability/Gaussian/Basic Probability/Gaussian/Calculus Probability/Gaussian/Moments Probability/Gaussian/Comparison Probability/Gaussian/Concentration
Probability/Concentration/Basic Probability/Concentration/Scalar Probability/Concentration/Matrix Probability/Concentration/QuadraticForms Probability/Concentration/Entropy Probability/Concentration/Martingales
RandomMatrix/Basic RandomMatrix/General RandomMatrix/Spectral RandomMatrix/SubGaussian RandomMatrix/Rademacher RandomMatrix/Haar RandomMatrix/Covariance
RandomMatrix/Gaussian/Basic RandomMatrix/Gaussian/Invariance RandomMatrix/Gaussian/Moments RandomMatrix/Gaussian/Spectral RandomMatrix/Gaussian/Wishart RandomMatrix/Gaussian/InverseMoments
Krylov/Spaces Krylov/Processes Krylov/Solvers Krylov/Spectral Krylov/Quadrature Krylov/MatrixFunctions
Sketching/Basic Sketching/Gaussian Sketching/Structured Sketching/Sparse Sketching/Sparse/FiniteLaw Sketching/Sparse/MomentMethod Sketching/Sparse/IIDComparison Sketching/Sparse/FockModel Sketching/Sparse/Bands Sketching/Sparse/Bands/Directional Sketching/Sparse/Bands/Heavy Sketching/Sparse/Bands/Light Sketching/Sparse/Bands/Mixed Sketching/Sampling
Sketching/Properties/JL Sketching/Properties/SubspaceEmbedding Sketching/Properties/ApproxMatrixMultiplication
LowRank/Structural LowRank/RangeFinding LowRank/RandomizedSVD LowRank/Nystrom LowRank/Cholesky LowRank/PolynomialMethods LowRank/Sampling
Estimation/Basic Estimation/Trace Estimation/Diagonal Estimation/QuadraticForms Estimation/Quadrature Estimation/Spectral
Solvers/Kaczmarz Solvers/SketchAndSolve Solvers/SketchAndProject Solvers/Preconditioning""".split()
LEAVES = set(TREE)
LAYER = {"ForMathlib": -1, "Matrix": 0, "Polynomial": 0, "Probability": 1, "Krylov": 1, "RandomMatrix": 2,
         "Sketching": 3, "LowRank": 4, "Estimation": 4, "Solvers": 5}
GROUPS = {"M1": ["Matrix"], "M2": ["Concentration"], "M3": ["Gaussian"], "M4": ["Sketching"],
          "M5": ["Krylov", "Polynomial", "ForMathlib"], "M6": ["LowRank", "Estimation", "Solvers"]}
DECL = re.compile(r"^\s*(@\[[^\]]*\]\s*)?(noncomputable\s+|protected\s+|private\s+)*(theorem|lemma|def|abbrev|structure|instance|inductive|class|opaque|axiom)\s", re.M)

def is_aggregator(p):   # declaration-free AND the aggregator of a sibling directory of the same name
    return (not DECL.search(p.read_text())) and p.with_suffix("").is_dir()
def content_files():
    return sorted(p for p in (ROOT / "NLAlib").rglob("*.lean") if not is_aggregator(p))
def mod_of(path):      # NLAlib/A/B.lean -> NLAlib.A.B
    return ".".join(pathlib.Path(path).with_suffix("").parts)
def imports_of(p):
    return [m.group(1) for m in re.finditer(r"^import (NLAlib(?:\.\w+)*)\s*$", p.read_text(), re.M)]
def leaf_of(dest):
    return "/".join(pathlib.Path(dest).parts[1:-1])
def top_of(path):
    return pathlib.Path(path).parts[1]
def check_table(path, verbose=True):
    j = json.load(open(path)); moves = j["moves"]; problems = []
    group = j.get("group"); srcdirs = GROUPS.get(group, [])
    dests = collections.Counter(d for d in moves.values() if d)
    for src, dst in moves.items():
        sp = ROOT / src
        if not sp.exists(): problems.append(f"missing source {src}"); continue
        if dst is None:
            if DECL.search(sp.read_text()): problems.append(f"cannot delete a file with declarations: {src}")
            continue
        dp = pathlib.Path(dst)
        if not src.startswith("NLAlib/") or not dst.startswith("NLAlib/"): problems.append(f"paths must start with NLAlib/: {src} -> {dst}"); continue
        if dp.suffix != ".lean": problems.append(f"not a .lean destination: {dst}")
        leaf = leaf_of(dst)
        if leaf not in LEAVES and not any(leaf.startswith(l + "/") for l in LEAVES if l.startswith("ForMathlib/")):
            problems.append(f"destination not in a leaf directory of the target tree: {dst}")
        if not re.match(r"^[A-Z][A-Za-z0-9]*\.lean$", dp.name): problems.append(f"destination base name not UpperCamelCase: {dst}")
        if dests[dst] > 1: problems.append(f"two files map to {dst}")
    if srcdirs:
        expected = {str(p.relative_to(ROOT)) for d in srcdirs for p in (ROOT / "NLAlib" / d).rglob("*.lean") if not is_aggregator(p) and not in_tree(str(p.relative_to(ROOT)))}
        unmapped = sorted(expected - set(moves)); extra = sorted(set(moves) - expected)
        if unmapped: problems.append(f"{len(unmapped)} content files of group {group} not mapped: " + ", ".join(unmapped[:15]) + (" …" if len(unmapped) > 15 else ""))
        for e in extra:
            if is_aggregator(ROOT / e): problems.append(f"aggregator (no declarations) should not be mapped: {e}")
            else: problems.append(f"file outside group {group}: {e}")
    if verbose:
        by = collections.Counter(leaf_of(d) if d else "(deleted)" for d in moves.values())
        print(f"{path}: {len(moves)} moves -> " + ", ".join(f"{k} {v}" for k, v in sorted(by.items())))
        print("problems:\n  " + "\n  ".join(problems) if problems else "table OK")
    return j, problems
def in_tree(path):
    leaf = leaf_of(path)
    return leaf in LEAVES or any(leaf.startswith(l + "/") for l in LEAVES if l.startswith("ForMathlib/"))
def all_moves():
    moves = {}; problems = []
    for p in content_files():   # already placed files map to themselves
        rel = str(p.relative_to(ROOT))
        if in_tree(rel): moves[rel] = rel
    for p in sorted((ROOT / "docs/reorg/mapping").glob("*.json")):
        j, pr = check_table(p, verbose=False); problems += [f"{p.name}: {x}" for x in pr]
        for s, d in j["moves"].items():
            if s in moves and moves[s] != d and moves[s] != s: problems.append(f"{s} mapped twice ({moves[s]} and {d})")
            moves[s] = d   # an explicit table entry overrides the implicit identity
    return moves, problems
def agg_modmap(moves, aggs):
    """old aggregator module -> new aggregator module of the directory most of its content moved to"""
    m = {}
    for a in aggs:
        old_dir = a.replace(".", "/"); dirs = collections.Counter()
        for s, d in moves.items():
            if d and s.startswith(old_dir + "/"): dirs[".".join(pathlib.Path(d).parts[:-1])] += 1
        if dirs: m[a] = dirs.most_common(1)[0][0]   # aggregator of the new directory holding most of its content
    return m
def check_all():
    moves, problems = all_moves()
    files = {str(p.relative_to(ROOT)) for p in content_files()}
    missing = sorted(files - set(moves))
    if missing: problems.append(f"{len(missing)} content files unmapped: " + ", ".join(missing[:20]) + (" …" if len(missing) > 20 else ""))
    aggs = {mod_of(str(p.relative_to(ROOT))) for p in (ROOT / "NLAlib").rglob("*.lean") if is_aggregator(p)}
    deleted = {mod_of(s) for s, d in moves.items() if d is None}; moves = {s: d for s, d in moves.items() if d}
    modmap = {mod_of(s): mod_of(d) for s, d in moves.items()}; modmap.update(agg_modmap(moves, aggs))
    # the new graph: content modules, plus one aggregator per new directory (imports everything beneath it)
    edges = collections.defaultdict(set); new_dirs = set()
    for s, d in moves.items():
        dm = mod_of(d); parts = pathlib.Path(d).parts   # NLAlib, A, B, File.lean
        for i in range(2, len(parts)):
            agg = ".".join(parts[:i]); new_dirs.add(agg)
            edges[agg].add(".".join(parts[:i + 1]) if i + 1 < len(parts) else dm)
        for imp in imports_of(ROOT / s):
            if imp in deleted: continue
            tgt = modmap.get(imp)
            if tgt is None:
                saved = ROOT / "docs/reorg/modmap.json"
                tgt = json.load(open(saved))["modules"].get(imp) if saved.exists() else None
                if tgt is not None: tgt = modmap.get(tgt, tgt)     # chain: old name -> previous home -> current move
                if tgt is None and (ROOT / (imp.replace(".", "/") + ".lean")).exists(): tgt = imp   # an aggregator of the new tree
            if tgt is None: problems.append(f"{s}: import {imp} has no new home"); continue
            if LAYER[d.split("/")[1]] < LAYER[tgt.split(".")[1]]: problems.append(f"layer violation: {d} imports {tgt}")
            edges[dm].add(tgt)
    WHITE, GREY, BLACK = 0, 1, 2; color = collections.defaultdict(int); cyc = []
    sys.setrecursionlimit(10000)
    def dfs(u, stack):
        color[u] = GREY; stack.append(u)
        for v in sorted(edges.get(u, ())):
            if color[v] == GREY: cyc.append(stack[stack.index(v):] + [v])
            elif color[v] == WHITE: dfs(v, stack)
        stack.pop(); color[u] = BLACK
    for u in sorted(edges):
        if color[u] == WHITE: dfs(u, [])
    for c in cyc[:5]: problems.append("cycle: " + " -> ".join(c))
    agg_uses = collections.Counter(imp for s in moves for imp in imports_of(ROOT / s) if imp in aggs)
    print(f"{len(moves)} moves over {len(files)} content files; {len(aggs)} old aggregators; {len(new_dirs)} new directories; content files importing old aggregators: {dict(agg_uses)}")
    print("problems:\n  " + "\n  ".join(problems[:40]) if problems else "all tables OK")
    return all_moves()[0], aggs, problems
def prune_aggregators():
    """Delete generated aggregator files whose directory is gone or holds no declarations, then empty directories."""
    removed = []
    for p in sorted((ROOT / "NLAlib").rglob("*.lean")):
        t = p.read_text()
        if DECL.search(t): continue
        d = p.with_suffix("")
        generated = "generated by `scripts/reorg.py`" in t
        if (not d.is_dir() or not any(DECL.search(q.read_text()) for q in d.rglob("*.lean"))):
            if not generated and not d.is_dir(): continue      # hand-written shim: keep
            tracked = subprocess.run(["git", "ls-files", "--error-unmatch", str(p.relative_to(ROOT))], cwd=ROOT, capture_output=True).returncode == 0
            subprocess.run(["git", "rm", "-q", "-f", str(p.relative_to(ROOT))] if tracked else ["rm", str(p)], cwd=ROOT, check=True); removed.append(p)
    for _ in range(6):
        for d in sorted((ROOT / "NLAlib").rglob("*"), key=lambda q: -len(q.parts)):
            if d.is_dir() and not any(d.iterdir()): d.rmdir()
    return removed
def gen_aggregators(root_dir):
    """Write <Dir>.lean for every directory under NLAlib/ (recursively) importing its files and sub-aggregators."""
    removed = prune_aggregators()
    made = []
    for d in sorted({p for p in (ROOT / "NLAlib").rglob("*") if p.is_dir()} | {ROOT / "NLAlib"}, key=lambda p: len(p.parts), reverse=True):
        if d == ROOT / "NLAlib": continue
        files = sorted(p for p in d.glob("*.lean"))
        subs = sorted(p for p in d.iterdir() if p.is_dir())
        mods = [mod_of(str(p.relative_to(ROOT))) for p in files]
        mods += [mod_of(str(p.relative_to(ROOT))) for p in subs]   # NLAlib/X/Sub -> NLAlib.X.Sub (its aggregator)
        agg = d.with_suffix(".lean")
        rel = str(d.relative_to(ROOT / "NLAlib"))
        text = "\n".join(f"import {m}" for m in sorted(set(mods))) + f"\n\n/-! # `{rel}`\n\nAggregator for `NLAlib/{rel}/` (generated by `scripts/reorg.py`; edit the files, not this list). -/\n"
        agg.write_text(text); made.append(agg)
    tops = sorted(p for p in (ROOT / "NLAlib").iterdir() if p.is_dir())
    (ROOT / "NLAlib.lean").write_text("\n".join(f"import NLAlib.{p.name}" for p in tops) + "\n")
    return made
def apply():
    moves, aggs, problems = check_all()
    if problems: print("refusing to apply with problems"); sys.exit(1)
    deleted = {mod_of(s) for s, d in moves.items() if d is None}
    for s_, d in list(moves.items()):
        if d is None: subprocess.run(["git", "rm", "-q", s_], cwd=ROOT, check=True)
    moves = {s_: d for s_, d in moves.items() if d}
    # 1. module rename map: content modules; old aggregators -> new aggregator of the directory most of their content moved to
    modmap = {mod_of(s): mod_of(d) for s, d in moves.items() if s != d}; modmap.update(agg_modmap(moves, aggs))
    saved = ROOT / "docs/reorg/modmap.json"
    if saved.exists():
        for k, v in json.load(open(saved))["modules"].items(): modmap.setdefault(k, modmap.get(v, v))   # compose with earlier moves
    # 2. git mv
    for s, d in moves.items():
        if s == d: continue
        (ROOT / d).parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "mv", s, d], cwd=ROOT, check=True)
    # 3. delete old aggregators
    for a in aggs:
        p = ROOT / (a.replace(".", "/") + ".lean")
        if p.exists(): subprocess.run(["git", "rm", "-q", "--ignore-unmatch", str(p.relative_to(ROOT))], cwd=ROOT, check=False); p.unlink(missing_ok=True)
    # 4. rewrite imports everywhere
    pat = re.compile(r"^import (NLAlib(?:\.\w+)*)\s*$", re.M)
    for p in list((ROOT / "NLAlib").rglob("*.lean")) + list((ROOT / "scripts").glob("*.lean")):
        s = p.read_text(); t = pat.sub(lambda m: "" if m.group(1) in deleted else "import " + modmap.get(m.group(1), m.group(1)), s)
        if t != s: p.write_text(t)
    # 5. aggregators
    made = gen_aggregators(ROOT / "NLAlib")
    # 6. layer map
    cl = ROOT / "scripts/check_layers.py"; s = cl.read_text()
    s = re.sub(r"LAYER = \{.*?\}", "LAYER = " + json.dumps(LAYER), s, flags=re.S); cl.write_text(s)
    # 6b. old module names inside Lean docstrings (content files only; generated aggregators are rebuilt from the tree)
    pat_doc = re.compile(r"\bNLAlib(?:\.\w+)+\b")
    for p in list((ROOT / "NLAlib").rglob("*.lean")) + list((ROOT / "scripts").glob("*.lean")):
        if "generated by `scripts/reorg.py`" in p.read_text(): continue
        t = p.read_text(); u = pat_doc.sub(lambda m: modmap.get(m.group(0), m.group(0)), t)
        if u != t: p.write_text(u)
    # 7. module names in docs and atlas area modules/layers
    pat_md = re.compile(r"\bNLAlib(?:\.\w+)+\b")
    for p in list((ROOT / "docs").rglob("*.md")) + [ROOT / "README.md", ROOT / "CONTRIBUTING.md", ROOT / "AGENTS.md", ROOT / "atlas/README.md", ROOT / "atlas/TARGETING.md"]:
        if not p.exists(): continue
        t = p.read_text(); u = pat_md.sub(lambda m: modmap.get(m.group(0), m.group(0)), t)
        if u != t: p.write_text(u)
    atlas_p = ROOT / "atlas/atlas.json"; atlas = json.load(open(atlas_p))
    AREA_MOD = {"concentration": ("NLAlib/Probability", 1), "gaussian": ("NLAlib/RandomMatrix", 2)}
    for a in atlas["areas"]:
        if a["id"] in AREA_MOD: a["module"], a["layer"] = AREA_MOD[a["id"]]
    json.dump(atlas, open(atlas_p, "w"), ensure_ascii=False, indent=1); open(atlas_p, "a").write("\n")
    json.dump({"modules": modmap}, open(ROOT / "docs/reorg/modmap.json", "w"), indent=1)
    print(f"moved {len(moves)} files, removed {len(aggs)} old aggregators, wrote {len(made)} aggregators; module map in docs/reorg/modmap.json")
if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["--check"]: check_table(a[1])
    elif a[:1] == ["--check-all"]: check_all()
    elif a[:1] == ["--apply"]: apply()
    elif a[:1] == ["--gen-aggregators"]:
        made = gen_aggregators(ROOT / "NLAlib"); print(f"regenerated {len(made)} aggregators")
    else: print(__doc__)
