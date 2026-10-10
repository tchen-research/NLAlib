# Audit: what to assume, and what then becomes easy

Read `CONTRIBUTING.md` (§ "Assuming is encouraged"), `docs/STANDARDS.md`, `atlas/README.md` (statuses),
then the atlas (`atlas/atlas.json`) and declaration index (`atlas/declarations.json`) for your areas,
and the Lean sources of your modules. This is a READ-ONLY audit: do not edit any Lean file, the
atlas, or anything outside your one report file.

## Policy being applied
Ideally everything is proved. But a well-known theorem with a precise, standard statement may be
**assumed** (a named `SCAFFOLD:` declaration with a `sorry` body, or an explicit hypothesis) so the
tree below it gets built now. A wrong assumption propagates to every consumer, so the care goes into
the *statement*: exact hypotheses, constants, degenerate cases, a source with theorem number. Link
status in the viewer is "the implication is machine-checked", so a scaffold at the top does not
block green links below it.

## What to produce
Write `docs/audit/<group>.md` with three sections, each a table or list with the fields shown.

**A. Theorems to assume.** Well-known results, not in Mathlib (check: `grep -rn` in
`.lake/packages/mathlib/Mathlib` and name what you find), not yet in NLAlib, that unlock the most
downstream atlas results. For each: proposed atlas id (existing id if it is already catalogued) ·
one-line statement · a precise Lean-ready statement in NLAlib's vocabulary (`frobSq`, `specNorm`,
`singularValues`, `IsSVD`, `pinvL/pinvR`, `HasOrthonormalCols`, `gaussianMatrix`, `krylovSpace`,
`quadForm`, `Polynomial.Chebyshev.T`, …; `[Fintype ι]` unless a Gaussian law is involved) · source
with theorem number · confidence that the statement as written is correct and standard (high /
medium; say what could be subtly wrong: constants, strictness, degenerate cases) · the atlas results
it unlocks (ids) · module file where the scaffold should live · whether a full proof is realistic
soon (difficulty 1–5) so it is a scaffold, not a permanent assumption.

**B. Easy proofs once A is in place.** Atlas results (candidate / planned / stated / assumed) in
your areas that an Opus agent could prove in one session (difficulty ≤ 2) given the assumptions in A
and the existing library. For each: atlas id · what it follows from (atlas ids, NLAlib declaration
names, Mathlib names) · sketch of the proof in 2–4 lines · estimated difficulty · the file it goes in.
Include results not yet in the atlas if they are obvious reusable corollaries (mark "new").

**C. Easy proofs with no new assumptions.** Same format, for results provable now from what exists.
Also list any `assumed`/`scaffold` result whose Lean statement you believe is wrong or non-standard.

Rank each section by downstream reuse (count the atlas `depends_on` in-edges, transitive). Be
concrete: an item without a precise statement or a specific dependency list is not useful. Check
Mathlib for every item in A; many classical matrix facts are there under unfamiliar names
(`Matrix.IsHermitian.eigenvalues`, `LinearMap.singularValues`, `Matrix.PosSemidef`, `cfc`,
`Matrix.rank`, `Polynomial.Chebyshev`, `ProbabilityTheory.*`).

## Groups
- **G0** Matrix analysis and polynomial approximation (areas `matrix*`, `polynomial*`; modules
  `NLAlib/Matrix/**`, `NLAlib/Polynomial/**`). Also the deterministic hypotheses of the LRA
  project's assumed results (`von-neumann-trace`, `hmt-9-1-spectral`).
- **G1** Concentration and Gaussian (areas `concentration*`, `gaussian*`; modules
  `NLAlib/Concentration/**`, `NLAlib/Gaussian/**`).
- **G2** Sketching and low-rank approximation (areas `sketching*`, `lra*`; modules
  `NLAlib/Sketching/**`, `NLAlib/LowRank/**`), including `jl-distributional` (the one remaining
  scaffold) and the Gaussian OSE / AMM chain.
- **G3** Krylov, estimation, solvers (areas `krylov`, `estimation`, `solvers`; modules
  `NLAlib/Krylov/**`, `NLAlib/Estimation/**`, `NLAlib/Solvers/**`), including CG from the
  Chebyshev minimax, Lanczos, Gauss quadrature, Hutchinson tails, Kaczmarz.

Final message: the path of your report and a 10-line summary (top 3 of each section).
