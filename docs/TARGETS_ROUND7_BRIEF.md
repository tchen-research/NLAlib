# Targeting round 7: what else the library should want

Purpose: identify foundational statements NLAlib does not yet have, in three areas, ranked by how
many downstream randomized-NLA arguments would cite them. This round *identifies*; it does not
prove. Output is a set of candidate atlas entries.

Repository: `/home/tyler/Documents/prove2me/lean` (Lean 4 / Mathlib). Read first:
- `atlas/README.md` (what an atlas entry is), `atlas/TARGETING.md` (how targets are chosen),
  `atlas/atlas.json` (the catalogue: `results`, `areas`, `sources`), `atlas/schema.json`.
- `atlas/declarations.json` (every public NLAlib declaration with its signature; search it before
  proposing anything) and `atlas/external.json`.
- Mathlib is at `.lake/packages/mathlib/Mathlib`; grep it for existing statements
  (`grep -rn "theorem name" .lake/packages/mathlib/Mathlib`, and look in `Mathlib/LinearAlgebra/Matrix`,
  `Mathlib/Analysis/Matrix`, `Mathlib/Analysis/InnerProductSpace`, `Mathlib/RingTheory/Polynomial/Chebyshev`,
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev`, `Mathlib/Analysis/Polynomial`,
  `Mathlib/LinearAlgebra/Lagrange`).

## Rules
1. **A statement that Mathlib already has is not an atlas result.** If Mathlib has it, say so in
   the report (with the declaration name) and, where a proposed result would use it, list it under
   that result's `mathlib_prereqs`. If Mathlib has a *weaker* or *differently shaped* version, the
   NLAlib statement is a legitimate target: say precisely what the gap is.
2. **Do not propose what NLAlib already has** (check `declarations.json` and the result ids in
   `atlas.json`). A sharper or more general form of an existing result is fine if you say what
   is sharper.
3. **Foundations over algorithms.** Prefer statements that several downstream arguments cite
   (an inequality, an identity, a definition with its characterisations) over end-to-end
   algorithm guarantees. For each candidate name at least one concrete consumer (an existing atlas
   id, or a well-known randomized-NLA theorem) and rank by that.
4. **Precise statements.** Hypotheses explicit, constants explicit (never "O(·)" where a constant
   is known), real matrices with `Fintype` index types unless the statement is intrinsically
   complex. Cite the source with theorem number. If the literature has a sharp form and a simple
   form, propose the sharp form and mention the simple one as a corollary.
5. **Definitions are results.** When a statement needs a definition NLAlib lacks (Arnoldi
   relation, field of values, Chebyshev coefficients, majorization, unitarily invariant norm, …),
   propose a `kind: definition` entry for it with its basic characterisations, and make the
   theorems `depends_on` it.
6. Do not edit any Lean file or `atlas/atlas.json`. Write only your two output files.

## Output (two files, exact names given per group)
1. `docs/targets/<GROUP>.md`: a readable report. For each candidate: statement in words and in
   formulas, source with theorem number, what Mathlib has (declaration names) and what it lacks,
   what NLAlib has that it would build on, its consumers, estimated difficulty 1–5 (1 routine,
   3 a day of work, 5 research-level), and whether to *prove* it or *assume* it (a well-known
   theorem whose statement we are sure of may be assumed so that consumers can be built; see
   `CONTRIBUTING.md` § "Assuming is encouraged").
2. `docs/targets/<GROUP>.json`: `{"results": [...], "sources": [...]}` ready to merge into the
   atlas. Each result follows `atlas/schema.json` with: `id` (lower-kebab, unique, not an existing
   id), `title`, `aliases`, `area` (an existing area id, or a new sub-area you also define under
   `"areas": [{"id","title","parent","order"}]` in the JSON), `kind` (definition | lemma | theorem
   | bound | identity), `status: "candidate"`, `informal` (one or two sentences, KaTeX allowed),
   `hypotheses` (list of strings), `conclusion` (string), `sources` (`[{"source": id, "label":
   "Thm 3.1"}]`, with any new source added to `"sources"` using fields `id, type, title, authors,
   year, url?, doi?, role`), `depends_on` (existing or proposed ids), `mathlib_prereqs`
   (`[{"decl", "present": true|false, "note"}]`), `difficulty`, `priority` (`now` for the handful
   you would do first, else `next`/`later`), `tags`, `notes` (consumers and the prove/assume
   recommendation), `updated_at: "2026-10-10"`. Validate your JSON parses before finishing.

Aim for 12–25 well-chosen candidates per group, not an exhaustive list. Quality of the statement
and of the dependency edges matters more than count.

## Groups

**T1 — Krylov methods beyond CG** (`docs/targets/T1.*`). Arnoldi and the Arnoldi relation
`AQ_k = Q_k H_k + h_{k+1,k} q_{k+1} e_kᵀ`; the Lanczos three-term recurrence as the symmetric case
(NLAlib has `lanczosMatrix` with orthonormality and tridiagonality but not the recurrence
identity, atlas `lanczos-recurrence`); GMRES as residual minimisation over the Krylov space, its
polynomial characterisation `r_k = p_k(A) r_0`, `p_k(0)=1`, and convergence bounds: for
diagonalisable `A` (`κ(V)·min_p max_i |p(λ_i)|`, Saad–Schultz 1986 / Saad 2003 Prop 6.32), for
normal matrices, the field-of-values / Elman bound, the Beckermann–Goreinov–Tyrtyshnikov bound,
the Crouzeix–Palencia constant (assume), and the Greenbaum–Pták–Strakoš "any convergence curve is
possible" result as a caution; MINRES and its Chebyshev bound on indefinite spectra; FOM;
restarted GMRES; Kaniel–Paige–Saad bounds on Ritz values (NLAlib has `ritz-value-bounds`: check
what exactly); Krylov approximation of `f(A)b` with the polynomial-approximation error bound
`‖f(A)b − V f(H) e_1‖ ≤ 2 ‖b‖ min_p ‖f − p‖_{spectrum}` (Saad 1992 Thm 3.3 / Druskin–Knizhnerman),
block Krylov spaces and the randomized block Krylov analysis of Musco–Musco 2015 split into its
deterministic polynomial step; Chebyshev iteration and Richardson as polynomial methods. Source
texts: Saad, *Iterative Methods for Sparse Linear Systems* (2003), Greenbaum 1997 (atlas source
`greenbaum97`), Liesen–Strakoš 2013, Trefethen–Bau (`tb97`), Higham *Functions of Matrices* 2008.

**T2 — Polynomial approximation** (`docs/targets/T2.*`). Trefethen, *Approximation Theory and
Approximation Practice* (2019, atlas source `trefethen19`): Chebyshev series and coefficients
(definition), Theorems 3.1 (convergence of Chebyshev series), 4.1 (aliasing / interpolant
coefficients), 7.1–7.2 (coefficient decay and convergence for functions of bounded variation /
`ν` times differentiable), 8.1–8.2 (geometric decay and convergence for analytic functions on a
Bernstein ellipse: this is atlas `bernstein-ellipse-approx`, currently candidate; propose its
pieces), Lebesgue constants of Chebyshev interpolation (Thm 15.1–15.2), the equioscillation /
Chebyshev alternation characterisation of best approximation (Thm 10.1) and its consequences,
Jackson's theorems (Cheney `cheney66` Ch. 4, Rivlin `rivlin90`), the Bernstein inequality on the
ellipse, convergence of Clenshaw–Curtis and Gauss quadrature (Trefethen Ch. 19), and the specific
approximation problems randomized NLA uses: polynomial approximation of `1/x` on `[a,b]` (NLAlib
has the Chebyshev form `inverse-polynomial-approx`), of `exp(−tx)`, of `x^{−1/2}`, of the sign /
step function (used for spectral projectors and gap-dependent bounds; Eremenko–Yuditskii for the
sharp rate), of `log`, and lower bounds showing optimality (Chebyshev minimax is in NLAlib).
Say for each which is proved in Mathlib (`Polynomial.Chebyshev`, `Lagrange`, Weierstrass
`polynomialFunctions_closure_eq_top` …), which NLAlib has, and the "stronger version" where one
exists (e.g. the sharp constants of Jackson, the `ρ^{-n}` rates). Downstream consumers: Lanczos /
SLQ (`slq-error`), block Krylov (`mm15`), CG, trace estimation of `f(A)`, spectral density.

**T3 — Matrix analysis** (`docs/targets/T3.*`). Horn–Johnson (`hj13`), Bhatia *Matrix Analysis*
(`bhatia97`), Stewart–Sun. NLAlib has: SVD, Eckart–Young (both norms), Weyl, Mirsky,
Courant–Fischer, Cauchy interlacing, von Neumann trace inequality, Moore–Penrose, projections,
Loewner order and the CFC-based matrix functions, Lieb concavity, operator Jensen. Candidates:
singular-value and eigenvalue inequalities (Ky Fan maximum principle, Horn's product inequalities,
Lidskii, Hoffman–Wielandt, Weyl's product/sum inequalities for singular values beyond what is
there), majorization (definition, Schur–Horn, Schur-convexity, Ky Fan norms as sums of singular
values), unitarily invariant norms via symmetric gauge functions and the pinching / Schatten
Hölder inequalities, Davis–Kahan `sin θ` and Wedin theorems (perturbation of invariant subspaces,
heavily cited in randomized NLA), Stewart–Sun perturbation of singular subspaces, Neumann series
and perturbation of inverses and of pseudoinverses (Wedin's `‖A⁺ − B⁺‖` bound), Bauer–Fike,
Gershgorin, Sherman–Morrison–Woodbury, Schur complement facts beyond Mathlib's
`PosSemidef.fromBlocks`, Cholesky / QR / polar decompositions as existence statements with
uniqueness, Kronecker product and `vec`, the Rayleigh quotient and its gradient, condition
numbers and the relative-error bounds for linear systems and least squares (Golub–Van Loan),
Loewner–Heinz and operator monotonicity of `t^r` (Mathlib may have parts under `CFC`), Golden–
Thompson (candidate `golden-thompson`). Check Mathlib carefully: it has the spectral theorem,
`Matrix.PosSemidef`, `Matrix.rank` facts, Schatten/`lp` norms, `Matrix.kroneckerMap`, the Schur
complement block lemmas, `Matrix.cfc`, and recent operator-norm material; name what it has and
what it lacks.

## Report
Your final message: the path of your two files, the count of candidates, the five you would do
first and why, and anything you found already in Mathlib that the atlas should cite.
