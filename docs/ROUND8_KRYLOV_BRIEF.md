# Round 8: the Krylov refactor

Goal: rebuild `NLAlib/Krylov/` on the conventions of `docs/KRYLOV_DEFINITIONS.md` (read §6
first, then §3.1, §3.2, §3.5, §3.7, §3.11, §3.12, §5) so that GMRES, Jacobi-matrix identities,
block Krylov and preconditioned CG have a home, and close the Krylov candidates marked `now`.
Everything already proved stays proved (same or renamed declarations); nothing is deleted
without a rename entry.

Read before starting: `docs/STANDARDS.md` (§1 naming, §2 layers, §4 docstrings), `CONTRIBUTING.md`
§2–§3, `docs/ROUND1_BRIEF.md` (working rules), `docs/KRYLOV_DEFINITIONS.md`, and the atlas entries
for your ids (`python3 -c "import json;[print(json.dumps(r,indent=1)) for r in json.load(open('atlas/atlas.json'))['results'] if r['id'] in {'gmres-def','residual-polynomial'}]"`).
The statement to prove is the atlas entry's `informal`/`hypotheses`/`conclusion`; deviate only when
Lean forces it and say so in the docstring and the report. Difficulty and priority are in the entry.

## Working rules (in addition to ROUND1_BRIEF)
- **Exclusive file ownership** as listed per group. Create the new files named; do not touch other
  groups' files. The aggregator `NLAlib/Krylov.lean` is the coordinator's: name the modules to add
  in your report. Build your own modules with `lake build NLAlib.Krylov.<Module>` (never a full
  `lake build`); if Lake reports a lock, wait and retry.
- **Additive changes to shared files.** `Krylov/Basic.lean` and `Krylov/Polynomial.lean` are
  imported by everyone: group K-A may add to them but must not rename or change the statement
  of anything already there.
- **Renames** go through `docs/renames/2026-10-10-krylov.json` (`{"old.name": "new.name"}`), owned
  by group K-B; other groups list their renames in the report and K-B merges them. Before `v0.1`
  renames are direct (no deprecation alias), but every use in the library is updated in the same
  round by the group that owns the file using it.
- **Atlas tags.** The declaration that formalizes an atlas result ends its docstring with the tag
  line `atlas: <id>` (`atlas: <id> (partial)` when it covers only part of the statement; several
  ids comma-separated). Tag only ids that exist in `atlas/atlas.json`; propose new ids (with a
  one-paragraph statement and source) in your report and the coordinator adds them. Do not edit
  `atlas/atlas.json`. Helpers mention ids in prose only.
- **Scaffolds.** Prove what you can. A well-known fact that will not close may be a named
  scaffold (`SCAFFOLD: <id>` docstring, `sorry` body, statement checked against the source with
  theorem number); never scaffold something you are not sure is true as written, never an inline
  `sorry`.
- **Conventions that are not optional** (`KRYLOV_DEFINITIONS.md` §6): vectors `n → ℝ`, `[Fintype n]
  [DecidableEq n]`, squared norms as `v ⬝ᵥ v` / `quadForm`, `aeval A p` for polynomials,
  `cfc f A` for matrix functions, `Qᵀ * A * Q` for compressions; degrees `p.degree < q` for membership
  and `p.degree ≤ q` with `p.eval 0 = 1` for residual polynomials, never `natDegree` or `q - 1`;
  method theorems take an arbitrary residual polynomial `p` plus `∀ i, |p.eval (λ i)| ≤ M` and the
  Chebyshev polynomial is plugged in by a corollary; approximant theorems take any `Q` with
  `HasOrthonormalCols Q` and `krylovSpace A b q ≤ LinearMap.range Q.mulVecLin`; structure theorems
  take `D : LanczosDecomp A b q` / `ArnoldiDecomp`; breakdown goes through `krylovGrade`
  (`q ≤ krylovGrade A b`), never a bare `LinearIndependent` hypothesis in a public statement.
- Every file warning-free, lines ≤ 100 characters, `scripts/check_names.py` naming (`head_of_hyp`,
  `exists_…`, `…_iff`, `IsFoo` predicates, `fooBar` defs), module docstring naming the atlas ids.
- Each public declaration: docstring with source and label and the tag. Report at the end per
  ROUND1_BRIEF §Report: every public declaration with status, the exact check commands and
  output, renames, modules to add to the aggregator, proposed new atlas ids, helpers that belong
  elsewhere.

## Groups

**K-A — spaces, grade, the generic minimiser, CG** (owner of `Krylov/Basic.lean`, `Krylov/Polynomial.lean`,
new `Krylov/Grade.lean`, new `Krylov/Minimiser.lean`, `Krylov/CG.lean`, `Matrix/PolynomialCalculus.lean`,
`Polynomial/Basic.lean`, `Polynomial/Approximation.lean`). Other groups poll your first two oleans,
so do them first and build them:
1. `Krylov/Grade.lean` (atlas `krylov-grade`): `krylovGrade A b` (finrank of the span of all
   `A^i b`), `finrank_krylovSpace : finrank (krylovSpace A b q) = min q (krylovGrade A b)`,
   `krylovSpace_eq_of_krylovGrade_le`, `linearIndependent_pow_mulVec_iff_le_krylovGrade`,
   invariance `mulVec_mem_krylovSpace_krylovGrade`, `krylovGrade_le_natDegree_minpoly`,
   `krylovGrade_le_card`, finite termination `sub_mem_krylovSpace_krylovGrade` (§3.1).
   `lake build NLAlib.Krylov.Grade`.
2. `Krylov/Minimiser.lean` (atlas `residual-polynomial` for the polynomial part): `IsAffineMinimiser E x₀ S x`,
   `isAffineMinimiser_iff_isMinOn`, the residual-polynomial lemma promoted from CG.lean's private
   `exists_degree_lt_one_sub_eq_X_mul` into `Polynomial/Basic.lean` under a STANDARDS name, and
   K1 `IsAffineMinimiser.le_aeval` (§3.2). `lake build NLAlib.Krylov.Minimiser`.
3. Generalise `quadForm_aeval_mulVec_le` in `Matrix/PolynomialCalculus.lean` to weight `aeval A g`
   (keep the old statement as a corollary with its name), then the class theorem
   `quadForm_sub_le_of_isAffineMinimiser` (§3.2) in `Minimiser.lean`.
4. `Krylov/CG.lean`: redefine `IsCGIterate` as `IsAffineMinimiser (cgObjective A c) x₀ (krylovSpace …)`
   (same name, `Iff.rfl` to the old body as a lemma), rederive `quadForm_sub_le_of_isCGIterate_of_poly`
   and the κ-bound from the class theorem; dedupe `exists_degree_lt_abs_eval_sub_inv_le`'s
   repeated algebra in `Polynomial/Approximation.lean` against the promoted lemma.
5. If time remains: `richardson-iteration` and `chebyshev-iteration` as `polyIterate` instances (§3.6),
   in `Krylov/PolynomialMethods.lean` (new, yours).

**K-B — graded bases, Arnoldi, Lanczos, Jacobi** (owner of `Krylov/Lanczos.lean`, new
`Krylov/Arnoldi.lean`, new `Krylov/Jacobi.lean`, `docs/renames/2026-10-10-krylov.json`). Poll
`lake build NLAlib.Krylov.Grade` before step 2.
1. `Krylov/Arnoldi.lean` (atlas `graded-krylov-basis-def`, `arnoldi-def`): `IsGradedKrylovBasis A b Q`,
   `structure ArnoldiDecomp A b q := (Q, graded)`, `ArnoldiDecomp.H := Qᵀ * A * Q`,
   `ArnoldiDecomp.restrict`, `H_restrict` (leading principal submatrix), `exists_sign` (uniqueness up
   to column signs), `H_apply_eq_zero_of_add_one_lt` (unreduced Hessenberg), `abbrev LanczosDecomp`,
   `LanczosDecomp.T`, `T_apply_eq_zero_of_one_lt_dist` for symmetric `A` (§3.11–3.12).
2. The canonical witness `arnoldiDecomp A b q (h : q ≤ krylovGrade A b) : ArnoldiDecomp A b q` built
   from today's `lanczosMatrix` (Gram–Schmidt), with `arnoldiDecomp_H_subdiag_pos` (positive
   subdiagonal). Rename `lanczosBasis`/`lanczosMatrix`/`krylovVectors`/`lanczos_apply_eq_zero_of_add_one_lt`
   per KRYLOV_DEFINITIONS §5; record every rename in the renames file and update every use in your
   files (other groups' uses: list them in the report; `Estimation/SLQ.lean`, `Krylov/Ritz.lean`,
   `Krylov/GaussQuadrature.lean` do not use `lanczosMatrix` today, verify with grep).
3. `Krylov/Lanczos.lean` (atlas `arnoldi-relation`, `lanczos-recurrence`): the Arnoldi relation
   `A * D.Q_q = D.Q_q * H_q + h_{q+1,q} • (q_{q+1} e_qᵀ)` via `restrict`, and for symmetric `A` the
   three-term recurrence (column form) with `α_j, β_j` named; this closes `lanczos-recurrence` (drop
   the `(partial)` on the tags you keep).
4. `Krylov/Jacobi.lean` (atlas `lanczos-orthogonal-polynomials`, `jacobi-matrix-identities`, each
   piece may be `(partial)`): the Lanczos polynomials `q_j = p_j(A) b` and their orthonormality in
   `spectralMeasure`, `det (X − T_j)` as the monic orthogonal polynomial, Cauchy interlacing of
   `T_q` in `T_{q+1}` (from `cauchy-interlacing` in `Matrix/CourantFischer.lean`), Gauss nodes and
   weights from the eigendecomposition of `T` (restate `lanczos-gauss-quadrature` through `D.T`).
   Prove in this order; scaffold Christoffel–Darboux and the continued fraction if they do not close.

**K-C — approximants: `f(A)b`, GMRES/MINRES, quadrature exactness** (owner of new
`Krylov/FunctionApprox.lean`, new `Krylov/GMRES.lean`, `Krylov/GaussQuadrature.lean`,
`Matrix/Projections.lean`, `Estimation/SLQ.lean`). Start with 1 (needs nothing new); poll
`lake build NLAlib.Krylov.Minimiser` before 3.
1. `Krylov/FunctionApprox.lean` (atlas `krylov-polynomial-exactness`, `lanczos-fa-error`):
   `krylovFunApprox Q A f b := Q *ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ b))`, `krylovFunApprox_congr` (same
   range ⇒ same value), exactness `krylovFunApprox_eval_eq_aeval` for `p.degree < q`, interpolation
   at the Ritz values (`Lagrange.interpolate` at `(Qᵀ A Q).eigenvalues`; may be `(partial)`), and
   the error bound `‖f(A)b − Q f(T) Qᵀ b‖² ≤ (2E)² ‖b‖²` (§3.7, §3.9). Then
   `lanczos-quadrature-analytic-error` and `lanczos-quadrature-lipschitz-error` only if their
   polynomial inputs exist (they probably do not yet: say so, do not scaffold them).
2. `Matrix/Projections.lean`: `orthonormalBasisMatrix S` for a submodule of `n → ℝ` (orthonormal
   columns, range `= S`, index `Fin (finrank S)`), and receive the matrix helpers that
   `GaussQuadrature.lean`'s docstrings flag as belonging in `Matrix/`
   (`mulVec_transpose_mulVec_of_mem_range`, `isSymm_transpose_mul_mul`, the Rayleigh bounds): move
   them, keep names unless STANDARDS says otherwise, update `GaussQuadrature.lean` and `SLQ.lean`.
   Restate Gauss exactness with `p.degree < 2 * q` (no `0 < q`), keeping the old form as a corollary.
3. `Krylov/GMRES.lean` (atlas `gmres-def`, `minres-bound`, `gmres-diagonalizable` only if a real
   diagonalisable form makes sense, otherwise report): `IsGMRESIterate A c x₀ q x :=
   IsAffineMinimiser (fun y => (c − A y) ⬝ᵥ (c − A y)) x₀ (krylovSpace A (c − A x₀) q)`,
   existence (`Submodule.exists_norm_eq_iInf_of_complete_subspace` or finite-dimensional
   `IsCompact.exists_isMinOn`), the residual-orthogonality characterisation `r_q ⟂ A K_q`, the
   polynomial form `r_q = p(A) r_0`, monotonicity in `q`, the bound `‖r_q‖ ≤ max_i |p(λ_i)| ‖r_0‖` for
   symmetric `A` via the class theorem with `g = X²` (this is MINRES), and the two-interval
   indefinite bound if `two-interval-minimax` exists (it does not yet: report instead).

**K-D — eigenvalues, block spaces, preconditioning** (owner of `Krylov/Ritz.lean`, new
`Krylov/Block.lean`, new `Krylov/Preconditioned.lean`). Poll `lake build NLAlib.Krylov.CG` (K-A step 4)
before step 3.
1. `Krylov/Block.lean` (atlas `block-krylov-subspace`, `subspace-iteration-def`): `blockKrylovSpace A Ω q`,
   `blockKrylovSpace_eq_iSup`, `mem_blockKrylovSpace_iff` (matrix polynomials), `range_aeval_mul_le_blockKrylovSpace`,
   `krylovSpace_col_le_blockKrylovSpace`; `subspaceIterate A Ω k := LinearMap.range ((A ^ k * Ω).mulVecLin)`
   with `subspaceIterate_le_blockKrylovSpace` and invariance under `Ω ↦ Ω * R` (`R` invertible).
2. `Krylov/Ritz.lean` (atlas `krylov-eigenvector-angle`, `kaniel-paige-saad`): the Chebyshev bound on
   the angle between the top eigenvector and `K_q`, then the gap-dependent Kaniel–Paige–Saad bound
   on the largest Ritz value (Saad 2011 Thm 6.4), stated with explicit `tan θ` and
   `inv_eval_T_real_le_of_forall_abs_eval_le`/`chebyshevAmplifier`; keep the existing gap-free
   results as they are (fix their label note: the atlas entry `ritz-value-bounds` says what is proved).
3. `Krylov/Preconditioned.lean` (atlas `preconditioned-cg`, `cgls-lsqr-bound`): preconditioned CG
   stated under the Loewner sandwich `a • P ≼ A ≼ b • P` (`P` positive definite) with the
   `√(b/a)`-rate via the class theorem applied to `P^{-1/2} A P^{-1/2}` (use `CFC.sqrt`/`cfc` or an
   explicit symmetric square root from `Matrix/`), and CGLS/LSQR as CG on `Aᵀ A` with the
   `κ(A)`-rate.
4. If time remains: `subspace-iteration-convergence` needs principal angles (not yet in the library):
   do not scaffold it; report what the statement needs.

## Report
Per ROUND1_BRIEF: declarations with status and tags, exact check commands and output, renames,
modules for the aggregator, proposed new atlas ids with statements, helpers that belong elsewhere,
and what you did not reach.
