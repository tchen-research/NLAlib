# Dedup round phase 2, agent P_krylov (Krylov, Polynomial, Solvers, Estimation)

Rename table: `docs/renames/2026-10-12-dedup-P_krylov.json` (12 entries). Atlas tags: the only
dropped declaration carrying an `atlas:` line was `eval_derivative_T_real_one`
(`atlas: chebyshev-second-kind`); its keeper is Mathlib, so the tag could not travel (the entry keeps
its other formalizations `abs_eval_U_real_le`, `abs_eval_derivative_T_real_le`). Moved declarations
keep their tags; `quadForm_sub_le_of_isCGIterate` keeps `atlas: cg-convergence`.

## Findings executed

| id | keeper (home) | dropped / moved | files touched |
|---|---|---|---|
| krylov#0 | `frobSq_eq_sum_sq_eigenvalues` (Perturbation/EigenvalueTrace) | deleted `frobSq_eq_sum_eigenvalues_sq` (it had no users left after F2b) | Estimation/Trace/HutchinsonTail |
| krylov#1 | — | already done by P_norms (matrix_norms#26) | — |
| krylov#2 | `pow_mul_eq_mul_pow_of_mul_eq` (Functions/PolynomialIntertwining) | deleted `mul_pow_eq_pow_mul_of_mul_eq` | Bidiagonalization, Spaces/Polynomial |
| krylov#3 | Mathlib `mul_pow_mul` | deleted `mul_pow_mul_eq_mul_mul_pow` | Solvers/Preconditioned |
| krylov#6, #7 | `transpose_mulVec_pow_mulVec_eq`, `transpose_mulVec_aeval_mulVec_eq` moved FunctionApprox → Quadrature/GaussQuadrature (tag `krylov-polynomial-exactness (partial)` travels) | deleted `LanczosDecomp.transpose_Q_mulVec_pow_mulVec`, `LanczosDecomp.transpose_Q_mulVec_aeval_mulVec`; the two Jacobi uses now apply the general lemma with `D.hasOrthonormalCols b D.range_Q.ge (natDegree_le_iff_degree_le.1 _)` then `← ArnoldiDecomp.H_def` | GaussQuadrature, FunctionApprox, Jacobi |
| krylov#8, #25 | new file **`Matrix/Functions/CFCQuadratic.lean`** (imports PolynomialCalculus, HermitianFunctionalCalculus, Lagrange) holding `eigenvectorBasis_dotProduct_eigenvectorBasis`, `eigenvectorBasis_dotProduct_aeval_mulVec` (from Ritz), `eigenvalues_eq_dotProduct_mulVec`, `mul_dotProduct_le_dotProduct_mulVec_of_eigenvalues`, `dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues`, `abs_dotProduct_cfc_mulVec_le` (from GaussQuadrature), `dotProduct_cfc_mulVec_eq_sum` (from SpectralMeasure), `cfc_eq_aeval_of_forall_eval_eq`, `cfc_eq_aeval_interpolate`, `dotProduct_cfc_mulVec_self_le` and `eval_interpolate_eigenvalues` (was private, now public: FunctionApprox's private error lemma uses it) (from FunctionApprox) | deleted `eigenvectorBasis_dotProduct_self` (uses: `by simpa using eigenvectorBasis_dotProduct_eigenvectorBasis hA i i`, or `…, if_pos rfl` in a `rw`) | SpectralMeasure (imports CFCQuadratic instead of PolynomialCalculus), GaussQuadrature, FunctionApprox, Ritz, Preconditioned |
| krylov#11 | Arnoldi.lean imports `Matrix.Subspaces.Projections` instead of `Krylov.Quadrature.GaussQuadrature`; Lanczos.lean imports GaussQuadrature | — | Arnoldi, Lanczos |
| krylov#12 | — | **deleted file `Estimation/Trace/Hutchinson.lean`** (import-only shim) | aggregators regenerated; QuadForm docstring reference updated (reference edit) |
| krylov#13 | `Kaczmarz.step_sub_mem_range_of_sub_mem_range` moved KaczmarzRowSpace → KaczmarzExtensions | deleted `Kaczmarz.step_sub_mem_range` | KaczmarzExtensions, KaczmarzRowSpace |
| krylov#14 | `Kaczmarz.rate_nonneg_of_lower_bound_on_range` moved KaczmarzRowSpace → Kaczmarz/Core | deleted `Kaczmarz.rate_nonneg`; uses take `(fun v _ => hσ v)` | Core, KaczmarzExtensions, KaczmarzRowSpace |
| krylov#16 | Mathlib `Polynomial.Chebyshev.derivative_T_eval_one` | deleted `eval_derivative_T_real_one` (use: `rwa [derivative_T_eval_one, Int.cast_natCast]`) | Chebyshev/Growth |
| krylov#17 | Mathlib `Real.sum_le_exp_of_nonneg` | deleted `sum_pow_div_factorial_le_exp` | FunctionApproximation/Exponential |
| krylov#18 | public `chebyshevZero` API (`chebyshevZero_injective`, `eval_T_real_chebyshevZero`, `nodal_chebyshevZero`, `chebyshevZero_mem_Icc`) | deleted Markov's private `zero`, `injOn_zero`, `eval_T_zero`, `T_eq_C_mul_nodal`; Schur/Bernstein interpolation now runs over `Finset.univ : Finset (Fin q)` | Chebyshev/Markov (imports Interpolation/Lagrange) |
| krylov#23 | `krylovSpace_mulVec_le_succ`, `mulVec_mem_krylovSpace_of_mul_eq` moved Bidiagonalization → Spaces/Polynomial (Polynomial now imports Functions/PolynomialIntertwining, layer 0); `eq_zero_of_aeval_mulVec_eq_zero` moved Jacobi → Spaces/Grade | moves only | Bidiagonalization, Spaces/Polynomial, Spaces/Grade, Jacobi |
| krylov#24 | `arnoldiBasis_dotProduct_of_ne`, `arnoldiBasis_eq_zero_of_krylovGrade_le` moved LanczosRecurrence → ArnoldiProcess (the second reproved in 3 lines with `graded.eq_sum_of_mem`, since `ArnoldiDecomp.eq_of_forall_col_dotProduct_eq` lives downstream in Lanczos) | moves only | LanczosRecurrence, ArnoldiProcess |
| krylov#31 | `quadForm_sub_le_of_isCGIterate` now takes `a ≤ b` (old `_of_le` body, strict case inlined from the old strict proof; keeps `atlas: cg-convergence`) | deleted `quadForm_sub_le_of_isCGIterate_of_le` | CG, Preconditioned |
| krylov#32 | `def ArnoldiDecomp.Hbar` moved GMRESArnoldi → Lanczos; `mul_restrict_Q_eq_mul` now states `A * (D.restrict _).Q = D.Q * D.Hbar` | deleted `ArnoldiDecomp.mul_restrict_Q_eq_mul_Hbar` | Lanczos, GMRESArnoldi |

Extra moves along the way (same files, same rationale): `integral_eval_mul_eval_spectralMeasure`
Jacobi → Quadrature/SpectralMeasure (its docstring said it belonged there);
`eigenvectorBasis_dotProduct_aeval_mulVec` Ritz → CFCQuadratic. "Belongs in …" remarks removed
from the moved docstrings; module docstrings updated.

## Skipped

- krylov#15: excluded by the task (new content).
- krylov#20 (`IsUpperHessenberg.sub_smul_one`, `.add_smul_one`): the target has moved. F2c put
  `IsUpperHessenberg` in `Matrix/Structured/Hessenberg.lean`, which belongs to P_basic, who is still
  working. Moving lemmas into it is not a reference edit, so both stay in Krylov/Spectral/QRAlgorithm.
  Follow-up: append them to Structured/Hessenberg.
- krylov#28 (`IsStandardGaussian`/`IsRademacher` API): left for P_prob as instructed. As of this
  report the four lemmas are still in HutchinsonLaws (`aemeasurable_of_isStandardGaussian`,
  `aemeasurable_of_isRademacher`), HutchinsonTail (`hasSubgaussianMGF_of_isStandardGaussian`) and
  SLQRademacher (`ae_sq_eq_one_of_isRademacher`).
- krylov#30 (`frobConditionNumber`): optional, and not trivial in practice. Moving it into
  Perturbation/ConditionNumber (not my file) would make KaczmarzProbability import
  ConditionNumber's heavy chain (FiniteIndexTransport, FunctionalCalculusEigenvalues). Left in place.

## Files created / deleted

- Created: `NLAlib/Matrix/Functions/CFCQuadratic.lean`.
- Deleted: `NLAlib/Estimation/Trace/Hutchinson.lean`.
- Ran `python3 scripts/reorg.py --gen-aggregators`. It regenerated 93 aggregators, including pending
  changes from other agents.

## For the coordinator

- Atlas: re-run ExtractDecls / sync_atlas. `chebyshev-second-kind` loses the formalization
  `NLAlib.eval_derivative_T_real_one`; Mathlib's `derivative_T_eval_one` can be cited under
  `mathlib_prereqs`.
- HutchinsonTail still imports `Krylov.Quadrature.GaussQuadrature`. This is probably unnecessary
  now that `frobSq_eq_sum_eigenvalues_sq` is gone, but it was not tested, because dropping it could
  break transitive users.
- Reference edit in a foreign file: `Matrix/Basic/QuadForm.lean` docstring (stale module path).

## Compiled

`lake build` succeeded with no new `sorry` (only the existing catalogued scaffolds warn) for:
- `NLAlib.Matrix.Functions.CFCQuadratic`, `NLAlib.Matrix.Basic.QuadForm`.
- The whole `NLAlib.Krylov` aggregator, `NLAlib.Polynomial` and `NLAlib.Solvers`.
- `NLAlib.Estimation.Trace` (aggregator), Trace/{HutchinsonTail, Unbiased}, Quadrature/{SLQ,
  SLQAnalytic, SLQLipschitz} and Spectral/RandomStartLanczos.
- LowRank/PolynomialMethods/{PolynomialFilter, ComplexPolynomialFilter} and
  LowRank/RangeFinding/SubspaceConvergence.

Every moved declaration went upstream of its source, so no importer lost access to a name.
`check_layers.py` reports only the existing RademacherMgfCgf → HutchinsonLaws violation.
