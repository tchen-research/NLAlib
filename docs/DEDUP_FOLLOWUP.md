# Dedup round follow-ups (2026-10-12)

## Decided: real and complex handled like Mathlib

Owner's decision (2026-10-12): the Matrix-layer vocabulary is stated once over `[RCLike 𝕜]` with
`conjTranspose`, as Mathlib does for `PosSemidef`, `IsHermitian`, the L2 operator norm and
`LinearMap.singularValues`. `HasOrthonormalCols Q` becomes `Qᴴ * Q = 1` (over ℝ, `Aᴴ = Aᵀ` by
simp); `specNorm`, `frobInner`, `frobSq`, `frobNorm`, `quadForm`, `residual`, `moorePenroseInverse`
follow. Real theorems keep their statements; the probability and randomized layers stay real.
This is its own round after the dedup round: (1) generalise the vocabulary and its API files,
(2) sweep the files that spell `Qᵀ * Q = 1` or unfold the real definitions, (3) merge the ℝ/ℂ twin
families the dedup reviews left as follow-ups (Courant–Fischer / ComplexVariationalPrinciple,
Eckart–Young / ComplexEckartYoung, CS and oblique projections, RPCholesky, volume sampling,
complex subspace iteration, sampled matrices; see docs/dedup/*.md "follow-ups").

## Remaining follow-ups from the dedup reports (collected by agent L, 2026-10-12)

One line each, with the report that raised it (`docs/dedup/<agent>.md`). Items executed by agent L
are in `docs/dedup/L.md` and not repeated here.

### RCLike round (after the vocabulary is RCLike)

- `matrixQuadraticFormReal A u = (star u ⬝ᵥ A *ᵥ u).re` (Probability/Concentration/Martingales/LocalSecondMoment) is the complex Hermitian form; once `quadForm` is `star z ⬝ᵥ (A *ᵥ z)` over `[RCLike 𝕜]`, replace it by `RCLike.re (quadForm A u)` (bridge `rfl`) and delete it; `matrixVectorSqNorm` likewise becomes `‖A *ᵥ u‖²` in the Euclidean norm. (P_prob, L)
- Merge `complex_singularValues_isometry_mul` and `complex_singularValues_mul_unitary` (Spectral/ComplexSingularTransport) into `singularValues_isometry_mul` / `singularValues_mul_orthogonal` once `HasOrthonormalCols` is `Qᴴ * Q = 1`; `complex_singularValues_zero_eq_norm` into `singularValues_zero_eq_specNorm` once `specNorm` is RCLike. (F1, P_spectral)
- The three singular-basis existence statements `exists_orthogonal_transpose_mul_mul_eq_diagonal_singularValues`, `exists_unitary_conjTranspose_mul_mul_eq_diagonal_singularValues`, `exists_complex_rectangular_svd` are a real/complex family: one RCLike statement. (P_spectral)
- Complex matrix statements in Probability use `‖A‖` (L2 operator norm) because `specNorm` is ℝ-only; once `specNorm` is RCLike decide whether they switch to `specNorm` (bridge `specNorm_eq_norm`). (P_prob)
- RCLike Courant–Fischer (matrix_spectral#35, ~650 lines): then the two TraceTail wrappers `sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq` (ℝ) and `complex_sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq` (ℂ) collapse to the RCLike core. (P_spectral, P_norms)
- `map_ofReal_matrix_pow` stays: the reviewer's `Matrix.map_pow A Complex.ofRealHom` does not match `Complex.ofReal` under `rw`/`simp` (checked). No action unless the bridge disappears with the RCLike sweep. (P_spectral #40)

### ℝ/ℂ twin families (inventory for the RCLike round, step 3)

- Courant–Fischer / ComplexVariationalPrinciple; Eckart–Young / ComplexEckartYoung / ComplexGramTruncation / ComplexBestRankApproximation. (P_spectral, REORG M1)
- CS decomposition and oblique projections: CS* / ComplexCS*, Oblique* / ComplexOblique*, CSToolkit / ComplexCSToolkit. (F1, P_spectral)
- RPCholesky (randnla#5): `complexCholeskyResidualStep` is `choleskyStep (K := ℂ)` by `rfl`; plan in P_randnla (bridges under `map ofReal`, real theorems as corollaries, delete ~45 real CholeskyHistories copies). (P_randnla)
- Volume sampling (randnla#6): relate `bestRankFrobSq`/`singularValueTailSq` to `complexBestRankFrobSq`/`complexGramTail` first, then delete the real file and move its tags. (P_randnla)
- Complex subspace iteration (randnla#24): generalise `subspaceIterate` to `[CommSemiring R]` and `subspaceTangent` to `[RCLike 𝕜]`, delete `complexSubspaceIterate`/`complexSubspaceTangent`, merge SubspaceConvergence/ComplexSubspaceConvergence and PolynomialFilter/ComplexPolynomialFilter. (P_randnla)
- TraceTail/ComplexTraceTail, DiagonalFilter/ComplexDiagonalFilter, GramColumnDeterminant/ComplexGramColumnDeterminant, the complex column projectors next to Projections. (REORG M1, P_norms)

### Kaczmarz / sketch-and-project bridge

- Randomized Kaczmarz is sketch-and-project with `S = e_i`, `p_i = ‖A_i‖²/‖A‖_F²` (Gower–Richtárik), but nothing links `Kaczmarz.step`/`expErr` to `SketchProject.step`/`expErr`. Plan: new `Solvers/Kaczmarz/SketchProjectBridge.lean` with `Kaczmarz.step A b x i = SketchProject.step A b (replicateCol Unit (Pi.single i 1)) x` (needs the pseudoinverse of a `1 × n` row, `0` for the zero row), the `expErr` identity with `Kaczmarz.prob A`, and `expectedProjector = AᵀA / frobSq A`; optionally reprove `Kaczmarz.expErr_le(_of_sub_mem_range)` from the SketchProject versions. Keep the Kaczmarz definitions (atlas `kaczmarz-def`). Low priority. (review krylov, not executed by P_krylov)
- `frobConditionNumber` (KaczmarzProbability) next to `conditionNumber`, with `conditionNumber A ≤ frobConditionNumber A`; not done because KaczmarzProbability would import ConditionNumber's heavy chain. Optional. (P_krylov, krylov#30)

### `rectangularDiagonal` chain

- `rectangularDiagonal` (Fin thin-vector embedding via `rectDiag`) and `rectangularDiagonalMatrix` (its Fintype transport via `reindex`) coexist with `rectDiag`. Merging needs `Fintype.equivFin (Fin m)` to act as the identity, which is not definitional; plan: state the bridge `rectangularDiagonalMatrix (m := Fin m) (n := Fin n) x = rectangularDiagonal (x ∘ Fin.cast _)` by `ext` + `Fintype.equivFin` computation, then keep one of the two. Low priority. (P_norms, matrix_norms#31)

### Atlas-tag policy for toolkit bundles (question for the owner)

- The `*Toolkit.lean` files (LidskiiToolkit, KyFanToolkit, HornProductToolkit, KroneckerToolkit, CholeskyToolkit, CSToolkit, …) state a conjunction of `@NLAlib.x` components and several carry the full atlas tag, while the components carry `(partial)` tags. After the dedup round most components are the canonical keepers. Decide: (a) bundles keep the full tag (status = all parts proved) and components stay `(partial)`; or (b) the full tag moves to the main theorem and bundles become untagged documentation or are deleted. Related: `eigenvalues₀_add_le_add_eigenvalues₀_zero` was kept only "for its tag and the toolkit". (P_pert, F1, P_norms)

### Statement shapes

- ChiSquare: `integrable_and_integral_inv_sum_sq_gaussianReal` (any `Fintype ι`) and `integrable_and_integral_inv_sum_sq_gaussianReal_fin` (`Fin d`, `3 ≤ d`) coexist; STANDARDS §3 allows `Fin` where a Gaussian law is involved, so the coordinator decides whether the `_fin` form (used by the `Fin` product-measure callers) stays as a named corollary or is inlined. (P_prob)
- `sinThetaMax Q X := specNorm (residual Q X)` and `tanThetaMax`: keep as named vocabulary or retire `sinThetaMax` for `specNorm (residual Q X)` (nothing outside PrincipalAngles uses it). Vocabulary call for the owner. (P_basic)
- Mirsky: the `Fin` steps `weaklyMajorized_abs_singularValues_add_sub_fin` and `sum_abs_singularValues_add_sub_le_sum_range_fin` are private; `Factorizations/NearestPolar` uses the Fintype keeper with `rw [Fintype.card_fin, Fintype.card_fin] at hWeak`. Generalising NearestPolar to Fintype indices removes the rewrite. (L)
- `abs_diag_le_specNorm` (Norms/SpectralNormBounds, moved from the Hanson–Wright chain) is the diagonal case of `abs_apply_le_specNorm` (Norms/EntryBounds, created by the sparse agent S2 during this round). Once S2's file is final: delete `abs_diag_le_specNorm`, use `abs_apply_le_specNorm A i i` in QuadraticForms/{Centering, DiagonalCGF}. (L)
- `nuclearNorm_eq_trace_sqrt_gram` for rectangular matrices (matrix_pert#50): `nuclearNorm_eq_of_gram_eq` needs equal shapes; needs a different proof. (F2b)
- `rank_eq_card_nonzero_of_orthogonal_diagonalization` (Structured/KroneckerNormRank) duplicates `rank_eq_card_nonzero_of_diagonal_congruence` (Spectral/SemidefiniteCongruence); needs the latter moved into Matrix/Basic or Structured importing Spectral. (P_spectral #27)
- Schur triangularisation re-derivations in `ForMathlib/Analysis/*` (matrix_spectral #30, #31): reprove from one induction. (P_spectral)
- `mul_transpose_eq_mul_moorePenroseInverse_of_qr_of_rank_eq_card` (QRConsequences) is a special case of `mul_transpose_eq_mul_moorePenroseInverse` (Basic/MoorePenroseProjector); reprove as a corollary. (P_randnla, randnla#21)
- Optional: `leverageSamplingSketch = sampledRowMatrix 1`. (P_randnla, randnla#8)
- Restate `lanczosRitzValue`, `rayleighQuotient_toEuclideanCLM_bounds`, `sub_rayleighQuotient_pow_div_specNorm_le_log_overlap_div`, `powerRayleighRelativeError` with `rayleighQuotient A x` (krylov#10 step 2). (F2a)
- Optional rename `rank_isometry_mul_eq` → `HasOrthonormalCols.rank_mul_eq`. (F2a)
- Optional: restate the `ArnoldiDecomp`/`LanczosDecomp` shape facts through `IsUpperHessenberg`/`IsTridiagonal` (matrix_pert#48). (F2c)
- Private deterministic duplicates in Concentration/Matrix: IntrinsicChernoff's private `lambdaMin_nonneg` (Fin) = `lambdaMin_nonneg_of_posSemidef`; IntrinsicBernsteinExpectation's `norm_le_trace` = `lambdaMax_le_trace_of_posSemidef`; IntrinsicHermitianBernstein's `lambdaMax_zero`; the four `norm_exp_le` copies (signatures differ). (P_prob)
- Optional: derive `rademacher_pi_coordinate_moments` from `memLp_two_and_moments_of_isRademacher`. (P_prob)
- Optional rename `ExactRowSubset` → `FinsetOfCard` (9 files in Probability/Sketching). (P_formathlib)

### `matrixLog` retirement procedure

- Bridge `matrixLog_eq_log : matrixLog A = CFC.log A := rfl` exists (Functions/ExpLog). Procedure: file by file (≈118 occurrences in 30 files, 20 in Probability), replace `\bmatrixLog\b` by `CFC.log`, add `open scoped Matrix.Norms.L2Operator` where missing (`CFC.log` needs the `NormedRing`/`NormedAlgebra ℝ` instance on `Matrix d d ℂ`, which exists only under that scope; files with a different scoped norm must be checked for instance mismatches), build each file and its dependants, then delete the definition and record it in a rename table; move the atlas tag `matrix-calculus-def` if it is on the def. (P_pert #43 step 2)

### Files, imports, docs

- Norms/Core is ~690 lines: move its "spectral-norm helpers" section to Norms/SpectralNormBounds (needs import edits in dependants). (F2b)
- Prune imports with `scripts/ImportUsage.lean` + `apply_imports.py`: the explicit KyFan imports F1 added to OstrowskiCongruence, InvariantNorm, SchattenNorms, ObliqueCanonicalSpectrum, StrongRankRevealingQR (now `KyFanNorms`) are probably redundant; `Estimation/Trace/HutchinsonTail` probably no longer needs `Krylov.Quadrature.GaussQuadrature`. (F1, P_krylov)
- `Norms/KyFanNorm` defines `kyFanNorm` with the raw `(toEuclideanLin A).singularValues` because it imports only Mathlib (F2b's choice, to stay below Spectral/SVD). Importing `Spectral/SVD` there (no cycle) would let `kyFanNorm` use `singularValues` and remove the `simp only [← singularValues_eq_linearMap]` steps after `unfold kyFanNorm` (KyFanNorms, Schatten, NuclearPSD, NuclearHermitian, SchattenComparison). (L)
- The Hanson–Wright chain's `Source-transport helper …` docstrings (~90 lemmas) do not say what each lemma states. (P_prob)
- `ForMathlib/Algebra/InterlacingWeights.lean` imports `Mathlib.Tactic`. (P_formathlib)
- Near-Mathlib wrappers documented as upstreaming candidates in their module docstrings (GramSchmidt, FourierCircle, FourierConvolution, InterlacingInterpolation, NonnegativeSupermartingale, BoundedDifferences, Matrix/Order). (P_formathlib)
- `scripts/AuditNewProofs.lean`: the files created this round are not in its module list (several agents). (P_randnla)
- Atlas: re-run `ExtractDecls` and `sync_atlas.py` (all reports); tags moved this round are listed in each report's coordinator section.

### Sparse integration leftovers (for the sparse agents; see docs/SPARSE_INTEGRATION.md)

- FiniteLaw/FiniteL2 unused or simp-only declarations not yet decided (formathlib#11–18, #23–25, minus those S1 deleted). (P_formathlib, S1)
- `sum_ordered_swap`, `sum_offDiagonal_swap`, `sum_erase_comm`, `abs_entry_le_l2_opNorm`, `normSq_sum_le_card`: one-liners needing a home upstream of both users (phase 3e); `DependsOn` → Mathlib `DependsOn`; D9 final step (`FiniteHilbert.normSq x` → `x ⬝ᵥ x`, ~300 occurrences; `ParsevalFrame.normSq` → `‖x‖²`, ~140); later waves 2d, 2f, 2g, 2j, 2k, 2l. (S1)
