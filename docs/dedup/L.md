# Dedup round, agent L (leftovers)

Rename table: `docs/renames/2026-10-12-dedup-L.json` (19 entries). Remaining follow-ups from all
reports are collected in `docs/DEDUP_FOLLOWUP.md` ("Remaining follow-ups …", appended sections).

## Executed

| # | Task | Keeper / result | Dropped / renamed | Files |
|---|---|---|---|---|
| 1 | `lieb_concavity` to any finite index type | `lieb_concavity {n} [Fintype n] [DecidableEq n]` (OperatorTheory/LiebConcavity), **no `Nonempty` hypothesis** (empty type: constant function); the `Fin d` proof is the private `lieb_concavity_fin`, transported by `reindexStarAlgEquiv`. Tags now `operator-monotone-convex, matrix-freedman (partial)` (the latter moved from the dropped declaration) | `lieb_concavity_finite` | LiebConcavity (imports UnitaryCalculus), LiebTraceFunction (decl deleted, docstring, redundant UnitaryCalculus import dropped), Martingales/{ConditionalLieb, ConditionalLiebPredictable} (reference) |
| 2 | JensenIsometricCompression private copies | rewritten against public API: new public `cfc_reindex_of_isHermitian` (the ℂ-algebra `reindexStarAlgEquiv` suffices for the real `cfc` via `StarAlgHomClass.map_cfc`, so **no real `≃⋆ₐ[ℝ]` version was needed**), `isHermitian_reflection_conj`, `spectrum_reflection_conj`, `cfc_reflection_conj` (Functions/UnitaryCalculus), `spectrum_reindex` (Functions/HermitianCalculus; `lambdaMax_reindex` now uses it) | private `reindexStar`, `reindex_cfc`, `unitary_calculus` | JensenIsometricCompression (imports UnitaryCalculus), UnitaryCalculus, HermitianCalculus |
| 3 | ε-net lemmas to Matrix/Norms | new **`Matrix/Norms/Net.lean`**: every deterministic declaration of the old Net file (`abs_dotProduct_mulVec_le`, `specNorm_le_of_forall_sqrt_le`, `exists_unit_abs_quadForm_eq_specNorm`, `specNorm_le_div_of_net`, `…_bilinear`, `…_quadForm`, `exists_finset_sphere_net`, `exists_finset_net_specNorm_le`, private helpers), names and `epsilon-net-norm` tags unchanged; `Probability/Concentration/Basic/Net` keeps only `measure_lt_specNorm_le_of_hasSubgaussianMGF` and imports it. `abs_diag_le_specNorm` → Norms/SpectralNormBounds, `sum_diag_sq_le_frobSq` and `sum_diag_sq_le_frobNorm_sq` → Norms/Core, all three **generalised `Fin n` → any `Fintype`** | — (moves) | Net (both), SpectralNormBounds, Core, QuadraticForms/{CutAverages (cut), Geometry (import SpectralNormBounds)} |
| 4 | `quadForm_eq_sum_mul_mul` | moved to Matrix/Basic/QuadForm (Fintype, module docstring updated) | — (move) | QuadForm, QuadraticForms/Geometry (cut) |
| 4b | `matrixQuadraticFormReal` | **skipped**: it is the complex Hermitian form `(star u ⬝ᵥ A *ᵥ u).re` on `Matrix n n ℂ`, while `quadForm` is ℝ-only; replaceable only after the RCLike round (listed in DEDUP_FOLLOWUP) | — | — |
| 5 | FourthMoment with `linForm` (randnla#19 second half) | `integrable_linForm_mul_{two,four}_gaussianMatrix`, `integral_linForm_mul_{two,four}_gaussianMatrix` stated with `linForm u G` and curried coefficients (`∑ᵢⱼ uᵢⱼ vᵢⱼ`); the uncurried proofs are private steps. `integral_linForm_sq_gaussianMatrix` (LinearForms, now imports FourthMoment) is the 2-line `u = v` corollary | the four `…_linear_mul_…` names | RandomMatrix/Gaussian/{Moments/FourthMoment, Moments/ApproxMultiplication (private bridges `L_eq_linForm`, `ip_eq_sum_sum`), Basic/LinearForms} |
| 6 | `spectralNorm` in names | `specNorm_le_norm_map_ofReal`, `measure_le_norm_leverage_gram_sub_one` (no other `spectralNorm` left in `NLAlib/`) | `specNorm_le_spectralNorm_map_ofReal`, `measure_le_spectralNorm_leverage_gram_sub_one` | Norms/RealComplexNorm, Spectral/{MatrixPowerReal, MatrixPowerBounded}, Sketching/Structured/{SRHT, SRHTWithReplacement}, Sketching/Sampling/LeverageSampling (reference) |
| 7 | `fromBlocks_zero_posSemidef` | `posSemidef_fromBlocks_diag` (HermitianCalculus, StarOrderedRing) | `fromBlocks_zero_posSemidef` | Inequalities/BlockOrderConsequences (imports HermitianCalculus, whose NLAlib closure is 3 small files) |
| 8 | krylov#20 | `IsUpperHessenberg.sub_smul_one`, `.add_smul_one` moved verbatim to Matrix/Structured/Hessenberg; QRAlgorithm module docstring now names Structured/Hessenberg for the shape predicates and Givens only for the QR lemmas | — (move) | Hessenberg, QRAlgorithm |
| 9 | raw singular-value spelling | 220 rewrites of `(Matrix.toEuclideanLin A).singularValues` / `A.toEuclideanLin.singularValues(_nonneg/_antitone)` to `singularValues A` (NLAlib `singularValues_nonneg/_antitone`) in 48 files, plus the remaining `LinearMap.singularValues_nonneg/_antitone _` uses. Now-redundant `← singularValues_eq_linearMap` rewrites removed; bridges added where a proof unfolds a raw definition or applies a Mathlib `LinearMap` lemma under `rw` | see below | 48 Matrix files (Spectral, Norms, Inequalities, Factorizations, Subspaces, Perturbation, Structured, Functions) |
| 9b | the 11 `toEuclideanLin_singularValues_*` theorems | Fin twins collapsed: `weaklyMajorized_abs_singularValues_add_sub` and `sum_abs_singularValues_add_sub_le_sum_range` are now the Fintype statements (Fin proofs private `_fin`; NearestPolar adapted with `rw [Fintype.card_fin]`); `sum_range_singularValues_mul_rpow_le` (HornPowerSums) **generalised Fin → Fintype with its body unchanged** and the Fintype copy deleted. Renamed: `singularValues_map_ofReal`, `singularValues_eq_eigenvalues₀_of_posSemidef`, `weaklyMajorized_abs_singularValues_add_sub_padded`, `weaklyMajorized_singularValues_add`, `sum_range_singularValues_rpow_eq_of_min_le`, `singularValues_cfc_abs`, `multiset_singularValues_eq_sqrt_eigenvalues`, `multiset_singularValues_kronecker` | 11 old names (rename table) | the 9 defining files + toolkits (Lidskii, KyFan, HornProduct, Kronecker), users |
| 10 | InversePerturbation's `Spectral.Weyl` import | dropped; the full reverse closure (17 modules) builds | — | InversePerturbation |
| 11 | docs | TroppMatrixConcentration (`matrixFunction_*` → `cfc_*`, moved modules, `CFC.log_monotoneOn`, HermitianCalculus split), KRYLOV_DEFINITIONS and ROUND8_KRYLOV_BRIEF (`Subspaces/OrthonormalBasisMatrix`), REORG_FOLLOWUP (15 items annotated "Done 2026-10-12": deleted files, KyFan chain, gaussianMatrix move, Net, shims), MATRIX_TOOLKIT_COMPLETION (stale `toEuclideanLin_` name), STANDARDS §2 (`--gen-aggregators`, `ImportUsage.lean` + `apply_imports.py`) and §3 (both pseudoinverses and when to use which, `singularValues` over `[RCLike 𝕜] [Fintype]` with its bridge, `linForm`, `cfc`, `‖A‖` instead of a named spectral norm; the Loewner order line was already there). CONTRIBUTING/AGENTS list no vocabulary | — | docs |
| 12 | follow-ups | `docs/DEDUP_FOLLOWUP.md`: RCLike round items, ℝ/ℂ twin inventory, Kaczmarz/sketch-and-project bridge, `rectangularDiagonal` chain, toolkit atlas-tag policy question, statement shapes (ChiSquare `_fin`, `sinThetaMax`, …), `matrixLog` retirement procedure, files/imports/docs, sparse leftovers | — | docs |

### Raw spellings left (5 occurrences in 3 files)

- `Spectral/SVD.lean` (2): the definition of `singularValues` and the `rfl` bridge `singularValues_eq_linearMap`.
- `Norms/KyFanNorm.lean` (1): the definition of `kyFanNorm`; the file deliberately imports only
  Mathlib (F2b), below Spectral/SVD. Switching it is a follow-up (no cycle).
- `Spectral/ComplexSingularTransport.lean` (1 line, 2 occurrences): a proof step in
  `rank_eq_of_complex_real_singularValues_eq` that needs the `Finsupp` (`ℕ →₀ ℝ`) structure of
  Mathlib's `LinearMap.singularValues` (support cardinality = rank).
- Proof-internal `a.singularValues` with `a := toEuclideanLin A` in ComplexRectangularSVD and
  ComplexSquareSingularBasis (abstract linear map, not the matrix spelling).
`Spectral/ComplexSquareSingularBasis` now imports `Spectral/SVD` to state its result with
`singularValues`. No theorem name contains `toEuclideanLin_singularValues` any more.

## Generalisations

- `lieb_concavity`: `Fin d` + `[NeZero d]` → any `[Fintype n] [DecidableEq n]` (empty included).
- `abs_diag_le_specNorm`, `sum_diag_sq_le_frobSq`, `sum_diag_sq_le_frobNorm_sq`: `Fin n` → `Fintype`.
- `sum_range_singularValues_mul_rpow_le`, `weaklyMajorized_abs_singularValues_add_sub`,
  `sum_abs_singularValues_add_sub_le_sum_range`: `Fin` → `Fintype` (names kept).

## Files created / deleted

- Created: `NLAlib/Matrix/Norms/Net.lean`. Aggregators regenerated with
  `python3 scripts/reorg.py --gen-aggregators` (96 aggregators; this also picked up the sparse
  agent's new `Matrix/Norms/EntryBounds`).
- Deleted: none.

## For the coordinator

- Atlas: re-run ExtractDecls/sync_atlas. Tag moved: `matrix-freedman (partial)` from
  `lieb_concavity_finite` onto `lieb_concavity`. Module changes for the `epsilon-net-norm`
  declarations (now `NLAlib.Matrix.Norms.Net`), `gaussian-frob-fourth-moment`
  (`integral_linForm_mul_four_gaussianMatrix`, renamed), `lidskii (partial)`
  (`weaklyMajorized_abs_singularValues_add_sub`, now the Fintype statement),
  `horn-product-inequality (partial)` (`sum_range_singularValues_mul_rpow_le`, now Fintype),
  `leverage-sampling-ose (partial)` (`measure_le_norm_leverage_gram_sub_one`, renamed).
- `abs_diag_le_specNorm` duplicates the diagonal case of S2's new `abs_apply_le_specNorm`
  (Norms/EntryBounds); left in place because S2's file is in flux (DEDUP_FOLLOWUP).
- Foreign files touched (reference/import edits or the assigned cuts): Probability
  QuadraticForms/{CutAverages, Geometry}, Martingales/{ConditionalLieb, ConditionalLiebPredictable},
  Sketching/{Structured/SRHT, Structured/SRHTWithReplacement, Sampling/LeverageSampling}.

## Compilation

`lake build` green for: every touched module and its direct dependants after each task (Lieb: 5
dependants; calculus: 9; Norms moves: 31 direct dependants; Gaussian moments: 4; items 6–7: 12;
InversePerturbation: its 17-module reverse closure); the singular-value pass: the 48 edited modules
and their full reverse closure (290 modules, Sketching/Sparse excluded); finally
`lake build NLAlib.ForMathlib NLAlib.Matrix NLAlib.Polynomial NLAlib.Krylov NLAlib.Probability
NLAlib.RandomMatrix NLAlib.Estimation NLAlib.LowRank NLAlib.Solvers NLAlib.Sketching.{Sampling,
Structured, Gaussian, Properties}` (4929 jobs) green. Sketching/Sparse was not built (S2 is
building it concurrently; no Sparse file references a changed name or `singularValues`). No new
`sorry`. `check_layers.py` OK, `check_names.py` OK.

## Summary

All twelve tasks done except the `matrixQuadraticFormReal` replacement (complex form; needs the
RCLike `quadForm`). `lieb_concavity` and five singular-value/diagonal lemmas generalised to
`Fintype`; the JensenIsometricCompression private copies replaced by public lemmas over the
existing ℂ `reindexStarAlgEquiv`; the deterministic ε-net lemmas now in `Matrix/Norms/Net`; the
raw singular-value spelling reduced from 179 to 5 occurrences (definitions and one `Finsupp`
proof step), the 11 `toEuclideanLin_singularValues_*` names gone; 19 renames recorded.
