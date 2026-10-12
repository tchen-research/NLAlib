# Dedup round, agent F2a (basic vocabulary: QuadForm, frames, Moore–Penrose, dilation, Schur pivot)

Theme: Matrix/Basic and Matrix/Subspaces are the single home of the foundational vocabulary's API.
Rename table: `docs/renames/2026-10-12-dedup-F2a.json` (19 entries). No atlas tag moved: none of the
dropped declarations carried an `atlas:` or `SCAFFOLD:` line (keepers keep theirs).

## Findings executed

| id | keeper / new home | dropped or moved | files touched |
|---|---|---|---|
| matrix_basic#0, #1, matrix_pert#23 | `pivotSchur`, `posSemidef_pivotSchur` (Basic/SchurComplement) | deleted `choleskyTrailingResidual`, `posSemidef_choleskyTrailingResidual` and the file `Factorizations/CholeskyTrailingResidual.lean` | CholeskySemidefinite (imports SchurComplement now), CholeskyCharacterization (`hCorrection` restated in `pivotSchur_apply` form), CholeskyToolkit, scripts/AuditNewProofs.lean (module list) |
| matrix_basic#8, matrix_pert#28 | `apply_eq_zero_of_posSemidef_of_apply_self_eq_zero` (+ primed row version), moved to Basic/GramVanishing and **generalised to `[RCLike 𝕜]`** | deleted `apply_eq_zero_of_posSemidef_of_diag_eq_zero` (GramVanishing), `apply_eq_zero_of_complex_posSemidef_of_diag_eq_zero` (ComplexCholeskyPivot) | SchurComplement (section removed, imports GramVanishing), ComplexCholeskyPivot (imports GramVanishing), CholeskySemidefinite, Spectral/SemidefiniteCongruence, LowRank/Cholesky/CholeskyPivot |
| matrix_basic#28, matrix_pert#29 | `eq_zero_of_matrix_rank_eq_zero` **generalised to any `[Field K]`** | deleted `eq_zero_of_complex_matrix_rank_eq_zero` | ComplexCholeskyPivot, LowRank/Cholesky/ComplexCholeskyHistories |
| matrix_basic#5 | `dilation` **generalised to `{α} [Zero α] [Star α]`** (body unchanged); new generic API in Basic/Dilation: `isHermitian_dilation`, `dilation_add` (`[AddMonoid α] [StarAddMonoid α]`) | deleted `realDilation`, `isHermitian_realDilation`, `realDilation_add`; renamed `exists_realDilation_orthogonal_diagonalization`, `eigenvalues₀_realDilation{,_top,_bottom}` → `…dilation…` (no clashes); def `realDilationSpectrum` keeps its name | Spectral/RealDilation (imports Basic/Dilation; proofs add `conjTranspose_eq_transpose_of_trivial`), Spectral/RealDilationSpectrum, Inequalities/Mirsky (mechanical renames; its private `eigenvaluePrefix_realDilation` left as is) |
| matrix_basic#6 | Basic/Dilation imports `Mathlib.Data.Matrix.Block` + `Mathlib.LinearAlgebra.Matrix.Hermitian` instead of `Matrix.Functions.ExpLog` | — | no downstream needed an added ExpLog import (whole dependant closure rebuilt) |
| matrix_basic#16 | `frobSq_frame_eq_card` moved ProjectionGaps → Subspaces/Projections | deleted square-only `frobSq_eq_card_of_hasOrthonormalCols` (ScaledOrthogonal) | ProjectionGaps, ScaledOrthogonal |
| matrix_basic#19 | `card_le_card_of_hasOrthonormalCols` (keeps `atlas: orthonormal-completion`) moved CourantFischer → Subspaces/Projections | deleted `card_le_of_transpose_mul_self_eq_one` | Projections (own use), CourantFischer, RandomMatrix/Gaussian/Invariance/Invariance (`card_le_card_of_hasOrthonormalCols (Q := V) hV`) |
| matrix_basic#29 | `HasOrthonormalCols.toLinearIsometry` moved GramIsometry → Subspaces/OrthogonalProducts, `norm_map'` reproved via `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` | deleted `orthogonalToEuclideanIsometry` (CanonicalQR now uses `HasOrthonormalCols.toLinearIsometry (transpose_mul_self_orthogonalGroup O)`; the `rfl` in `qrColumnFamily_orthogonal_mul` still closes) | GramIsometry, CanonicalQR (imports OrthogonalProducts) |
| matrix_basic#36 | Subspaces/OrthogonalProducts now hosts `HasOrthonormalCols.submatrix_cols` (from Inequalities/KyFan), `HasOrthonormalCols.reindex` (from Spectral/FiniteIndexTransport), `rank_isometry_mul_eq` (from Factorizations/MaximumVolumeRankAdapted; not renamed) | moves only | KyFan, FiniteIndexTransport, MaximumVolumeRankAdapted import OrthogonalProducts; **GramIsometry no longer imports Inequalities/KyFan** (now OrthogonalProducts + Basic/MoorePenrose); MaximumVolumeRankAdapted needed an explicit `import NLAlib.Matrix.Norms.RankNorm` and Spectral/SimultaneousOrthogonal an explicit `import NLAlib.Matrix.Functions.PolynomialCalculus` (both previously transitive through KyFan) |
| matrix_basic#31–#35, krylov#9 | Basic/QuadForm now hosts `quadForm_sq_eq_sum` (from QuadraticMoments), `quadForm_reindex` (from HansonWright), `quadForm_smul_add_smul` (from Wielandt), `quadForm_vecMulVec_self` (from SeparatingPSDVector), `quadForm_transpose_mul_mul` (from Krylov/Solvers/Preconditioned, **generalised to rectangular `W : Matrix n k ℝ`**), `quadForm_transpose_mul_self` (from Preconditioned) | deleted `quadForm_mul_mul_transpose` (OstrowskiCongruence); its four `rw` sites now read `rw [show S * A * Sᵀ = Sᵀᵀ * A * Sᵀ by rw [Matrix.transpose_transpose], quadForm_transpose_mul_mul]` | QuadForm imports `Mathlib.Data.Real.Star` (was `Real.Basic`) and `Mathlib.LinearAlgebra.Matrix.Hermitian` |
| krylov#10 (step 1 only) | `rayleighQuotient` moved Krylov/Spectral/PowerMethod → Basic/QuadForm; bridge `rayleighQuotient_toEuclideanCLM_eq` (Spectral/PowerRayleigh) restated with RHS `rayleighQuotient A b` | — | uses append `rayleighQuotient, quadForm` to the rewrite: PowerRayleigh, Krylov/Spectral/MeasurableRitz, Estimation/Spectral/RandomStart{Lanczos,Power,Endpoints} |
| krylov#26 | OrthogonalProducts (section Columns) hosts `transpose_mul_self_apply`, `mulVec_eq_sum_smul_col`, `HasOrthonormalCols.col_dotProduct_col`, `HasOrthonormalCols.linearIndependent_col` (from Krylov/Processes/Arnoldi), `inner_eq_dotProduct_ofLp` (from ArnoldiProcess) | deleted private `inner_eq_ofLp_dotProduct` in RandomMatrix/Gaussian/InverseMoments/SchurComplement (uses renamed, import added). `transpose_mul_mul_apply` was meanwhile replaced by F2c's `transpose_mul_mul_apply_eq_dotProduct` (ForMathlib), so it is not duplicated here | Arnoldi (imports OrthogonalProducts; empty "Matrix helpers" header removed), ArnoldiProcess |
| krylov#27 | Basic/MoorePenrose, new section `RowProjector`: `dotProduct_self_sub_moorePenroseInverse_mul_mulVec`, `dotProduct_moorePenroseInverse_mul_mulVec_le_dotProduct_self`, `inv_specNorm_moorePenroseInverse_sq_mul_dotProduct_le`, and (kept, moved) `inv_specNorm_pinvL_sq_mul_dotProduct_le` | renamed out of `SketchProject`/`Kaczmarz` namespaces (see rename table) | Solvers/SketchAndProject/Core, Solvers/Kaczmarz/KaczmarzExtensions, Solvers/Kaczmarz/KaczmarzProbability |

## Findings skipped / partial

* krylov#10 step 2 (restating `lanczosRitzValue`, `rayleighQuotient_toEuclideanCLM_bounds`,
  `sub_rayleighQuotient_pow_div_specNorm_le_log_overlap_div`, `powerRayleighRelativeError` in terms of
  `rayleighQuotient A x`) not done, per the task (step 1 only).
* Not in my findings but found: `rayleighQuotient_toEuclideanCLM_eq_quadForm_div`
  (Matrix/Perturbation/EigenvalueResidualToolkit.lean:21, unused) is now a literal duplicate of
  `rayleighQuotient_toEuclideanCLM_eq` (RHS `quadForm A x / (x ⬝ᵥ x)` is `rayleighQuotient A x` by `rfl`).
  Follow-up: delete it.
* `rank_isometry_mul_eq` not renamed to `HasOrthonormalCols.rank_mul_eq` (optional in the finding).

## Generalisations

`dilation` (ℂ → any `[Zero α] [Star α]`), `apply_eq_zero_of_posSemidef_of_apply_self_eq_zero{,'}`
(ℝ → `[RCLike 𝕜]`), `eq_zero_of_matrix_rank_eq_zero` (ℝ → `[Field K]`), `quadForm_transpose_mul_mul`
(square → rectangular `W`).

## Files created / deleted

* Deleted: `NLAlib/Matrix/Factorizations/CholeskyTrailingResidual.lean`. Its only importers were
  CholeskySemidefinite (fixed) and the generated aggregator `NLAlib/Matrix/Factorizations.lean`
  (line `import NLAlib.Matrix.Factorizations.CholeskyTrailingResidual`): **coordinator must regenerate
  aggregators** (`scripts/reorg.py` has no `--gen-aggregators` flag; `gen_aggregators()` exists).
* Created: none.

## Notes for the coordinator

* Sizes: Subspaces/Projections.lean is 542 lines and Basic/MoorePenrose.lean 543 (both were near 500
  before); candidates for a split (e.g. Projections' orthogonal-completion section, MoorePenrose's
  `RowProjector` section).
* Compiled with `lake build` (per module): GramVanishing, SchurComplement, ComplexCholeskyPivot,
  Cholesky{Semidefinite,Definite,Characterization,Toolkit}, Factorizations/Cholesky, HadamardDeterminant,
  QRExistence, SemidefiniteCongruence, LowRank/Cholesky/{CholeskyPivot,ComplexCholeskyHistories,
  CholeskyHistories,PartialCholesky}, Dilation, RealDilation(Spectrum), Concentration/Basic/{MatrixCalculus,
  IntrinsicDimension}, Concentration/Matrix/{DilationIdentities,DilationVariance,MatrixSeries,MatrixBernstein,
  UnitaryCalculus,IntrinsicBernstein}, Jensen{IsometricCompression,ReflectionAlgebra}, LightSectorAbstract,
  QuadForm, HansonWright, QuadraticMoments, Wielandt, SeparatingPSDVector, FiniteExponentialGram,
  OstrowskiCongruence, Preconditioned, PowerMethod, PowerRayleigh, MeasurableRitz, RandomStart{Lanczos,Power,
  Endpoints}, Projections, OrthogonalProducts, ProjectionGaps, GramIsometry and its nine importers,
  CanonicalQR, CourantFischer, KyFan, KyFanToolkit, CompressionDeterminant, SchurHornProjection,
  FiniteIndexTransport, SquareSingularBasis, ProductSingularValues, EigenvalueVariation,
  MaximumVolumeRankAdapted, Arnoldi, ArnoldiProcess, Lanczos, LanczosRecurrence, Jacobi, Invariance,
  InverseMoments/SchurComplement, MoorePenrose, SketchAndProject/Core, Kaczmarz{Extensions,Probability}.
* Import drops (Basic/Dilation lost ExpLog, CholeskySemidefinite lost ComplexCholeskyPivot +
  RealComplexCFC, GramIsometry lost KyFan): the full reverse-import closure of these three files (127
  modules, 23 maximal targets) was rebuilt successfully after the two import fixes above.
