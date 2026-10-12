# Dedup round, agent F2b (basic norm API)

Theme: `Matrix/Norms/Core.lean` (plus two split-off Norms files) is the home of the basic norm API.

## Findings executed

| id | keeper / new home | dropped or moved | files touched |
|---|---|---|---|
| matrix_norms#28 | `NLAlib.dotProduct_self_nonneg` (Norms/Core) | private `dotProduct_self_nonneg'` ×2 | Factorizations/Householder, Factorizations/GramSchmidt |
| matrix_norms#29, matrix_spectral#37 (norm part) | new `Matrix/Norms/Reindex.lean` | moved `frobInner_reindex` (NuclearFiniteIndex), `frobSq_reindex`, `frobNorm_reindex`, `specNorm_reindex` (+ private `reindex_frame_orth`) (Spectral/FiniteIndexTransport); `frobSq_reindex` is now `frobInner_reindex A A em en` | Norms/NuclearFiniteIndex, Spectral/FiniteIndexTransport |
| matrix_norms#30 | new `Matrix/Norms/KyFanNorm.lean` (imports only `Mathlib.Analysis.InnerProductSpace.SingularValues`) | moved defs `kyFanNorm`, `nuclearNorm` (names and atlas tags unchanged); Inequalities/KyFan imports it | Inequalities/KyFan |
| matrix_spectral#23 | `sqrt_mulVec_dotProduct_le_specNorm_mul` (moved SpectralBounds → Norms/SpectralNormBounds) | deleted `sqrt_mulVec_dotProduct_le` and private `norm_toLp_eq_sqrt` (uses → `sqrt_dotProduct_self_eq_norm`) in Probability/Concentration/Basic/Net | Spectral/SpectralBounds, Net |
| matrix_spectral#24 | `mulVec_dotProduct_mulVec_self` | deleted `dotProduct_transpose_mul_mulVec`; uses rewritten with `← mulVec_dotProduct_mulVec_self` | Spectral/Core, Spectral/ProductSingularValues, Spectral/CourantFischer, Spectral/SpectralMinimum, Factorizations/RankRevealingTrailing (reference edits) |
| matrix_spectral#36 | Norms/Core: `specNorm_zero`, `mulVec_dotProduct_mulVec_le_frobSq_mul`, `sqrt_dotProduct_add_le`, `norm_eq_sqrt_sum_sq`, `norm_eq_sqrt_dotProduct`, `sqrt_dotProduct_self_eq_norm` (now a one-line corollary of `norm_eq_sqrt_dotProduct`); Norms/SpectralNormBounds: `abs_specNorm_sub_specNorm_le`, `abs_specNorm_sub_specNorm_le_frobNorm` (keeps `atlas: norm-lipschitz`) | moved from Spectral/Core | Spectral/Core |
| krylov#21 | `specNorm_diagonal_le` → Norms/SpectralNormBounds (generalised index name only) | moved from Krylov/Spectral/SubspaceIteration | SubspaceIteration |
| krylov#29 | `specNorm_blockDiagonal_const_le` (+ its dependency `specNorm_le_of_forall_sum_sq_mulVec_le`) → Norms/SpectralNormBounds; `frobNorm_one_sq` → Norms/Core; `frobNorm_le_trace_of_posSemidef` → Matrix/Perturbation/EigenvalueTrace (now proved with `frobSq_eq_sum_sq_eigenvalues`) | moved from Estimation/Trace/HutchinsonTail, Estimation/Quadrature/SLQ | HutchinsonTail (+ import EigenvalueTrace), SLQ |
| matrix_pert#49 | `sqrt_dotProduct_self_pos`, `sqrt_dotProduct_sub_le` → Norms/Core next to `sqrt_dotProduct_add_le` | moved from Perturbation/Conditioning | Conditioning |
| matrix_pert#50 | `frobInner_eq_trace_mul_transpose` → Norms/Core next to `frobInner_eq_trace`; `nuclearNorm_eq_trace_sqrt_gram`, `nuclearNorm_eq_trace_sqrt_rowGram` and their dependency `nuclearNorm_eq_of_gram_eq` → new `Matrix/Norms/NuclearGram.lean` | moved from Factorizations/ProcrustesRotations, Factorizations/Procrustes, Factorizations/ScaledOrthogonal (F2a's file: one declaration cut, reference-level) | those three files |

Also moved (needed by `specNorm_reindex` at the Norms layer): `specNorm_mul_left_of_hasOrthonormalCols` and
`specNorm_mul_transpose_right_of_hasOrthonormalCols` from Spectral/SpectralBounds to Norms/SpectralNormBounds
(names and `atlas: norms-frob-spec` tags unchanged).

Rename table: `docs/renames/2026-10-12-dedup-F2b.json` (two public drops; all moves keep their names).

## Layout decision (Core size)

Norms/Core was already 601 lines before this round; it is now ~675 with the vector/Frobenius basics. The
spectral-norm additions went to a new `Matrix/Norms/SpectralNormBounds.lean` (imports Core and
`Mathlib.Data.Matrix.Block` only) and the reindex lemmas to a new `Matrix/Norms/Reindex.lean` (imports
SpectralNormBounds). `Spectral/Core` imports SpectralNormBounds and `Spectral/FiniteIndexTransport` imports
Reindex, so every previous user still sees the moved names transitively. Core gained one import,
`Mathlib.LinearAlgebra.Matrix.DotProduct` (for `dotProduct_self_eq_zero`). Splitting Core further (e.g.
moving its existing "spectral-norm helpers" section to SpectralNormBounds) would need import edits in many
dependants; left as a follow-up.

## Files created

- `NLAlib/Matrix/Norms/SpectralNormBounds.lean`
- `NLAlib/Matrix/Norms/Reindex.lean`
- `NLAlib/Matrix/Norms/KyFanNorm.lean`
- `NLAlib/Matrix/Norms/NuclearGram.lean`

The coordinator must regenerate the aggregators (`NLAlib/Matrix/Norms.lean`); `scripts/reorg.py` has no
`--gen-aggregators` flag, so I did not touch them.

## Compilation

Built with `lake build`: Norms/{Core, SpectralNormBounds, Reindex, KyFanNorm, NuclearGram}, every edited
file (Spectral/{Core, SpectralBounds, FiniteIndexTransport, ProductSingularValues, CourantFischer,
SpectralMinimum}, Inequalities/KyFan, Factorizations/{Procrustes, ProcrustesRotations, ScaledOrthogonal,
Householder, GramSchmidt, RankRevealingTrailing}, Perturbation/{Conditioning, EigenvalueTrace},
Estimation/{Trace/HutchinsonTail, Quadrature/SLQ}, Krylov/Spectral/SubspaceIteration,
Probability/Concentration/Basic/Net) and all 67 modules referencing a moved name: all green (only the
pre-existing GramSchmidt scaffold `sorry`). `check_layers.py`: the only violation is the unrelated
`RademacherMgfCgf → HutchinsonLaws`.

## Not done / follow-ups

- `rectangular` generalisation of `nuclearNorm_eq_trace_sqrt_gram` (matrix_pert#50): not attempted;
  `nuclearNorm_eq_of_gram_eq` needs equal shapes, so a rectangular version needs a different proof.
- `specNorm_le_of_forall_sum_sq_mulVec_le` (now in SpectralNormBounds) duplicates
  `specNorm_le_of_mulVec_sq_le` (Norms/EuclideanOperatorBounds, which imports Spectral/SpectralBounds
  although its proof needs only Core). Suggested follow-up (krylov#1 / matrix_norms#26): move
  `specNorm_le_of_mulVec_sq_le` into SpectralNormBounds and drop the sum-of-squares form.
- `frobSq_eq_sum_eigenvalues_sq` in HutchinsonTail is now unused there (its only use moved with
  `frobNorm_le_trace_of_posSemidef`); its deletion is krylov#0 / matrix_pert#21 (not in my task file).
- Net keeps the private bridge `norm_toLp_mulVec_le` (one-line Mathlib proof used twice in norm form).
- `HasOrthonormalCols.reindex`, `moorePenroseInverse_reindex`, `mul_reindex` left in FiniteIndexTransport
  as instructed.
