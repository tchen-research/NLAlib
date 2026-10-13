# F4 wave 1, agent M2, cluster I: `NLAlib/Matrix/Inequalities` (2026-10-13)

Status: DONE (2026-10-13; resumed once after a usage-limit stop). Rename table: `docs/renames/2026-10-F4-M2-I.json`.

## Items

1. **Prefix sums (N3/D2).** `sumLargest` is the one prefix-sum definition (`Majorization.lean`);
   the `(partial)` markers on `sumLargest`, `WeaklyMajorized`, `Majorized` are gone
   (`atlas: majorization-def`). `eigenvaluePrefix hA (k : ℕ) := sumLargest hA.eigenvalues₀ k`
   over `[RCLike 𝕜]` (`KyFan.lean`; no proof argument). API: `eigenvaluePrefix_eq_sum_castLE
   (hk : k ≤ card n)`, `eigenvaluePrefix_of_card_le`, `eigenvaluePrefix_zero`;
   `trace_compression_le_eigenvaluePrefix` / `sum_bottom_eigenvalues_le_trace_compression` are
   over 𝕜 with `RCLike.re (Qᴴ * A * Q).trace`. Lemmas M1 can use for `kyFanNorm A k :=
   sumLargest (fun i : Fin (min (card m) (card n)) => singularValues A i) k` (or a `Fin N` list):
   `sumLargest_eq_prefix_of_antitone (a : Fin n → ℝ) (ha : Antitone a) (k) : sumLargest a k =
   ∑ i : Fin n, if i.val < k then a i else 0` (`MajorizationProperties.lean`),
   `sum_fin_ite_lt_eq_sum_castLE (hk : k ≤ n) (a) : (∑ i : Fin n, if i.val < k then a i else 0) =
   ∑ i : Fin k, a (Fin.castLE hk i)` (same file), `sum_fin_ite_lt_eq_sum_range (hk : k ≤ N) (g : ℕ → ℝ)
   : ∑ l : Fin N, (if l < k then g l else 0) = ∑ i ∈ range k, g i` (`VonNeumann.lean`),
   `sumLargest_eq_sum_of_card_le`, `sumLargest_zero`, `sumLargest_add_le`, `sumLargest_comp_perm`,
   `sum_le_sumLargest`.
2. **Mirsky (D3).** `Inequalities/Mirsky.lean` + `MirskyPadded.lean` → `SingularValueMajorization.lean`
   (one file; theorem names unchanged), retagged `weyl-mirsky` (atlas entry "Weyl and Mirsky
   perturbation bounds for singular values"; the old tag was `lidskii (partial)`). Stays over `ℝ`:
   the proof goes through the real dilation spectrum `Spectral/RealDilationSpectrum.lean`
   (`eigenvalues₀_dilation_top/bottom`, ℝ and `Fin`), owned by M1; the public statements are
   `Fintype` already.
3. **Von Neumann.** `frobInner_le_sum_singularValues_mul` is now stated over `[Fintype m] [Fintype n]`
   (`Matrix m n ℝ`, sum over `range (min (card m) (card n))`), with the `Fin` proof as a private step.
   Stays over `ℝ` because it uses `singularValues_isometry_mul` / `singularValues_mul_orthogonal`
   (`Spectral/SingularValueInvariance.lean`, ℝ-only, M1) and the real squares argument
   (`sum_sq_col_eq_one`); the 𝕜 version needs the 𝕜 invariances first (request to M1 below).
   `frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one` (KyFan.lean) is over `Fintype` too.
   `trace_compression_le_eigenvaluePrefix` uses `Qᴴ * A * Q` over 𝕜; `exists_trace_compression_eq_eigenvaluePrefix`
   stays ℝ (its proof uses the real `eq_eigenvectorUnitary_mul_diagonal_mul_transpose`).
4. **D4.** `HadamardOrder.lean`: `abs_quadForm_le_iff_neg_le_and_le` (`↔ -A ≤ B ∧ B ≤ A`), the
   Hadamard sandwich theorem split into `neg_hadamard_le_hadamard_of_neg_le_of_le` and
   `hadamard_le_hadamard_of_neg_le_of_le`; `TraceTail.lean`:
   `sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq (hRA : R ≤ A)`; `HadamardExponential.lean`:
   the bundle `entrywise_exponential_positivity_characterizations` is deleted (its last conjunct
   was already the `≤` form `sum_inv_factorial_smul_map_pow_le_map_exp`). No `IsSymm` in any
   statement of the cluster (VonNeumann's only use was a proof-internal `have`).
5. **D5.** `ComplexDiagonalMajorization.lean` deleted; `Schur.lean` is over 𝕜:
   `norm_sq_entries_mem_doublyStochastic_of_hasOrthonormalCols` (𝕜, `HasOrthonormalCols P`),
   `re_diagonal_eq_norm_sq_eigenvectorUnitary_mulVec`, `majorized_diagonal_eigenvalues`
   (`Majorized (fun i => RCLike.re (A i i)) hA.eigenvalues`), `re_diagonal_mem_Icc_eigenvalues₀`;
   `sum_convex_diagonal_le_trace_cfc` (Peierls) stays ℝ because `trace_cfc_eq_sum_eigenvalues`
   (`Functions/CFCTrace.lean`, cluster F) is ℝ. `HermitianPart.lean` consumes the 𝕜 versions.
6. **N2.** Every `u ⬝ᵥ u = 1` hypothesis/conclusion in statements (`PlaneRotationSpectrum`,
   `SchurHornDescent`, `SchurHornResidual`, `SchurHornProjection`, `SchurHorn`, `Kantorovich`:
   `(x ⬝ᵥ x) ^ 2` → `‖WithLp.toLp 2 x‖ ^ 4`) is `‖(WithLp.toLp 2 u : EuclideanSpace ℝ n)‖ = 1`;
   the raw `Rᵀ * R = 1` hypotheses in `hmin` (Descent, Derivative) are `HasOrthonormalCols R`.
   Bridge used: `norm_toLp_eq_one_iff_dotProduct_self_eq_one` (`SchurHornProjection.lean`; candidate
   for `Norms/Core` next to `norm_toLp_sq_eq_dotProduct_self`).
7. **N1.** No file-level `open scoped … Matrix.Norms.*` remains in the cluster; the `‖·‖` signature
   hits reported by `check_norms.py` are listed under "Residual lint hits" (all vector or entry norms).
8. **I7.** `check_docstrings.py NLAlib/Matrix/Inequalities`: 0 hits (from 86). Manuscript keys
   replaced by Tropp 2015 §4.8 / Buchholz 2001 (trace-power files), Chen–Epperly–Tropp–Webber 2023
   (trace tail), Horn–Johnson Thm 4.3.48 (Schur–Horn variational files).
9. **Bundles.** Deleted: `BlockContractionToolkit`, `DeterminantConvexityToolkit`,
   `DeterminantInequalityToolkit`, `HadamardToolkit`, `HornProductToolkit`, `KyFanNormToolkit`,
   `KyFanToolkit`, `LidskiiToolkit`, `MajorizationToolkit` (modules), the Schur–Horn bundle,
   the two Kantorovich bundles (`QuadraticConditionBounds.lean`), the real-part bundle
   (`HermitianPartToolkit.lean` → `RealPartMajorization.lean`, keeping the `iff`). The
   `inequality ∧ equality-case` theorems are split into two public theorems each
   (`abs_det_le_prod_column_norm` / `abs_det_eq_prod_column_norm_iff`,
   `det_rpow_inv_card_add_le` / `det_add_rpow_inv_card_eq_iff`, `det_overlapping_blocks_le` / `_eq_iff`,
   `det_principal_three_sets_le` / `_eq_iff`, `det_principal_union_mul_inter_le_of_posDef` / `_eq_iff_of_posDef`,
   `det_pow_card_pred_le_prod_complement_singleton` / `det_pow_card_pred_eq_prod_complement_singleton_iff`,
   `det_rpow_mul_le_det_smul_add` / `det_smul_add_eq_rpow_mul_iff`, `trace_le_of_le` / `trace_eq_iff_of_le`,
   `principalMinor_pow_pred_le_prod_erase` / `_eq_iff`, `spectrum_mul_nonempty_of_posDef` /
   `sInf_spectrum_mul_nonneg_of_posDef`), the combined proof kept as a private `_aux`.
   Component theorems keep `(partial)` where they prove part of an entry; `(partial)` was removed
   where the theorem is the entry's statement (Ky Fan maximum principle, Lidskii, Schur's theorem,
   Kantorovich, the real-part `iff`).

## Requests

- **M1** (`Norms/KyFanNorm`, `Norms/NuclearNorm`, `Norms/NuclearPSD`, `Norms/FanDominance`,
  `Norms/NuclearHermitian`, `Norms/SchattenTrace`, `Perturbation/*`):
  - The deleted bundle `ky_fan_norm_toolkit_properties` carried `atlas: ky-fan-norms-def`; its
    components (`kyFanNorm_nonneg`, `kyFanNorm_add_le`, `kyFanNorm_smul`, `kyFanNorm_eq_zero_iff`,
    `kyFanNorm_orthogonal_mul`, `kyFanNorm_mul_orthogonal`, `kyFanNorm_transpose`,
    `kyFanNorm_one_eq_specNorm`, `nuclearNorm_*`, `isGreatest_nuclearNorm_frobInner`,
    `nuclearNorm_eq_trace_of_posSemidef`, `specNorm_le_nuclearNorm`, `nuclearNorm_le_rank_mul_specNorm`,
    `frobNorm_le_nuclearNorm`, `nuclearNorm_le_sqrt_rank_mul_frobNorm`) should carry the tag.
    Likewise `lidskii_toolkit_properties` → `invariantNorm_rectangularDiagonal_singularValues_add_sub_le`
    (`FanDominance`) and `sum_abs_eigenvalues₀_add_sub_le_nuclearNorm` (`NuclearHermitian`) take
    `atlas: lidskii`.
  - `Norms/FanDominance.lean` imports `NLAlib.Matrix.Inequalities.Mirsky` → `…SingularValueMajorization`.
  - `eigenvaluePrefix hA hk` → `eigenvaluePrefix hA k` in `Perturbation/{SpectralFrameWeights,
    DavisKahanPopulation, DavisKahanToolkit, PopulationTraceGap, EigenvalueVariation, DavisKahanFrames}`;
    `unfold eigenvaluePrefix` → `rw [eigenvaluePrefix_eq_sum_castLE hA hk]`;
    `trace_compression_le_eigenvaluePrefix` now gives `RCLike.re (Qᴴ * A * Q).trace ≤ …`
    (at ℝ: `simp only [RCLike.re_to_real, Matrix.conjTranspose_eq_transpose_of_trivial, Fintype.card_fin] at h`).
  - `frobInner_le_sum_singularValues_mul` (`Norms/SchattenTrace`) is `Fintype`; at `Fin` rewrite
    `Fintype.card_fin`. `frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one` (`Norms/NuclearNorm`) likewise.
  - `norm_sq_entries_mem_doublyStochastic (U : unitaryGroup n ℂ)` in
    `Perturbation/HoffmanWielandtNormal.lean` is a special case of the 𝕜 lemma
    `norm_sq_entries_mem_doublyStochastic_of_hasOrthonormalCols` (`Inequalities/Schur.lean`,
    `HasOrthonormalCols P`); M1 can delete theirs (then the longer name can be shortened).
  - For von Neumann / Ky Fan singular-value statements over 𝕜: 𝕜 versions of
    `singularValues_isometry_mul`, `singularValues_mul_orthogonal` (`Spectral/SingularValueInvariance`).
- **Owner I**: `weyl-mirsky` now has the weak-majorization theorems
  (`weaklyMajorized_abs_singularValues_add_sub`, `_padded`, `sum_abs_singularValues_add_sub_le_sum_range`);
  the `lidskii` entry keeps `majorized_eigenvalues₀_add_sub`, `sum_eigenvalues₀_add_le_sum_add_eigenvaluePrefix`.
  `check_norms.py` flags `‖(WithLp.toLp 2 u : EuclideanSpace ℝ n)‖` (vector norm) and entry norms
  `‖P i j‖` as "`‖·‖` on a matrix" — see residual hits.
- **Wave 2**: `LowRank/Cholesky/RandomPivotedCholesky` calls
  `sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq` with a `(A - R).PosSemidef` argument
  (now `R ≤ A`, definitionally the same under `MatrixOrder`); `RandomMatrix/Gaussian/InverseMoments/OffDiagonal`
  uses `transpose_planeRotation_mul_self` (now `hasOrthonormalCols_planeRotation`, M2 phase 1).

## Scaffolds

None.

## Not done / residual

- **Lint.** `check_docstrings.py NLAlib/Matrix/Inequalities`: 0 hits. `check_norms.py`: 21 hits,
  all false positives of the "`‖·‖` on a matrix" rule: vector norms
  `‖(WithLp.toLp 2 u : EuclideanSpace ℝ n)‖` (the N2 spelling; `ColumnDeterminantBound`,
  `Kantorovich`, `QuadraticConditionBounds`, `PlaneRotationSpectrum`, `SchurHorn*`), entry norms
  `‖P i j‖`/`‖A i j‖₊` (`Schur`, `TraceYoung`, `HadamardPowerSeries`) and `(…).trace.re` lines
  (`TracePowers`, `TraceYoung`, where the `‖` is inside a `unitaryGroup` coercion). No file-level
  `open scoped … Matrix.Norms.*` remains and no matrix norm is spelled `‖A‖` in a signature.
  Request to owner I: have `check_norms.py` skip `WithLp.toLp` and `‖X i j‖` patterns.
- **Still ℝ (proof obstruction recorded):** `SingularValueMajorization.lean` (uses M1's real
  dilation spectrum `Spectral/RealDilationSpectrum`), `VonNeumann.lean` (uses the ℝ-only
  `singularValues_isometry_mul`/`singularValues_mul_orthogonal` of `Spectral/SingularValueInvariance`
  and a real-squares argument), `exists_trace_compression_eq_eigenvaluePrefix` (real
  `eq_eigenvectorUnitary_mul_diagonal_mul_transpose`), `sum_convex_diagonal_le_trace_cfc`
  (`trace_cfc_eq_sum_eigenvalues` in `Functions/CFCTrace` is ℝ), the Ky Fan norm/gauge consumers
  (`KyFanNorms`, `KyFanSums`, `KyFanAttainment`: they are built on M1's `kyFanNorm` over ℝ).
  They become 𝕜 once the M1 inputs listed under "Requests" are 𝕜.
- **`hadamard-fischer-inequalities (partial)`** stays on the split Szász components in
  `PrincipalMinorProductBounds.lean` (each proves one step of the entry).
- **Downstream (wave 2)** call sites of the renames in the JSON table were not edited
  (`LowRank/Cholesky/RandomPivotedCholesky`, `RandomMatrix/Gaussian/InverseMoments/OffDiagonal`,
  M1's `Norms/FanDominance`, `Norms/NuclearNorm`, `Norms/SchattenTrace`, `Perturbation/*`
  `eigenvaluePrefix` users).
- **Build.** `flock /tmp/m2-lake.lock lake build NLAlib.Matrix.Inequalities`: every Inequalities
  module that is reachable builds; the aggregator is blocked only by files of other owners in
  flux at the time of the last run (`Functions/PolynomialCalculus.lean` — M2-F, uses the deleted
  real twin `specNorm_mul_transpose_right_of_hasOrthonormalCols`; `Spectral/EckartYoung.lean` —
  M1, uses `IsBestRankApprox` renamed `IsBestFrobRankApprox` by M2-S; `Subspaces/Stiefel.lean` —
  M2-S). 30 of the 68 Inequalities modules are built and green; the other 38 (every module that
  imports `Spectral/EckartYoung`, `Functions/PolynomialCalculus` or `Subspaces/Stiefel`
  transitively: `BlockContraction`, `BlockOrderConsequences`, `BlockQuadratic`,
  `BlockStrictContraction`, `FiniteExponentialGram`, `FischerDeterminant`, `HadamardDeterminantLower`,
  `HadamardExponential`, `HadamardInverse`, `HadamardMinimumSpectrum`, `HadamardOrder`,
  `HadamardPowerOrder`, `HermitianPart`, `HornPowerSums`, `Kantorovich`, `KyFan`, `KyFanAttainment`,
  `KyFanNorms`, `KyFanSums`, `Lidskii`, `MajorizationConvex`, `MajorizationHLP`,
  `MajorizationSupport`, `MajorizationWeakSupport`, `OverlappingBlockDeterminant`,
  `PositiveSpectralEndpoints`, `PrincipalOverlapDeterminant`, `QuadraticConditionBounds`,
  `RealPartMajorization`, `RelativeSpectrum`, `Schur`, `SchurHorn`, `SchurHornProjection`,
  `SeparatingPSDVector`, `SingularValueMajorization`, `StrictRelativeSpectrum`, `VonNeumann`,
  `Wielandt`) were green at the previous instance's last build and are blocked, not failing;
  rerun `flock /tmp/m2-lake.lock lake build NLAlib.Matrix.Inequalities` once those three files
  build. Last-minute edits after that build: `PrincipalMinorProductBounds.lean` (built green),
  `KyFanNorms.lean` (`(partial)` removed from `kyFanSeminorm`'s tag) and `VonNeumann.lean`
  (private `sum_sq_col_eq_one` takes `HasOrthonormalCols`); the last two are among the blocked
  modules.
