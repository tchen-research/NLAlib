# F4 wave 1, fork M2-Fa (cluster `Matrix/Factorizations`): report

Status: DONE (2026-10-13; resumed once after a usage-limit termination).
Rename table: `docs/renames/2026-10-F4-M2-Fa.json`. Build: see the end.

## Items done

1. **D2 elimination step.** `CholeskyStep.lean` → `EliminationStep.lean`, `choleskyStep` →
   `eliminationStep` (any field), PSD API over `[RCLike 𝕜]`: `isHermitian_eliminationStep`,
   `posSemidef_eliminationStep`, `eliminationStep_le : eliminationStep A t ≤ A` (D4: Loewner
   order instead of `(A - choleskyStep A t).PosSemidef`), `eliminationStep_apply_pivot_left/right`,
   `ker_mulVecLin_le_ker_eliminationStep`, `ker_eliminationStep_eq_sup_span_singleton`,
   `rank_eliminationStep_add_one_eq`, `rank_eliminationStep_lt`,
   `star_dotProduct_eliminationStep_mulVec`. `ComplexCholeskyPivot.lean` is deleted:
   `complexCholeskyResidualStep` was `eliminationStep` by `rfl` and its lemmas are the 𝕜 lemmas
   above; the pivot law is `choleskyPivotProbability (R : Matrix n n 𝕜) (i : n) : ℝ` in the new
   `CholeskyPivotProbability.lean` (`sum_choleskyPivotProbability`, `choleskyPivotProbability_nonneg`,
   one-step mean `sum_choleskyPivotProbability_smul_eliminationStep_eq`, expected trace
   `sum_choleskyPivotProbability_mul_re_trace_eliminationStep_eq`), using M2-B's
   `Basic/PosSemidefTrace.lean` (`re_trace_nonneg_of_posSemidef`, `re_trace_eq_zero_iff_of_posSemidef`,
   `diag_eq_ofReal_re_of_posSemidef`).
2. **D2 Givens.** `givens i j c s := planeRotation (Pi.single i 1) (Pi.single j 1) c s`
   (`Basic/PlaneRotation.lean`), `givens_apply` (entries for `i ≠ j`), Golub–Van Loan orientation
   documented in the module and definition docstrings: `G(i,j,θ)` has `(i,i) = c, (i,j) = s,
   (j,i) = −s, (j,j) = c`, and **`Gᵀ` zeroes**: `givensSin a b = −b/√(a²+b²)`,
   `givensRotation_transpose_mulVec_apply_right : ((givensRotation i j x)ᵀ *ᵥ x) j = 0`,
   `givensRotation_transpose_mulVec_apply_left : … i = √(x_i² + x_j²)`; Hessenberg QR recursion
   `H_{k+1} = G_kᵀ H_k`, `Q_k = G_0 ⋯ G_{k−1}` (GVL Alg. 7.4.1). Public orthogonality statements
   are `hasOrthonormalCols_givens`, `hasOrthonormalCols_givensRotation`, `hasOrthonormalCols_givensQRQ`
   (the `Gᵀ G = 1` forms stay as proof helpers). `transpose_givens : Gᵀ = G(i,j,−θ)`,
   `transpose_planeRotation` added.
3. **D4 `IsSymm` → `IsHermitian`** in every statement: `Cholesky.lean` (`eq_cholesky_mul_transpose_of_pivotSchur`,
   `isCholesky_cholesky`, `choleskySucceeds_iff_posDef`), `Givens.lean` (`isHermitian_mul_of_isQR`,
   `isTridiagonal_mul_of_isQR`, `isTridiagonal_givensQR_snd_mul_fst`), `Hessenberg.lean`
   (`IsHessenbergForm.isHermitian`, `.isTridiagonal`). No `IsSymm` remains in the cluster's
   statements (`grep IsSymm NLAlib/Matrix/Factorizations` is empty).
4. **D4 existence over `[LinearOrder n]`** via `monoEquivOfFin` transport (`IsLU.submatrix`,
   `exists_eq_mul_transpose_submatrix`, `leadingMinor_submatrix_monoEquivOfFin`,
   `submatrix_monoEquivOfFin_symm`): `exists_isLU_of_forall_leadingMinor_ne_zero`,
   `exists_isLU_iff_forall_leadingMinor_ne_zero` (hypotheses with the new `leadingMinor`),
   `exists_isCholesky_iff_posDef`, `exists_eq_mul_transpose_of_posSemidef` (the `_fintype`
   twin `exists_cholesky_of_posSemidef_fintype` and `CholeskySemidefinite.lean` are gone);
   `invariantNorm_sub_polar_le_sub_isometry` is the one public (Fintype) statement, the `_fin`
   step is private. LU uses `Basic/LeadingMinor.lean` throughout (`leadingSubmatrix A k` without
   proof argument, `IsLU.leadingMinor_eq_prod`, `leadingMinor_one`,
   `leadingMinor_succ_eq_mul_leadingMinor_pivotSchur`, `luSucceeds_iff_forall_leadingMinor_ne_zero`).
   `exists_isFullQR` stays on `Fin m`/`Fin n` on purpose: `IsFullQR` (square `Q : m × m`, upper
   trapezoidal `R : m × n`) is itself a `Fin`-indexed predicate; the `[LinearOrder n]` existence
   statement for the `[LinearOrder n]` predicate `IsQR` is `exists_isQR` (`QRExistence.lean`,
   already Fintype/LinearOrder).
5. **D1.** `QR.lean` `isFullQR_mul_borderedUpper (hW : HasOrthonormalCols W)`;
   `hasOrthonormalCols_list_prod (hl : ∀ M ∈ l, HasOrthonormalCols M)` (was `Mᵀ * M = 1`),
   `hasOrthonormalCols_householderQ`, `hasOrthonormalCols_hessenbergQ` as the public forms. No
   raw `Pᵀ * P = 1` hypothesis remains in a statement.
6. **I7.** "(label to verify)" resolved: Higham 2002 Thm 10.1 (SPD Cholesky), Thm 10.9 (pivoted
   semidefinite Cholesky), §10.3; Trefethen–Bau Lect. 22 eq. (22.4) / Higham §9.3 eq. (9.13)
   for the LU growth factor. `check_docstrings.py NLAlib/Matrix/Factorizations`: 0 hits.
7. **N1/N2.** No file-level `open scoped … Matrix.Norms.*` in the cluster; the Procrustes/polar
   statements use `frobSq`/`frobNorm`/`specNorm`. Vector norms in statements are
   `‖WithLp.toLp 2 x‖` (`gramSchmidtCol_eq`, `norm_smul_gramSchmidtCol`, `householder_mulVec`,
   `householder_mulVec_householderVector`); `gramSchmidtCol`/`householderVector` definition bodies
   keep `√(x ⬝ᵥ x)`.
8. **Bundles** deleted with tags moved to the components: `cholesky_decomposition`
   (`CholeskyToolkit.lean`), `polar_decomposition_properties` (`PolarToolkit.lean`),
   `orthogonal_procrustes_properties` (`ProcrustesToolkit.lean`), `lu_row_inclusion_properties`
   (`LURowInclusion.lean`).
9. `IsHessenbergForm` uses `HasOrthonormalCols Q`; it stays on `Fin n`/ℝ because M1's
   `IsUpperHessenberg`/`IsTridiagonal` (`Structured/Hessenberg.lean`) are still `Fin n`/ℝ at the
   time of writing (M1 renamed `isTridiagonal_of_isSymm` → `isTridiagonal_of_isHermitian`, which
   this cluster now uses).

## Scaffolds

None added (the pre-existing `SCAFFOLD: hessenberg-reduction` in `Hessenberg.lean` is unchanged).

## Requests

- **M1**: when `IsUpperHessenberg`/`IsTridiagonal` become `[LinearOrder n] [Zero α]`,
  `IsHessenbergForm` (Factorizations/Hessenberg.lean) and the Givens Hessenberg-QR theorems
  follow in wave 2 (they consume the `Fin n` spelling `(j : ℕ) + 1 < i`). A real bridge
  `norm_toLp_eq_sqrt_dotProduct_self : ‖WithLp.toLp 2 x‖ = √(x ⬝ᵥ x)` next to
  `norm_toLp_sq_eq_dotProduct_self` in `Norms/Core.lean` would let `GramSchmidt.lean` and
  `Householder.lean` drop their private copies.
- **A1 (wave 2, `Krylov/Spectral/QRAlgorithm`)**: `givensQRState`/`givensQRQ` orientation changed
  (`Gᵀ` on the left, `Q = G_0 ⋯ G_{n−2}`); `isQR_givensQR`, `givensQRQ_mul_givensQRState`,
  `givensQRQ_transpose_mul_self` keep their names.
- **A2 (wave 2, `LowRank/Cholesky/*`)**: `choleskyStep` → `eliminationStep` (+ lemma names);
  `LowRank/Cholesky/CholeskyPivot.lean`'s real `choleskyPivotProbability` duplicates the 𝕜 one in
  `Matrix/Factorizations/CholeskyPivotProbability.lean` — delete the LowRank copy and import this
  file; `LowRank/Cholesky/ComplexCholeskyHistories.lean` imports the deleted
  `Factorizations/ComplexCholeskyPivot` (use `EliminationStep` + `CholeskyPivotProbability` at `𝕜 = ℂ`;
  `Complex.re` → `RCLike.re`).

## Not done / residual

- `exists_isFullQR` over `[LinearOrder n]`: not done, by design (see item 4).
- `check_norms.py NLAlib/Matrix/Factorizations` residual hits: `GramColumnExchange.lean:21`,
  `GramSchmidt.lean:81/88`, `Householder.lean:62/147` are vector norms
  `‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖` flagged as matrix norms (false positives of the
  lint); `GramSchmidt.lean:46`, `Householder.lean:40` are the private bridge
  `norm_toLp_eq_sqrt_dotProduct_self` (see the request to M1).
