# F4 wave 1, fork M2-B (cluster `Matrix/Basic`): report

Status: DONE (2026-10-13; resumed once after a usage-limit termination). Rename table:
`docs/renames/2026-10-F4-M2-B.json`. Build that passed:
`flock /tmp/m2-lake.lock lake build NLAlib.Matrix.Basic` (exit 0).

## Items

1. **D5.** `Basic/ComplexPosSemidefTrace.lean` → `Basic/PosSemidefTrace.lean` over `[RCLike 𝕜]`
   (`diag_eq_ofReal_re_of_posSemidef`, `trace_eq_ofReal_re_of_posSemidef`,
   `re_trace_nonneg_of_posSemidef`, `re_trace_eq_zero_iff_of_posSemidef`, thin `RCLike.re`
   wrappers of Mathlib's `PosSemidef.trace_nonneg`/`trace_eq_zero_iff`); the ℂ-only
   `apply_eq_zero_of_posSemidef_of_apply_self_eq_zero` was already the 𝕜 lemma of
   `Basic/GramVanishing.lean`. `Basic/ComplexFullRowInverse.lean` → the 𝕜 theorems
   `isUnit_mul_conjTranspose_of_rank_eq_card`, `mul_pinvR_of_rank_eq_card` in
   `Basic/Pseudoinverse.lean`. Both ℂ files deleted.
2. **D2/D4.** `Basic/GeneralizedSchurComplement.lean` is over 𝕜: `generalizedSchurComplement A B C
   = C − Bᴴ A⁺ B` for `fromBlocks A B Bᴴ C`; Albert's criterion `posSemidef_fromBlocks_iff` carries
   `atlas: generalized-schur-complement-psd`; the variational theorems are stated with
   `star x ⬝ᵥ (M *ᵥ x)`; the order bounds are Loewner: `generalizedSchurComplement_nonneg`
   (`0 ≤ M/A`), `generalizedSchurComplement_le` (`M/A ≤ C` for `A.PosSemidef`; was
   `(C - schurComplement).PosSemidef`); the bundle `generalized_schur_complement` is gone.
   `pivotSchur` stays ℝ/`Fin (n+1)`; its statements take `IsHermitian`
   (`isHermitian_pivotSchur`, `posDef_iff_pivotSchur`).
3. **D1.** `IsMoorePenroseInverse.unitary_transform` takes `HasOrthonormalCols U/V`. No raw
   `Pᴴ * P = 1` hypothesis remains in a Basic statement.
4. **Docs.** `moorePenroseInverse`: defined by choice, well defined by uniqueness, formula
   `moorePenroseInverse_eq_svd` (renamed from `IsSVD.moorePenroseInverse_eq`) named in the module
   and definition docstrings. `rayleighQuotient`: meaningful for Hermitian `A` only. `pinvL`/`pinvR`:
   junk `0` on rank-deficient input; the theorems take `IsUnit (Gᴴ * G)`/`IsUnit (G * Gᴴ)`.
5. **N2.** `IsLeastSquaresSolution` and its API use `‖WithLp.toLp 2 ·‖` (squared where the source
   squares); the dot-product forms are private helpers or `isLeastSquaresSolution_iff_dotProduct`.
6. **N1.** No file-level `open scoped … Matrix.Norms.*` in Basic (`PositiveSemidefiniteSeries`,
   `PositiveDefiniteClosure`, `GeneralizedSchurComplement`, `MoorePenroseTransformations`,
   `PSDDuality`, `MoorePenrose` cleaned; proofs that need the normed API use
   `open scoped Matrix.Norms.L2Operator in`). The `‖·‖` in `Pseudoinverse.lean` statements is
   `specNorm`/`frobNorm`.
7. **I7.** `python3 scripts/check_docstrings.py NLAlib/Matrix/Basic`: 0 hits. No definition
   carries `(partial)` (`compoundMatrix`, `IsLeastSquaresSolution` fixed).
8. **A11.** `Basic/QuadForm.lean` has `Matrix.IsHermitian.re_quadForm_mem_Icc` (Rayleigh bounds
   from an eigenvalue enclosure) and the helper A1 asked for,
   `Matrix.IsHermitian.eigenvalues_conjTranspose_mul_mul_same_mem_Icc (hA) (hQ : HasOrthonormalCols Q)
   (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c) (j) :
   (Matrix.isHermitian_conjTranspose_mul_mul Q hA).eigenvalues j ∈ Set.Icc a c`.
   **Note for A1:** `Matrix.IsHermitian.conjTranspose_mul_mul_same` does not exist in this
   Mathlib; the Hermitian proof of the compression is `Matrix.isHermitian_conjTranspose_mul_mul Q hA`
   (that name is for `PosSemidef`/`PosDef` only).
9. **I8.** `set_option backward.isDefEq.respectTransparency false` removed from Basic (none left).
10. Phase-1 files `Basic/LeadingMinor.lean`, `Basic/PlaneRotation.lean` untouched.

## Renames

See `docs/renames/2026-10-F4-M2-B.json`. Downstream call sites (wave 2):
`LowRank/PolynomialMethods/ComplexPolynomialFilterBounds` (import of `ComplexFullRowInverse`),
`LowRank/Cholesky/ComplexRandomPivotedCholesky`, `LowRank/Cholesky/ComplexCholeskyHistories`
(`re_trace_*_of_complex_posSemidef`). M1: `Spectral/SylvesterCriterion.lean:66,167` use
`isSymm_pivotSchur (Matrix.isHermitian_iff_isSymm.mp hA)` → `isHermitian_pivotSchur hA`.

## Scaffolds

None.

## Requests

- **M1**: the `isHermitian_pivotSchur` call sites above.
- **A1**: the helper exists (item 8); drop the real copy in `GaussQuadrature.lean`.
- **A2 (wave 2)**: the LowRank call sites above.

## Not done

Nothing in scope. (`Projections.lean:398` errors seen during the Basic build are in
`Matrix/Subspaces`, fork M2-S's file.)

## Residual lint hits

`check_norms.py NLAlib/Matrix/Basic`: 8 "`‖·‖` on a matrix in a signature" hits, all false
positives on vector or scalar norms: `LeastSquares.lean:83,217,299,364,394` and
`PlaneRotation.lean:39,48` are `‖(WithLp.toLp 2 v : EuclideanSpace ℝ _)‖` (the N2 spelling);
`CauchyBinetAdjoint.lean:86` is `‖(…).det‖` (a complex scalar). `check_docstrings.py`: 0.
