# Round 9 follow-up (housekeeping queue and scaffold notes)

Collected from the D-A…D-E reports (2026-10-11). The scaffold queue itself is the atlas
Scaffold tab (every `SCAFFOLD:` declaration carries a proof sketch and a difficulty estimate).

## Scaffolds left by this round (difficulty in brackets)
- D-A: `posSemidef_fromBlocks_iff` (Albert) [3], `dotProduct_schurComplement_mulVec_le/_eq` [2],
  `choleskyPivoted_apply_self_pos_iff_lt_rank` [3], `choleskyPivoted_apply_eq_zero_of_rank_le` [2–3],
  `partialCholeskyFactor_mul_transpose_eq_nystrom` [3].
- D-B: `givensQRQ_invariant` [2] (its attempted proof was lost to an API failure; sketch in the
  docstring), one `gram-schmidt` scaffold, two `hessenberg-reduction` scaffolds (see the files; D-B's
  report never arrived, so read the `SCAFFOLD:` docstrings directly).
- D-C: sharp Wedin constants (`…_goldenRatio_…`) [4], projector difference bound
  `specNorm_mul_moorePenroseInverse_sub_le_of_rank_eq` [3], Gastinel–Kahan attainment [2], the
  four least-squares `ΔA` sensitivities (T&B 18.1 / Higham 20.1) [3].
- D-D: six principal-angle characterisations [2–3], `sq_tanThetaMax_replicateCol_eq_tanSqAngle` [2],
  `range_qrAlgorithmQ_castLE_eq_subspaceIterate` [2], `card_eigenvalues_lt_eq_card_sign_changes` [3],
  Golub–Kahan realisation and breakdown [3], entries of `B` [2].
- D-E: `dotProduct_cgRecurrence_r_eq_zero` and `dotProduct_cgRecurrence_p_mulVec_eq_zero` [3, joint
  induction], `lanczosRecurrence_eq_arnoldiBasis` [2–3].

## Helpers to relocate
- `Matrix/MoorePenrose.lean` ← D-C's `transpose_mul_mul_moorePenroseInverse`, `moorePenroseInverse_eq_nonsing_inv`,
  `moorePenroseInverse_smul`, `moorePenroseInverse_mul_of_hasOrthonormalCols`, `IsMoorePenroseInverse.*` complement lemmas.
- `Matrix/Norms.lean` / `Spectral.lean` ← `one_le_specNorm_of_isIdempotentElem`, `sqrt_dotProduct_self_pos`,
  `sqrt_dotProduct_sub_le` (D-C); `specNorm_mul_of_transpose_mul_self_eq_one`, `specNorm_diagonal_le` (D-D).
- `Matrix/RankNorm.lean` / `Pseudoinverse.lean` ← `rank_eq_card_iff_forall_mulVec_eq_zero`, `isUnit_transpose_mul_self_of_rank_eq`.
- `Matrix/Projections.lean` ← `residual_eq_of_range_eq`, `exists_eq_mul_of_range_le`, `transpose_mul_mul_apply_eq_dotProduct` (D-D).
- `Matrix/QuadForm.lean` ← `rayleighQuotient` (D-D).
- `Matrix/PolynomialCalculus.lean` ← `eigenvectorBasis_dotProduct_sub_smul_mulVec`, `eigenvectorBasis_dotProduct_inv_sub_mulVec`,
  `dotProduct_pow_mulVec_eq`, `sub_smul_one_eq_transpose_mul_diagonal_mul`, `isUnit_transpose_eigenvectorUnitary` (D-D).
- `Matrix/SchurComplement.lean` (layer 0) ← `selectionMatrix` and lemmas, `choleskyStep`, `posSemidef_choleskyStep`
  (currently in `LowRank/PartialCholesky.lean`); `borderedMatrix` could become `Matrix/Bordered.lean`.
- `ForMathlib` ← `absArgmax`, `apply_eq_zero_of_posSemidef_of_apply_self_eq_zero(')`, `isHermitian_of_isSymm`,
  `isSymm_of_isHermitian`; the private span facts in `CGRecurrence.lean`.
- `Krylov/ArnoldiProcess.lean` ← `arnoldiBasis_dotProduct_of_ne`, `arnoldiBasis_eq_zero_of_krylovGrade_le` (D-E).
- `Krylov/Polynomial.lean` ← the intertwining lemmas and `krylovSpace_mulVec_le_succ` (D-D).
- `tanSqAngle` and its lemmas (Ritz, PowerMethod) → `Matrix/PrincipalAngles.lean` once the bridge scaffold is proved.
- `Matrix/Conditioning.lean` is 587 lines: split the least-squares perturbation section out.
- `Matrix/Factorizations/LU.lean` is 572 lines: consider moving partial pivoting to its own file.

## Statement conventions introduced this round
`Matrix.IsUpperTriangular`/`IsLowerTriangular` from Mathlib (no NLAlib duplicates); existence
theorems for LU/Cholesky on `Fin n`, uniqueness for any linear order (general-index transport via
`Fintype.orderIsoFinOfCardEq` not done); `LUSucceeds` = all `n` pivots nonzero (GVL's minimal
`n−1` minors form is a separate theorem); `backSubst` = forward substitution on the reversed index;
partial pivoting ties go to the smallest index and need no invertibility for the realisation; the
QR algorithm is parametrised by a QR routine and a shift sequence; subspace-iteration convergence
takes an invariant orthogonal splitting instead of ordered eigenvalues; first-order sensitivities
are stated as `∀ ε > 0, ∃ δ > 0, …`.

## Atlas notes
- `Matrix.PosDef.fromBlocks₁₁` does not exist in the pinned Mathlib (only the PSD form); the PD pivot
  criterion is `posDef_iff_pivotSchur` in `Matrix/SchurComplement.lean`.
- Mathlib has the uniqueness half of Sylvester's law (`QuadraticMap.Equivalent.sigPos_eq`).
- Proposed but not yet added: `sturm-sequence-count` (if split from `sylvester-inertia`), an
  `IsFOMIterate` predicate for `fom-def`.
