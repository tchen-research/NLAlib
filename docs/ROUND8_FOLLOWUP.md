# Round 8 follow-up (housekeeping queue)

Collected from the K-A…K-D reports (2026-10-11). None of these blocks anything; they are the
"helpers where they belong" and open clauses to pick up in the next housekeeping round.

## Helpers to relocate
- `Matrix/PolynomialCalculus.lean` ← from `Krylov/GaussQuadrature.lean`: `mul_dotProduct_le_dotProduct_mulVec_of_eigenvalues`,
  `dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues`, `eigenvalues_eq_dotProduct_mulVec`,
  `eigenvectorBasis_dotProduct_self`, `eigenvalues_transpose_mul_mul_mem_Icc` (keep names; Ritz,
  Preconditioned, Lanczos import them through GaussQuadrature today); ← from `Krylov/FunctionApprox.lean`:
  `cfc_eq_aeval_of_forall_eval_eq`, `cfc_eq_aeval_interpolate`, `dotProduct_cfc_mulVec_self_le`;
  ← from `Krylov/Ritz.lean`: `eigenvectorBasis_dotProduct_eigenvectorBasis`, `eigenvectorBasis_dotProduct_aeval_mulVec`.
- `Matrix/Projections.lean` ← `transpose_mul_mul_eq_of_range_le` (Block), `transpose_mul_mul_apply`,
  `transpose_mul_self_apply`, `mulVec_eq_sum_smul_col`, `HasOrthonormalCols.col_dotProduct_col`,
  `HasOrthonormalCols.linearIndependent_col` (Arnoldi), `col_mul_eq_mulVec_col` (Block).
- `Matrix/QuadForm.lean` ← `quadForm_transpose_mul_mul`, `quadForm_transpose_mul_self` (Preconditioned).
- `Matrix/` (new `InverseSqrt.lean` or `Spectral.lean`) ← `exists_isSymm_transpose_mul_mul_eq_one` (`P^{-1/2}`),
  `isUnit_of_transpose_mul_mul_eq_one`, `inv_eq_mul_transpose_of_transpose_mul_mul_eq_one` (Preconditioned).
- `Matrix/` (new `Tridiagonal.lean`) ← `jacobiMatrix`, `det_smul_one_sub_jacobiMatrix`, `inv_apply_zero_zero`,
  `submatrix_succ_jacobiMatrix` (JacobiFraction); proposed atlas id `jacobi-determinant-recurrence`.
- `Polynomial/Approximation.lean` ← `exists_degree_le_eval_eq_one_abs_eval_le` (Ritz; a shifted amplifier,
  worth a named `chebyshevShiftedAmplifier a c L q`); `Polynomial/Chebyshev.lean` ← `pow_div_two_le_eval_T_real_one_add_two_mul`.
- `Krylov/Minimiser.lean` ← `isAffineMinimiser_map_iff` (Preconditioned); `Krylov/Grade.lean` ←
  `eq_zero_of_aeval_mulVec_eq_zero` (Jacobi); `Krylov/SpectralMeasure.lean` ← `integral_eval_mul_eval_spectralMeasure` (Jacobi).
- `Krylov/Ritz.lean`: `tanSqAngle` should become part of `principal-angles-def` when that lands.

## Open clauses (recorded in the atlas notes)
`residual-polynomial` ε_k(S) clauses · `krylov-polynomial-exactness` minimality of χ_H · `gmres-def`
Arnoldi least-squares form · `minres-bound` two-interval case (needs `two-interval-minimax`) ·
`gmres-diagonalizable` complex form · `jacobi-matrix-identities` strict interlacing, complex x ·
`chebyshev-iteration` three-term recurrence · `richardson-iteration` preconditioned form ·
`kaniel-paige-saad` i-th Ritz value · `krylov-grade` μ_{A,b} ∣ μ_A · implicit-Q theorem from a
Hessenberg hypothesis alone · `subspace-iteration-convergence` (needs principal angles).

## Statement conventions introduced this round (now the norm)
Squared tangents and squared norms; Krylov dimension `q+1` with `T_q` in Ritz bounds; enclosures
`[a, c]` of the non-top eigenvalues instead of `λ₂, λ_n`; singular-value hypotheses in Rayleigh form
`σ_lo² ‖v‖² ≤ ‖Av‖² ≤ σ_hi² ‖v‖²`; `0 < q` hypotheses in SLQ are now redundant and can be dropped.

## Labels to verify
Golub–Meurant numbers for Christoffel–Darboux, interlacing, Golub–Welsch, the charpoly
proportionality and the continued fraction (marked "label to verify" in the docstrings).
