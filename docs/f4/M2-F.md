# F4 wave 1: fork M2-F report (`Matrix/Functions`, `Matrix/OperatorTheory`)

Status: IN PROGRESS. Early notes for the other owners first; the full report is at the end.

## Names published early (for fork M2-S and agent P)

- `Functions/ComplexDiagonalFilter.lean` is deleted; `Functions/DiagonalFilter.lean` is over
  `[RCLike 𝕜]` with `specNorm_rectDiag_le` (`specNorm (rectDiag s : Matrix (Fin m) (Fin n) 𝕜) ≤ b`),
  `rectDiag_mul_aeval_gram` (`Σ * aeval (Σᴴ * Σ) p = rectDiag (s i * p.eval (s i ^ 2))`),
  `aeval_gram_diagonal_mul_diagonal_inv_eq_one`, `specNorm_diagonal_inv_le` (the former `let`–`∧`
  bundle `diagonal_filter_right_inverse_and_specNorm_le` split in two), and the helper
  `aeval_diagonal_ofReal`. The complexification helpers of the ℂ file are gone: use Mathlib,
  `map_ofReal_mul A B` → `Matrix.map_mul (f := Complex.ofRealHom)` (or `RCLike.ofRealHom`),
  `conjTranspose_map_ofReal A` → `by ext; simp` (`Matrix.conjTranspose_map` + `Complex.conj_ofReal`),
  `aeval_map_ofReal A p` → `(Polynomial.aeval_algHom_apply Complex.ofRealAm.mapMatrix A p).symm`.
  The merged statements take `rectDiag s : Matrix (Fin m) (Fin n) 𝕜` directly (no `map ofReal`).
- `eigenProj A hA i` → `eigenvectorProjector hA i` over 𝕜 (`Functions/HermitianCalculus.lean`);
  `cfc_eq_sum_smul_eigenProj A hA f` → `cfc_eq_sum_smul_eigenvectorProjector hA f`.
  (P call site: `Probability/Concentration/Basic/MatrixCalculus.lean:75-81`.)
- `norm_conjTranspose_mul_mul_le (hE : HasOrthonormalCols E) M` (was `(hE : Eᴴ * E = 1)`).
- `relativeEntropy (A H : Matrix d d 𝕜) : ℝ := RCLike.re (…)`; over ℂ rewrite with
  `relativeEntropy_complex` (rfl) to get the `Complex.re` form, as with `traceExp_complex`.
- `OperatorConvexOn I f` no longer takes `NeZero d`: `hf.2 d A H hA hH hAI hHI t ht₀ ht₁`.
- `lambdaMax`/`lambdaMin` are now M1's (`Matrix/Spectral/Core.lean`, over 𝕜); `ExpLog.lean`
  imports `Spectral.Core` and no longer defines them (S2 done).
