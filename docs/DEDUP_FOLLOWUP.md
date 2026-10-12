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
