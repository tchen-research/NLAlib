# F1c: transpose twins removed from `Spectral/SVD.lean`

Date: 2026-10-13. Status: done. `lake build NLAlib.Matrix.Spectral.SVD`, then
`lake build NLAlib.Matrix NLAlib.LowRank NLAlib.Krylov NLAlib.Sketching` (one invocation):
green (4886 jobs). `scripts/check_names.py`: OK; `scripts/check_layers.py`: OK.
No new theorems; every leaf statement unchanged.

## 1. What was removed from `Matrix/Spectral/SVD.lean`

Rule (STANDARDS §2, "transpose twins"): one statement with `ᴴ`; the general lemma keeps or takes
the plain name; a `@[deprecated (since := "2026-10-13")] alias` only for a removed name still
used in term position outside the core.

| removed real (`ᵀ`) form | general lemma | alias kept? |
|---|---|---|
| `IsSVD.transpose_mul_left` | `IsSVD.conjTranspose_mul_left` (field) | yes, 24 term uses |
| `IsSVD.transpose_mul_right` | `IsSVD.conjTranspose_mul_right` (field) | yes, 23 term uses |
| `IsSVD.mul_transpose_left` | `IsSVD.mul_conjTranspose_left` (field) | yes, 4 term uses |
| `IsSVD.mul_transpose_right` | `IsSVD.mul_conjTranspose_right` (field) | yes, 5 term uses |
| `IsSVD.transpose_mul_mul` | `IsSVD.conjTranspose_mul_mul` | yes, 1 term use (KyFanAttainment) |
| `IsSVD.transpose_eq` | `IsSVD.conjTranspose_eq` | yes, 2 term uses (SingularValueInvariance, SingularFrames) |
| `IsSVD.eq_mul_transpose` | `IsSVD.eq` (field) | no (all uses were `rw`/`conv`, repaired) |
| `IsSVD.transpose_mul_self` | `IsSVD.conjTranspose_mul_self` | no (all uses repaired) |
| `IsSVD.mul_transpose_self` | `IsSVD.mul_conjTranspose_self` | no |
| `IsSVD.transpose_mul` | `IsSVD.conjTranspose_mul` | no (0 uses) |
| `transpose_rectDiag_mul_rectDiag` | `conjTranspose_rectDiag_mul_rectDiag` | no (all `rw`) |
| `rectDiag_mul_transpose_rectDiag` | `rectDiag_mul_conjTranspose_rectDiag` | no (all `simp only`) |
| `rectDiag_eq_of` (real unfolding, `rfl`) | `unfold NLAlib.rectDiag` | no (0 uses) |

Real names that did not mention `transpose` were taken by the general lemma (the old general
name is removed; none had uses outside SVD.lean/EckartYoung):

| old general name | new name (= old real name, now general) |
|---|---|
| `IsSVD.apply_eq_sum_mul_star` | `IsSVD.apply` |
| `IsSVD.eq_head_add_tail_mul_conjTranspose` | `IsSVD.eq_head_add_tail` |
| `singularValues_eq_of_eq_mul_rectDiag_mul_conjTranspose` | `singularValues_eq_of_eq_mul_rectDiag_mul` |

`transpose_mul_self_of_orthonormalBasis` was already deleted by F1b-α. All 16 entries are in
`docs/renames/2026-10-F1.json` (re-read before writing; additive only). The two stale atlas
formalizations (`…eq_head_add_tail_mul_conjTranspose`, `…_mul_conjTranspose`) were removed from
`atlas/atlas.json` by hand; `check_atlas.py` reports them as an out-of-sync *addition* only
because `atlas/declarations.json` is stale: regenerate it (`lake env lean
scripts/ExtractDecls.lean`, needs the full build) before running `sync_atlas.py`.

## 2. `rectDiag_apply` (real, cast-free): kept

`rectDiag_apply_ofReal` exists. At `ℝ`, full `simp [rectDiag_apply_ofReal]` closes the cast-free
form by itself (Mathlib's `@[simp] RCLike.ofReal_real_eq_id`), but `simp only
[rectDiag_apply_ofReal]` and `rw` leave `↑(σ i)` (an `RCLike.ofReal` cast at `ℝ`), which blocks the
following `split_ifs`/`ring`/`rw` steps (tested, `/tmp/f1c/T.lean`). `rectDiag_apply` is used
39 times in 17 files, almost all in `simp only`/`rw`; removing it would need
`simp only [rectDiag_apply_ofReal, RCLike.ofReal_real_eq_id, id]` at every site. So `simp only`
needs it at `ℝ`, and it stays (it is a cast-free specialisation, not a `ᵀ` twin). The module
docstring says so.

## 3. Call-site repairs (statements unchanged)

Recipes used: `show Vᵀ * V = 1 from h.conjTranspose_mul_right` (and the analogous full real
statement for the Gram identities, e.g. `show Aᵀ * A = V * Matrix.diagonal (fun j : Fin n =>
singularValues A j ^ 2) * Vᵀ from h.conjTranspose_mul_self`) in `rw`/`simp only` lists;
`conv_lhs => rw [h.eq, Matrix.conjTranspose_eq_transpose_of_trivial]` for the old
`rw [h.eq_mul_transpose]`; named arguments where the consumer takes `Pᵀ * P = 1` with `P` implicit
(`specNorm_mul_left_of_hasOrthonormalCols (P := V) h.conjTranspose_mul_right`) or where
`rfl` would fix `A` with `Vᴴ` (`singularValues_eq_of_eq_mul_rectDiag_mul (A := U * … * Vᵀ)`).

* Core: `Spectral/EckartYoung` (2× `eq_head_add_tail_mul_conjTranspose` → `eq_head_add_tail`).
* Matrix/Spectral: SvdPowers, SpectralBounds, RealDilation, SquareSingularBasis, SvdBlocks,
  ProductSingularValues.
* Matrix/Subspaces: ObliqueProjectionCanonical, InverseOverlapGram, ProjectionGaps,
  ObliqueCanonicalSpectrum.
* Matrix/Functions: DiagonalFilter, ComplexDiagonalFilter.
* Matrix/Inequalities: VonNeumann (`rw [h.apply]` now needs
  `simp only [RCLike.ofReal_real_eq_id, id_eq, star_trivial]` before `ring`).
* Matrix/Structured: KroneckerSingularValues.
* Matrix/Factorizations: NearestPolar (`hasOrthonormalCols_rectDiag_one` now rewrites with the
  general `conjTranspose_rectDiag_mul_rectDiag` directly; a `show` with the cast-free real form
  timed out in `whnf` under the file's `backward.isDefEq.respectTransparency false`),
  ProcrustesRotations.
* Matrix/Norms: SchattenSingularCoefficients, SchattenDuality.
* LowRank: RangeFinding/SpectralRangeFinder, Sampling/VolumeSampling.
* Krylov, Sketching: nothing needed.

The 59 remaining term-position uses (19 files) of the six kept aliases produce deprecation
warnings (as in R2's policy for the other F1 aliases).

## 4. `docs/llms.txt`

§"How to find a fact", item 3 rewritten to the STANDARDS §3 vocabulary (`[RCLike 𝕜]`,
`Matrix m n 𝕜` over `Fintype`s, `Fin` only as a sorted position, `ᴴ`-only lemmas with the `ᵀ`
recipe, `HasOrthonormalCols Q := Qᴴ * Q = 1`, `residual`, `quadForm`/`rayleighQuotient`,
`moorePenroseInverse`/`pinvL`/`pinvR`, `singularValues`, `IsSVD` with E′ shapes, `eigenvalues₀`,
Loewner `≤`). Item 2's import example fixed to `NLAlib.Matrix.Spectral.SVD`.

## 5. Notes for the coordinator

* Concurrency: F2a's full `lake build NLAlib` (log `/tmp/f2a/build2.log`) started after my
  SVD.lean edit and rebuilt SVD with it, so its failures in SvdPowers, SpectralBounds,
  RealDilation and ObliqueProjectionCanonical were mine, not F2a's; all are repaired now.
* F2a's files (`Matrix/Structured/Measurable`, `Matrix/Subspaces/Stiefel`,
  `Probability/Concentration/Basic/MatrixStatistics`, the new ForMathlib file) use none of the
  removed names; no repair was needed there and none was made.
* No consumer outside Matrix/LowRank/Krylov/Sketching mentions `IsSVD`, `rectDiag` or the
  uniqueness lemma, so Probability/RandomMatrix/Estimation are unaffected by this change.
