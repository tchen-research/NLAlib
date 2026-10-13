# RCLike round, stage A-2, agent α: `Matrix/Subspaces/Projections`

Date: 2026-10-13. File: `NLAlib/Matrix/Subspaces/Projections.lean` (486 → 692 lines; the extra
lines are the D1 real corollaries, so the file drops back to about 500 when they are retired).
`lake build NLAlib.Matrix.Subspaces.Projections` succeeds with no warnings, and
`scripts/check_names.py` passes. Imports are unchanged: `Mathlib.LinearAlgebra.Matrix.Rank`,
`Mathlib.LinearAlgebra.Matrix.Hermitian` and `NLAlib.Matrix.Norms.Core`. No other file was edited.

## Definitions (over `{𝕜 : Type*} [RCLike 𝕜]`)

| def | body | at ℝ |
|---|---|---|
| `HasOrthonormalCols Q` | `Qᴴ * Q = 1` | definitionally `Qᵀ * Q = 1` |
| `residual Q A` | `A - Q * (Qᴴ * A)` | `rfl` to the old body |
| `IsBestRankApprox k C Y` | unchanged body (`rank`, `frobSq`), now over 𝕜 | same |

The atlas tags `orthonormal-columns-def`, `residual-def` and `best-rank-approx-def` stay on the
definitions. Their docstrings now say `ᴴ`; the atlas text is D13 (coordinator).

## Bridges

* 𝕜: `HasOrthonormalCols.conjTranspose_mul_self : Qᴴ * Q = 1` and
  `hasOrthonormalCols_iff_conjTranspose_mul_self` (`Iff.rfl`).
* ℝ: `HasOrthonormalCols.transpose_mul_self : Qᵀ * Q = 1`,
  `hasOrthonormalCols_iff_transpose_mul_self` (`Iff.rfl`), and
  `residual_eq_sub_mul_transpose_mul : residual Q A = A - Q * (Qᵀ * A)` (`rfl`).

## Generalised in place (same name; statement has no `ᵀ`, or `ᵀ` only in a hypothesis)

`frobInner_mul_residual`, `residual_residual`, `residual_mul_self`, `residual_mul`,
`frobSq_frame_eq_card`, `frobSq_residual_le`, `frobSq_residual_le_frobSq_sub_mul`,
`frobSq_residual_le_of_eq_mul`, `card_le_card_of_hasOrthonormalCols`, and
`isSymm_transpose_mul_mul` (over 𝕜 with its statement unchanged; it is true over any ring).

Four of these had a `ᵀ` that is now `ᴴ`:

* In a hypothesis: `residual_mul_eq_zero_of_range` (`h : Q * (Qᴴ * (A * Ω)) = A * Ω`) and
  `frobSq_sub_mul_le_of_isBestRankApprox` (`hY : IsBestRankApprox k (Qᴴ * A) Y`). Real callers
  can still pass the `ᵀ` form. This was checked in a scratch file, and is the pattern
  `RangeFinder` l.156 uses.
* In the conclusion, with no downstream users: `frobSq_eq_frobSq_proj_add_residual` and
  `frobSq_proj_le` (`Q * (Qᴴ * A)`).

## New general lemmas (𝕜, `conjTranspose`/`star` names)

`star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`,
`mul_conjTranspose_mul_mul_conjTranspose`, `one_sub_mul_conjTranspose_idem`,
`conjTranspose_mul_one_sub_mul_conjTranspose`, `one_sub_mul_conjTranspose_conjTranspose_mul`,
`residual_eq_one_sub_mul_conjTranspose_mul`, `mul_conjTranspose_mul_add_residual`,
`conjTranspose_mul_residual`, `frobSq_eq_frobSq_conjTranspose_mul_add_residual`,
`frobSq_residual_eq_frobSq_sub_frobSq_conjTranspose_mul`, `frobSq_conjTranspose_mul_le`,
`frobSq_sub_mul_eq_frobSq_residual_add_frobSq_conjTranspose_mul_sub`,
`conjTranspose_mul_eq_zero_comm`, `gram_conjTranspose_mul_eq`,
`conjTranspose_mul_eq_zero_of_completion`, `residual_eq_mul_conjTranspose_mul_residual`,
`exists_unitary_completion` (`VᴴV = I` extends to `WᴴW = I`, proved over `EuclideanSpace 𝕜`),
`exists_unitary_complement`, `mulVec_conjTranspose_mulVec_of_mem_range`,
`sum_norm_sq_conjTranspose_mulVec_le` (Bessel `∑ ‖(Qᴴx)ᵢ‖² ≤ ∑ ‖xᵢ‖²`, through
`specNorm_le_one_of_conjTranspose_mul_self`), `star_conjTranspose_mulVec_dotProduct_self_of_mem_range`,
`mul_conjTranspose_mul_eq_of_range_le`, `mul_conjTranspose_eq_of_range_eq`.

Mathlib already has the general forms of two real lemmas, so they get no NLAlib general version:
`mul_transpose_symm` corresponds to `Matrix.isHermitian_mul_conjTranspose_self`, and
`isHermitian_transpose_mul_mul` to `Matrix.isHermitian_conjTranspose_mul_mul`. The latter now proves
the real lemma.

Atlas: the tags `projection-facts` and `orthonormal-completion` stay on the real corollaries. The
general versions of the tagged results carry the same ids: `conjTranspose_mul_residual`,
`frobSq_sub_mul_eq_frobSq_residual_add_frobSq_conjTranspose_mul_sub`, `exists_unitary_completion`
and `exists_unitary_complement`.

## Kept real under the current names (D1)

Each is a term-mode application of the general lemma, which is definitional at ℝ. The exception is
`transpose_mulVec_dotProduct_self_le`, which is `simpa [dotProduct, sq]` from the norm-sum form.

`mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`, `mul_transpose_symm`,
`mul_transpose_mul_mul_transpose`, `one_sub_mul_transpose_idem`,
`transpose_mul_one_sub_mul_transpose`, `one_sub_mul_transpose_transpose_mul`,
`residual_eq_one_sub_mul`, `mul_transpose_mul_add_residual`, `transpose_mul_residual`,
`frobSq_eq_frobSq_transpose_mul_add_residual`, `frobSq_residual_eq_sub`,
`frobSq_transpose_mul_le`, `frobSq_sub_mul_eq`, `transpose_mul_eq_zero_comm`,
`gram_transpose_mul_eq`, `transpose_mul_eq_zero_of_completion`,
`residual_eq_mul_transpose_mul_residual`, `exists_orthogonal_completion`,
`exists_orthonormal_complement`, `mulVec_transpose_mulVec_of_mem_range`,
`isHermitian_transpose_mul_mul`, `transpose_mulVec_dotProduct_self_le`,
`transpose_mulVec_dotProduct_self_of_mem_range`, `mul_transpose_mul_eq_of_range_le`,
`mul_transpose_eq_of_range_eq`.

Two of these have no downstream callers and are kept only for uniformity:
`transpose_mul_one_sub_mul_transpose` and `one_sub_mul_transpose_transpose_mul`. Retire them in the
D1 cleanup.

The following were checked in a scratch file (`lake env lean`) at ℝ:
* passing `hY : IsBestRankApprox k (Qᵀ * A) Y` and `h : Q * (Qᵀ * (A * Ω)) = A * Ω`;
* `rw [hQ.transpose_mul_self]` and `rw [residual_eq_sub_mul_transpose_mul]`;
* `obtain ⟨W, hW, -⟩ := exists_orthogonal_completion …` followed by `rw [hW]` on a `Wᵀ * W` goal;
* `frobSq_frame_eq_card` at `ℂ`.

## Probe (direct importers of Projections; nothing edited)

Projections has 27 direct importers. I built the 13 whose import closure contains neither
`Basic/Pseudoinverse` nor `Spectral/SVD` (both are being edited concurrently) nor an A-1 breakage.
Each was built separately with `lake build NLAlib.<module>`.

| module | result | first error / note |
|---|---|---|
| Matrix.Subspaces.OrthogonalProducts | ✖ | l.30, 49, 61: `rw [hP]`/`rw [hQ]`/`rw [hU]` after `change (…)ᵀ * … = 1` (`rw [hQ]` pattern; predicted) |
| Matrix.Subspaces.OrthonormalBasisMatrix | ✔ | |
| Matrix.Subspaces.FrameContractions | ✖ | l.58 `rw [frobNorm, frobSq, frobInner_eq_trace, hQ, …]` (`rw [hQ]`; predicted) |
| Matrix.Subspaces.GraphTangent | ✖ | l.40, 44: `rw [… hU₁, hU …]` on `U₁ᵀ * U₁` (`rw [hQ]`; predicted) |
| Krylov.Spaces.Block | ✔ | predicted `rw [hQ]`, but it builds (false positive) |
| Krylov.Processes.Arnoldi | not built | blocked by OrthogonalProducts |
| Matrix.Subspaces.Stiefel | ✖ | l.78: `congrArg (fun M => M j j) hQ` then `simpa only [Matrix.transpose_apply, …]` leaves `(Matrix.of Q)ᴴ j j₁`. **Not predicted** (a "HasOrthonormalCols unfold" via `congrArg`). Fix: `congrArg … hQ.transpose_mul_self` |
| Matrix.Spectral.RealSpectrumSchur | ✖ | l.86 `rw [… ← Matrix.mul_assoc Qᵀ Q, hQ, …]` (`rw [hQ]`; predicted as "HasOrthonormalCols") |
| Matrix.Spectral.OrderedSymmetricDiagonalization | ✔ | predicted "HasOrthonormalCols", but it builds (false positive) |
| Matrix.Inequalities.PlaneRotation | ✔ | |
| Matrix.Subspaces.FrameFourthContractions | ✖ | l.26: `congrFun (congrFun hU a) b` then `simpa only [Matrix.mul_apply, Matrix.transpose_apply]`: same `congrFun`-on-`hQ` pattern as Stiefel. **Not predicted.** Fix: `congrFun (congrFun hU.transpose_mul_self a) b` |
| Sketching.Structured.SRHTFlattening | ✔ | |
| Matrix.Spectral.RealQZ | ✔ | predicted "HasOrthonormalCols", but it builds (false positive) |

Not probed because they import Pseudoinverse or SVD:
* GaussQuadrature, SketchedRegression, PowerIteration, RangeFinder, MoorePenroseProjector,
  MoorePenroseTransformations, QR, RectangularDiagonal, EigenspaceProjector, CourantFischer,
  EckartYoung, SingularValueInvariance, Structured.Measurable.
* `Subspaces/ProjectionGaps` imports Projections only transitively, and also imports SVD.
* `Norms/SpectralNormBounds` does not import Projections.

**Summary.** 13 modules built:
* 6 build;
* 6 fail, all with the same mechanical fix `hQ ↦ hQ.transpose_mul_self` (or
  `rw [hasOrthonormalCols_iff_transpose_mul_self] at hQ` once at the top of the proof);
* 1 (Arnoldi) is blocked by OrthogonalProducts.

Four of the six failures were predicted (`rw [hQ]`). Two are a pattern not in the breakage list:
`congrFun`/`congrArg` applied to `hQ`, followed by `simp only [transpose_apply]`. Stage B should
grep for `congrFun (congrFun hQ` and `congrArg … hQ` where `hQ : HasOrthonormalCols _`. The
predictor also has three false positives (Block, OrderedSymmetricDiagonalization, RealQZ). No
failure came from a changed lemma statement or a real corollary.
