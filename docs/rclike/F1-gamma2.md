# F1-γ2: transpose twins removed from Projections, QuadForm, Pseudoinverse, PenroseIdentities, MoorePenrose*

Date: 2026-10-13. Files: `NLAlib/Matrix/Subspaces/Projections.lean`,
`NLAlib/Matrix/Basic/{QuadForm, Pseudoinverse, PenroseIdentities, MoorePenrose, MoorePenroseProjector,
MoorePenroseRank, MoorePenroseTransformations}.lean`. No other Lean file was edited.

`lake build NLAlib.Matrix.Subspaces.Projections NLAlib.Matrix.Basic.QuadForm
NLAlib.Matrix.Basic.PenroseIdentities NLAlib.Matrix.Basic.Pseudoinverse NLAlib.Matrix.Basic.MoorePenrose
NLAlib.Matrix.Basic.MoorePenroseTransformations NLAlib.Matrix.Basic.MoorePenroseProjector
NLAlib.Matrix.Basic.MoorePenroseRank` completes with no warnings. It was built against F1-γ1's
`Norms/{Core,Frobenius}` and `Spectral/Core` as they stood at about 11:20, while γ1 was still editing.
Renames are in `docs/renames/2026-10-F1.json`, which is shared with γ1. I re-read the file before
merging, and 81 of its entries are mine.

## Conventions used

* **The general lemma takes the plain name.** When the real twin had a name without `transpose`
  (`residual_eq_one_sub_mul`, `frobSq_residual_eq_sub`, `frobSq_sub_mul_eq`, `quadForm_eq_sum`,
  `pinvL_mul`, `moorePenroseInverse_eq_pinvL`, …), the `ᴴ`/`star` statement now has that name and the
  long general name is gone. When the real name said `transpose`, the `conjTranspose` name stays.
  `RCLike.re` in a statement does not change the name. This matches γ1, whose `frobInner_eq_trace` is
  the `re` statement. So `frobSq_pinvR_eq_trace_inv`, `frobSq_pinvL_eq_trace_inv` and
  `frobSq_moorePenroseInverse_eq_trace_moorePenroseInverse` are now the `re` statements.
* **Aliases.** A `@[deprecated (since := "2026-10-13")] alias old := general` was kept only when
  `old` is used outside the core and at least one of those uses is in term position (`exact`,
  `have … :=`, an argument, `obtain`), where the general statement unifies by definitional unfolding at ℝ.
  Uses inside `rw`/`simp` do not unify, because `ᴴ` is not `ᵀ` syntactically. No alias was kept
  for names whose outside uses are all `rw`/`simp`. Each alias has a docstring.
* **Dot notation (brief §1).** Lemmas whose subject is a `Matrix.IsHermitian` / `PosSemidef` /
  `PosDef` hypothesis moved to the *root* namespaces `Matrix.IsHermitian.*`, `Matrix.PosSemidef.*`
  and `Matrix.PosDef.*`, declared with `_root_.` inside `namespace NLAlib`. A scratch test showed that
  `NLAlib.Matrix.IsHermitian.foo` is not found by `hA.foo`. γ1's change to
  `scripts/ExtractDecls.lean` also collects root-namespace declarations made in `NLAlib` modules, so
  these appear in `atlas/declarations.json`. None of mine carries an `atlas:` tag. Inside such a
  lemma, `moorePenroseInverse` resolves to the lemma itself, so the statements say
  `NLAlib.moorePenroseInverse`.
* **Loewner order.** None of my files has a `(B - A).PosSemidef` hypothesis, so nothing changed.
* **`specNorm` decidability (following γ1).** Two arguments were dropped because `specNorm` no
  longer forces them: `[DecidableEq n]` from `specNorm_moorePenroseInverse_sq` and from
  `inv_specNorm_moorePenroseInverse_sq_mul_dotProduct_le`. Callers are unaffected.
* **Following γ1's renames in my proofs.** `frobInner_eq_re_trace` → `frobInner_eq_trace`,
  `frobSq_mul_left_of_conjTranspose_mul_self` → `frobSq_mul_left_of_orthonormal`,
  `specNorm_le_one_of_conjTranspose_mul_self` → `specNorm_le_one_of_orthonormal`.
  `MoorePenrose`'s RowProjector section still uses the real `sum_sq_mulVec_le_specNorm_sq`, which γ1
  had not removed at build time. If γ1 removes it, the two call sites (l.~340, l.~360) need
  `sum_norm_sq_mulVec_le_specNorm_sq` plus `simp [Real.norm_eq_abs, sq_abs]`.

## Bridges (item 3): all deleted

Every recipe below was checked at ℝ in a scratch file (`/tmp/g2/T.lean`). Each is the simp-lemma route the brief asks for.

| deleted `rfl` bridge | replacement at a use site |
|---|---|
| `quadForm_eq_dotProduct` | `rw [quadForm_def, star_trivial]` |
| `rayleighQuotient_eq_div` | `simp only [rayleighQuotient_def, star_trivial, RCLike.re_to_real]`. Alternatively `rw [rayleighQuotient_def, RCLike.re_to_real, RCLike.re_to_real, star_trivial]`; add `quadForm_def` to unfold the numerator too |
| `hasOrthonormalCols_iff_transpose_mul_self` | `rw [hasOrthonormalCols_iff_conjTranspose_mul_self, Matrix.conjTranspose_eq_transpose_of_trivial]` |
| `residual_eq_sub_mul_transpose_mul` | `rw [residual, Matrix.conjTranspose_eq_transpose_of_trivial]` (or both names in a `simp only` list) |
| `pinvL_eq_inv_transpose_mul_mul_transpose` | `rw [pinvL, Matrix.conjTranspose_eq_transpose_of_trivial]` |
| `pinvR_eq_transpose_mul_inv` | `rw [pinvR, Matrix.conjTranspose_eq_transpose_of_trivial]` |
| `HasOrthonormalCols.transpose_mul_self` (`rw [hQ.transpose_mul_self]` on `Qᵀ * Q`) | `rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hQ.conjTranspose_mul_self]`, or normalise the goal with `simp only [← Matrix.conjTranspose_eq_transpose_of_trivial]` first. Where it was passed to a real Norms lemma, pass `hQ` to γ1's general lemma |
| `isMoorePenroseInverse_iff_transpose` | `refine ⟨?_, ?_, ?_, ?_⟩`, then `rw [Matrix.conjTranspose_eq_transpose_of_trivial]` in fields 3 and 4 |

Also checked at ℝ: `conjTranspose_mul_eq_zero_comm.1 hU` with `hU : U₁ᵀ * U₂ = 0` against an ascribed
`U₂ᵀ * U₁ = 0`; `conjTranspose_mul_eq_zero_of_completion hQ hQp hcomp` with `ᵀ` hypotheses;
`(h : A.IsHermitian) : A.IsSymm` and the converse, by term. These are why the corresponding aliases
were kept.

## Statements changed under an unchanged name (no alias possible; call sites in `rw` may break)

| name | new statement (over `𝕜`) | real-site effect |
|---|---|---|
| `residual_eq_one_sub_mul` | `residual Q A = (1 - Q * Qᴴ) * A` | the rewritten goal shows `Qᴴ` |
| `frobSq_residual_eq_sub` | `… = frobSq A - frobSq (Qᴴ * A)` | `Qᴴ` |
| `frobSq_sub_mul_eq` | `… + frobSq (Qᴴ * A - B)` | `Qᴴ` |
| `quadForm_eq_sum`, `quadForm_eq_sum_mul_mul`, `quadForm_sq_eq_sum` | the `star (z i)` expansions | add `star_trivial` to the `simp_rw`/`simp only` |
| `pinvL_mul`, `mul_pinvR`, `mul_pinvL_mul`, `pinvL_mul_pinvL`, `mul_pinvR_mul`, `pinvR_mul_pinvR`, `mul_pinvL_isIdempotentElem`, `pinvR_mul_isIdempotentElem` | hypothesis `IsUnit (Gᴴ * G)` / `IsUnit (G * Gᴴ)` | a variable `G` is fine. A compound `G` fails inside `rw` (SketchedRegression l.90, l.137); fix with `pinvL_mul (G := Ψᵀ * Q) h` |
| `isMoorePenroseInverse_pinvL/R`, `moorePenroseInverse_eq_pinvL/R` | hypothesis `IsUnit (Aᴴ * A)` / `IsUnit (A * Aᴴ)` | `A` is explicit, so real callers still elaborate |
| `IsSVD.moorePenroseInverse_eq` | `A⁺ = V Σ⁺ Uᴴ` | `Uᴴ` (InverseOverlapGram) |
| `moorePenroseInverse_mul_left_of_hasOrthonormalCols` | `(Q A)⁺ = A⁺ Qᴴ` | `Qᴴ` (QRConsequences) |
| `frobSq_pinvR_eq_trace_inv`, `frobSq_pinvL_eq_trace_inv` | `= RCLike.re (…)⁻¹.trace` | `re` appears. Mean l.242 `rw …; rfl` may survive (not built: blocked). FrobeniusMoments l.121/222 need `RCLike.re_to_real` |
| `frobSq_moorePenroseInverse_eq_trace_moorePenroseInverse` | `= RCLike.re (A Aᴴ)⁺.trace` | no outside users |

## Removed / renamed names

"alias" = a deprecated alias was kept. "outside uses" = number of lines outside my files that use the
name (code and docstrings, from a word-boundary grep). The full map is in `docs/renames/2026-10-F1.json`.

| old name (`NLAlib.`) | replacement | alias | outside uses |
|---|---|---|---|
| `HasOrthonormalCols.transpose_mul_self` | `HasOrthonormalCols.conjTranspose_mul_self` | no | ~120 |
| `hasOrthonormalCols_iff_transpose_mul_self` | `hasOrthonormalCols_iff_conjTranspose_mul_self` | no | 14 |
| `residual_eq_sub_mul_transpose_mul` | `rw [NLAlib.residual, Matrix.conjTranspose_eq_transpose_of_trivial]` | no | 12 |
| `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` | `star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` | yes | 14 |
| `mul_transpose_symm` | `Matrix.isHermitian_mul_conjTranspose_self` | no | 2 |
| `mul_transpose_mul_mul_transpose` | `mul_conjTranspose_mul_mul_conjTranspose` | yes | 3 |
| `one_sub_mul_transpose_idem` | `one_sub_mul_conjTranspose_idem` | yes | 2 |
| `transpose_mul_one_sub_mul_transpose` | `conjTranspose_mul_one_sub_mul_conjTranspose` | no | 0 |
| `one_sub_mul_transpose_transpose_mul` | `one_sub_mul_conjTranspose_conjTranspose_mul` | no | 0 |
| `residual_eq_one_sub_mul_conjTranspose_mul` | `residual_eq_one_sub_mul` | no | 0 |
| `mul_transpose_mul_add_residual` | `mul_conjTranspose_mul_add_residual` | no | 1 |
| `transpose_mul_residual` | `conjTranspose_mul_residual` | no | 0 |
| `frobSq_eq_frobSq_transpose_mul_add_residual` | `frobSq_eq_frobSq_conjTranspose_mul_add_residual` | yes | 1 |
| `frobSq_residual_eq_frobSq_sub_frobSq_conjTranspose_mul` | `frobSq_residual_eq_sub` | no | 0 |
| `frobSq_transpose_mul_le` | `frobSq_conjTranspose_mul_le` | yes | 2 |
| `frobSq_sub_mul_eq_frobSq_residual_add_frobSq_conjTranspose_mul_sub` | `frobSq_sub_mul_eq` | no | 0 |
| `transpose_mul_eq_zero_comm` | `conjTranspose_mul_eq_zero_comm` | yes | 8 |
| `gram_transpose_mul_eq` | `gram_conjTranspose_mul_eq` | no | 1 |
| `transpose_mul_eq_zero_of_completion` | `conjTranspose_mul_eq_zero_of_completion` | yes | 1 |
| `residual_eq_mul_transpose_mul_residual` | `residual_eq_mul_conjTranspose_mul_residual` | yes | 3 |
| `exists_orthogonal_completion` | `exists_unitary_completion` | yes | 6 |
| `exists_orthonormal_complement` | `exists_unitary_complement` | yes | 1 |
| `mulVec_transpose_mulVec_of_mem_range` | `mulVec_conjTranspose_mulVec_of_mem_range` | yes | 9 |
| `isHermitian_transpose_mul_mul` | `Matrix.isHermitian_conjTranspose_mul_mul` | no | 12 |
| `transpose_mulVec_dotProduct_self_le` | `sum_norm_sq_conjTranspose_mulVec_le` | no | 3 |
| `transpose_mulVec_dotProduct_self_of_mem_range` | `star_conjTranspose_mulVec_dotProduct_self_of_mem_range` | no | 1 |
| `mul_transpose_mul_eq_of_range_le` | `mul_conjTranspose_mul_eq_of_range_le` | yes | 9 |
| `mul_transpose_eq_of_range_eq` | `mul_conjTranspose_eq_of_range_eq` | yes | 2 |
| `quadForm_eq_dotProduct` | `rw [NLAlib.quadForm_def, star_trivial]` | no | 33 |
| `rayleighQuotient_eq_div` | `simp only [NLAlib.rayleighQuotient_def, star_trivial, RCLike.re_to_real]` | no | 10 |
| `quadForm_eq_sum_star` | `quadForm_eq_sum` | no | 0 |
| `quadForm_eq_sum_star_mul_mul` | `quadForm_eq_sum_mul_mul` | no | 0 |
| `quadForm_sq_eq_sum_star` | `quadForm_sq_eq_sum` | no | 0 |
| `quadForm_smul_add_smul` | `Matrix.IsHermitian.re_quadForm_smul_add_smul` | no | 1 |
| `re_quadForm_smul_add_smul` | `Matrix.IsHermitian.re_quadForm_smul_add_smul` | no | 0 |
| `ofReal_re_quadForm` | `Matrix.IsHermitian.ofReal_re_quadForm` | no | 0 |
| `star_dotProduct_mulVec_comm_of_isHermitian` | `Matrix.IsHermitian.star_dotProduct_mulVec_comm` | no | 0 |
| `quadForm_vecMulVec_self` | `quadForm_vecMulVec_star_self` | no | 2 |
| `quadForm_transpose_mul_mul` | `quadForm_conjTranspose_mul_mul` | yes | 9 |
| `quadForm_transpose_mul_self` | `quadForm_conjTranspose_mul_self` | no | 6 |
| `quadForm_nonneg` | `Matrix.PosSemidef.quadForm_nonneg` | no | 0 |
| `quadForm_pos` | `Matrix.PosDef.quadForm_pos` | no | 0 |
| `re_quadForm_nonneg` | `Matrix.PosSemidef.re_quadForm_nonneg` | no | 0 |
| `pinvL_eq_inv_transpose_mul_mul_transpose` | `rw [NLAlib.pinvL, Matrix.conjTranspose_eq_transpose_of_trivial]` | no | 3 |
| `pinvR_eq_transpose_mul_inv` | `rw [NLAlib.pinvR, Matrix.conjTranspose_eq_transpose_of_trivial]` | no | 2 |
| `pinvL_mul_of_isUnit_conjTranspose_mul_self` | `pinvL_mul` | no | 0 |
| `mul_pinvR_of_isUnit_mul_conjTranspose_self` | `mul_pinvR` | no | 0 |
| `mul_pinvL_mul_of_isUnit_conjTranspose_mul_self` | `mul_pinvL_mul` | no | 0 |
| `pinvL_mul_pinvL_of_isUnit_conjTranspose_mul_self` | `pinvL_mul_pinvL` | no | 0 |
| `mul_pinvR_mul_of_isUnit_mul_conjTranspose_self` | `mul_pinvR_mul` | no | 0 |
| `pinvR_mul_pinvR_of_isUnit_mul_conjTranspose_self` | `pinvR_mul_pinvR` | no | 0 |
| `mul_pinvL_isIdempotentElem_of_isUnit_conjTranspose_mul_self` | `mul_pinvL_isIdempotentElem` | no | 0 |
| `pinvR_mul_isIdempotentElem_of_isUnit_mul_conjTranspose_self` | `pinvR_mul_isIdempotentElem` | no | 0 |
| `mul_pinvL_isSymm` | `mul_pinvL_isHermitian` | yes | 1 |
| `pinvR_mul_isSymm` | `pinvR_mul_isHermitian` | yes | 1 |
| `pinvL_mul_isSymm` | `pinvL_mul_isHermitian` | no | 0 |
| `mul_pinvR_isSymm` | `mul_pinvR_isHermitian` | no | 0 |
| `frobSq_pinvR_eq_re_trace_inv` | `frobSq_pinvR_eq_trace_inv` | no | 0 |
| `frobSq_pinvL_eq_re_trace_inv` | `frobSq_pinvL_eq_trace_inv` | no | 0 |
| `frobSq_pinvR` | `frobSq_pinvR_eq_trace_inv` | no | 0 |
| `frobSq_pinvL` | `frobSq_pinvL_eq_trace_inv` | no | 0 |
| `isMoorePenroseInverse_iff_transpose` | `NLAlib.IsMoorePenroseInverse.mk` | no | 2 |
| `IsMoorePenroseInverse.transpose_mul_eq` | `IsMoorePenroseInverse.conjTranspose_mul_eq` | no | 0 |
| `IsMoorePenroseInverse.transpose_inv_mul_eq` | `IsMoorePenroseInverse.conjTranspose_inv_mul_eq` | no | 4 |
| `IsMoorePenroseInverse.orthogonal_transform` | `IsMoorePenroseInverse.unitary_transform` | no | 0 |
| `IsMoorePenroseInverse.transpose_mul_self` | `IsMoorePenroseInverse.conjTranspose_mul_self` | no | 0 |
| `mul_moorePenroseInverse_isSymm` | `mul_moorePenroseInverse_isHermitian` | yes | 22 |
| `moorePenroseInverse_mul_isSymm` | `moorePenroseInverse_mul_isHermitian` | yes | 11 |
| `IsSVD.moorePenroseInverse_eq_mul_conjTranspose` | `IsSVD.moorePenroseInverse_eq` | yes | 2 |
| `isMoorePenroseInverse_pinvL_of_isUnit_conjTranspose_mul_self` | `isMoorePenroseInverse_pinvL` | no | 0 |
| `isMoorePenroseInverse_pinvR_of_isUnit_mul_conjTranspose_self` | `isMoorePenroseInverse_pinvR` | no | 0 |
| `moorePenroseInverse_eq_pinvL_of_isUnit_conjTranspose_mul_self` | `moorePenroseInverse_eq_pinvL` | no | 0 |
| `moorePenroseInverse_eq_pinvR_of_isUnit_mul_conjTranspose_self` | `moorePenroseInverse_eq_pinvR` | no | 0 |
| `moorePenroseInverse_transpose_mul_self` | `moorePenroseInverse_conjTranspose_mul_self` | no | 1 |
| `moorePenroseInverse_self_mul_transpose` | `moorePenroseInverse_self_mul_conjTranspose` | no | 0 |
| `frobSq_moorePenroseInverse_eq_re_trace_moorePenroseInverse` | `frobSq_moorePenroseInverse_eq_trace_moorePenroseInverse` | no | 0 |
| `mul_transpose_eq_mul_moorePenroseInverse` | `mul_conjTranspose_eq_mul_moorePenroseInverse` | yes | 2 |
| `moorePenroseInverse_isSymm` | `Matrix.IsHermitian.moorePenroseInverse` | yes | 1 |
| `moorePenroseInverse_isHermitian` | `Matrix.IsHermitian.moorePenroseInverse` | no | 0 |
| `moorePenroseInverse_mul_left_eq_mul_conjTranspose` | `moorePenroseInverse_mul_left_of_hasOrthonormalCols` | yes | 1 |
| `moorePenroseInverse_posSemidef` | `Matrix.PosSemidef.moorePenroseInverse` | yes | 3 |

## Kept on purpose

* **General statements that genuinely use `ᵀ`** (true over `ℂ`, not twins): `isSymm_transpose_mul_mul`,
  `pinvL_transpose`, `pinvR_transpose`, `moorePenroseInverse_transpose` and
  `IsMoorePenroseInverse.transpose`.
* **Real-only, not twins (no `ᴴ` counterpart exists).** The `RowProjector` section of
  `MoorePenrose` (`dotProduct_self_sub_moorePenroseInverse_mul_mulVec`,
  `dotProduct_moorePenroseInverse_mul_mulVec_le_dotProduct_self`,
  `inv_specNorm_moorePenroseInverse_sq_mul_dotProduct_le`, `inv_specNorm_pinvL_sq_mul_dotProduct_le`).
  These are Kaczmarz / sketch-and-project helpers. Generalising them would add new theorems beyond what
  F1 needs, so they are flagged for the port instead.
* `quadForm_def` and `rayleighQuotient_def` (general, `rfl`).

## Probe of the direct importers (nothing edited)

The probe covered 51 direct importers. My own modules and the `NLAlib.Matrix.Basic` / `NLAlib.Matrix.Subspaces` aggregators were excluded.
There was one `lake build` with all targets, plus a rebuild of `Spectral.Core` and `Krylov.Spaces.Block`,
which had not been reached. Some failures come from γ1's in-flight Norms changes; those are marked **γ1**.

**Build:** `Matrix.Inequalities.PlaneRotation`, `Matrix.Spectral.OrderedSymmetricDiagonalization`,
`Matrix.Spectral.RealQZ`, `Matrix.Subspaces.OrthonormalBasisMatrix`,
`Probability.Concentration.QuadraticForms.Geometry`, `RandomMatrix.Gaussian.Invariance.Invariance` (uses
the `exists_orthogonal_completion` alias), `Solvers.SketchAndProject.Core`, `Matrix.Spectral.Core`,
`Krylov.Spaces.Block`.

**Fail (first errors):**

| module | cause |
|---|---|
| Matrix.Basic.SingletonInverse | `isMoorePenroseInverse_iff_transpose` removed (l.17) |
| Matrix.Structured.KroneckerIdentities | `isMoorePenroseInverse_iff_transpose` removed (l.46); `transpose_inv_mul_eq` (l.55) |
| Matrix.Basic.GeneralizedSchurComplement | `(mul_moorePenroseInverse_isSymm A).eq` / `(moorePenroseInverse_mul_isSymm A).eq` inside `simpa`/`rw` now give `ᴴ` (l.73, l.78). Through the aliases, `moorePenroseInverse_isSymm` and `moorePenroseInverse_posSemidef` elaborate, with deprecation warnings |
| Matrix.Norms.Net | `quadForm_eq_dotProduct` removed (l.106, l.218) |
| Matrix.Subspaces.GramColumnDeterminant | **γ1**: `frobInner_eq_trace` now has `re` (l.39). Then `pinvL_eq_inv_transpose_mul_mul_transpose` removed (l.45) |
| Matrix.Subspaces.OrthogonalProducts | `hP/hQ/hU.transpose_mul_self` (l.30, l.49, l.61); `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` alias inside `rw` (l.86) |
| Matrix.Subspaces.Stiefel | `hQ.transpose_mul_self` (l.77); `hV`/`hW` from the `exists_orthogonal_completion` alias are `ᴴ` facts used in `rw` on `ᵀ` goals (l.181, l.185) |
| Matrix.Subspaces.FrameContractions | `hQ.transpose_mul_self` (l.58) |
| Matrix.Subspaces.FrameFourthContractions | `hU.transpose_mul_self` (l.25) |
| Matrix.Subspaces.GraphTangent | `.transpose_mul_self` (l.40, l.44); `mulVec_transpose_mulVec_of_mem_range` / `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` aliases inside `rw` (l.90, l.112, l.145); `transpose_mulVec_dotProduct_self_of_mem_range` removed (l.93); `simpa … using` alias (l.162) |
| Matrix.Spectral.RealSpectrumSchur | `hQ.transpose_mul_self` (l.86) |
| Matrix.Spectral.SingularValueInvariance | `hasOrthonormalCols_iff_transpose_mul_self` removed (l.70) |
| Matrix.Spectral.SpectralBounds (not a direct importer; it blocks many) | **γ1**: `mulVec_dotProduct_mulVec_self` removed (l.185, l.205, l.219) |
| Matrix.Structured.Measurable | `pinvL_eq_…`, `pinvR_eq_…`, `residual_eq_sub_mul_transpose_mul` removed (l.92, l.108, l.136, l.186) |
| Matrix.Factorizations.QR | `pinvL_eq_inv_transpose_mul_mul_transpose` removed (l.332); `hWW` from the `exists_orthogonal_completion` alias used in `rw` (l.396) |
| LowRank.Nystrom.SketchedRegression | `pinvL_mul hG₁` with compound `G` (l.90, l.137); the `residual_eq_mul_transpose_mul_residual` alias leaves `Qpᴴ` (l.114); `mul_transpose_mul_add_residual` and `residual_eq_sub_mul_transpose_mul` removed (l.124, l.148); `.transpose_mul_self` (l.162, l.171, l.202) |
| LowRank.Structural.RangeFinder | `hU₂.transpose_mul_self` (l.96) |
| Probability…QuadraticMoments | `simp_rw [quadForm_eq_sum]` / `[quadForm_sq_eq_sum]` now leave `star` (l.114, l.282): add `star_trivial` |
| Probability…CutAverages (not direct) | `simp only [quadForm_eq_sum_mul_mul]` leaves `star` (l.126, l.143, l.228) |
| Sketching…SubspaceEmbedding | the `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` alias inside `simp only` (l.45). **γ1**: `mulVec_dotProduct_mulVec_self` (l.103) |
| Sketching.Structured.SRHTFlattening | `hUnorm` from the `mulVec_dotProduct…` alias has `star` (l.75) |
| Solvers.Kaczmarz.Core (not direct) | **γ1**: `frobSq_eq_sum_dotProduct_self` removed (l.87) |

**Not built: blocked by a failing dependency.** Static prediction is in the next table.
* Blocked by SpectralBounds (γ1): Krylov.Quadrature.GaussQuadrature, LowRank.Structural.PowerIteration,
  Matrix.Functions.PolynomialCalculus, Matrix.Norms.RankNorm, Matrix.Norms.RectangularDiagonal,
  Matrix.Perturbation.{ConditionNumber, EigenspaceProjector, PseudoinverseProjectors},
  Matrix.Spectral.{CourantFischer, EckartYoung}, Matrix.Subspaces.InverseOverlapGram,
  Probability.Concentration.QuadraticForms.HansonWright, Sketching.Sampling.Leverage.
* Blocked by OrthogonalProducts: Krylov.Processes.Arnoldi, Matrix.Subspaces.GramIsometry,
  Matrix.Factorizations.PolarDecomposition (also Measurable).
* Blocked by SketchedRegression: LowRank.Nystrom.RawNystromBridge.
* Blocked by SubspaceEmbedding: Sketching.Sparse.Bands.{Heavy.PreservingBound,
  Light.HardCoreEmbedding, Light.SynthesisBounds, Light.ZeroBlock}.
* Blocked by Kaczmarz.Core (γ1): Solvers.Kaczmarz.{KaczmarzExtensions, KaczmarzProbability}.

Core files of other F1 agents that use my names: `Spectral/CourantFischer` (`quadForm_eq_dotProduct`
removed; `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` alias inside `exact`, which is fine);
`Spectral/Weyl` (`rw [residual_eq_one_sub_mul]`, statement now `ᴴ`); `Spectral/EckartYoung`
(`(mul_moorePenroseInverse_isSymm B).eq`, alias, term, fine).

## Static list of affected use sites (all of NLAlib, for the repair wave)

Columns:
* "removed": names removed with no alias. These break.
* "`.transpose_mul_self`": `hX.transpose_mul_self` on a `HasOrthonormalCols`. These break; uses on `IsSVD` were filtered out heuristically.
* "alias": a deprecated alias. These break only inside `rw`/`simp`.
* "changed": names whose statement changed. These break only where `ᵀ`/`star`-free shapes are rewritten afterwards.

| file | sites |
|---|---|
| Estimation/Spectral/RandomStartEndpoints.lean | removed: `quadForm_eq_dotProduct`, `rayleighQuotient_eq_div` |
| Estimation/Spectral/RandomStartLanczos.lean | removed: `quadForm_eq_dotProduct`, `rayleighQuotient_eq_div` |
| Estimation/Spectral/RandomStartPower.lean | removed: `quadForm_eq_dotProduct`, `rayleighQuotient_eq_div` |
| Estimation/Trace/HutchinsonTail.lean | changed: `quadForm_eq_sum`×2 |
| Estimation/Trace/Unbiased.lean | alias: `mul_transpose_mul_mul_transpose` |
| Krylov/MatrixFunctions/FunctionApprox.lean | removed: `isHermitian_transpose_mul_mul`×7, `transpose_mulVec_dotProduct_self_le`; alias: `mul_transpose_eq_of_range_eq`, `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| Krylov/Processes/Arnoldi.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self`; alias: `mulVec_transpose_mulVec_of_mem_range` |
| Krylov/Processes/ArnoldiProcess.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self` |
| Krylov/Processes/Bidiagonalization.lean | alias: `mul_transpose_mul_eq_of_range_le` |
| Krylov/Processes/Lanczos.lean | alias: `mulVec_transpose_mulVec_of_mem_range`×3 |
| Krylov/Quadrature/GaussQuadrature.lean | removed: `isHermitian_transpose_mul_mul`, `transpose_mulVec_dotProduct_self_le`; alias: `mulVec_transpose_mulVec_of_mem_range`×3, `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| Krylov/Quadrature/Jacobi.lean | removed: `isHermitian_transpose_mul_mul` |
| Krylov/Quadrature/JacobiFraction.lean | alias: `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| Krylov/Solvers/CG.lean | removed: `quadForm_eq_dotProduct` |
| Krylov/Solvers/GMRES.lean | removed: `quadForm_eq_dotProduct` |
| Krylov/Solvers/GMRESArnoldi.lean | alias: `mulVec_transpose_mulVec_of_mem_range`, `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| Krylov/Solvers/Preconditioned.lean | removed: `quadForm_transpose_mul_self`×4; alias: `quadForm_transpose_mul_mul`×2 |
| Krylov/Spectral/MeasurableRitz.lean | removed: `quadForm_eq_dotProduct`×3, `rayleighQuotient_eq_div`×3 |
| Krylov/Spectral/PowerMethod.lean | removed: `quadForm_eq_dotProduct`, `rayleighQuotient_eq_div`×2 |
| Krylov/Spectral/Ritz.lean | removed: `quadForm_eq_dotProduct`; alias: `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| LowRank/Nystrom/GaussianNystrom.lean | removed: `residual_eq_sub_mul_transpose_mul` |
| LowRank/Nystrom/RawGaussianNystrom.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self`; changed: `pinvL_mul` |
| LowRank/Nystrom/RawNystromBridge.lean | alias: `mul_pinvL_isSymm`, `pinvR_mul_isSymm`; changed: `pinvL_mul`, `mul_pinvR`×2 |
| LowRank/Nystrom/SketchedRegression.lean | removed: `mul_transpose_mul_add_residual`, `residual_eq_sub_mul_transpose_mul`; `.transpose_mul_self`×3; alias: `residual_eq_mul_transpose_mul_residual`×3; changed: `pinvL_mul`×2 |
| LowRank/Nystrom/Structural.lean | removed: `moorePenroseInverse_transpose_mul_self`; alias: `mul_moorePenroseInverse_isSymm`×3, `mul_transpose_eq_mul_moorePenroseInverse`; changed: `residual_eq_one_sub_mul` |
| LowRank/PolynomialMethods/PolynomialFilter.lean | removed: `residual_eq_sub_mul_transpose_mul`; `.transpose_mul_self`×11; alias: `transpose_mul_eq_zero_comm`×4, `mul_transpose_mul_eq_of_range_le` |
| LowRank/RandomizedSVD/GaussianSketch.lean | removed: `gram_transpose_mul_eq`; `.transpose_mul_self`×1; alias: `transpose_mul_eq_zero_of_completion`, `exists_orthonormal_complement` |
| LowRank/RandomizedSVD/OptimalError.lean | alias: `frobSq_transpose_mul_le`, `frobSq_eq_frobSq_transpose_mul_add_residual`; changed: `mul_pinvR`, `frobSq_sub_mul_eq`×3 |
| LowRank/RangeFinding/ExpectedPower.lean | removed: `residual_eq_sub_mul_transpose_mul` |
| LowRank/RangeFinding/SpectralRangeFinder.lean | removed: `residual_eq_sub_mul_transpose_mul`; `.transpose_mul_self`×6; alias: `transpose_mul_eq_zero_comm` |
| LowRank/Structural/PowerIteration.lean | removed: `mul_transpose_symm`; alias: `one_sub_mul_transpose_idem`; changed: `residual_eq_one_sub_mul` |
| LowRank/Structural/RangeFinder.lean | `.transpose_mul_self`×3; alias: `transpose_mul_eq_zero_comm`; changed: `mul_pinvR` |
| Matrix/Basic/GeneralizedSchurComplement.lean | alias: `moorePenroseInverse_isSymm`, `mul_moorePenroseInverse_isSymm`, `moorePenroseInverse_mul_isSymm`, `moorePenroseInverse_posSemidef`×3 |
| Matrix/Basic/LeastSquares.lean | alias: `mul_moorePenroseInverse_isSymm`, `moorePenroseInverse_mul_isSymm`, `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`; changed: `moorePenroseInverse_eq_pinvL` |
| Matrix/Basic/SingletonInverse.lean | removed: `isMoorePenroseInverse_iff_transpose` |
| Matrix/Factorizations/GramSchmidt.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self` |
| Matrix/Factorizations/MaximumVolumeQR.lean | `.transpose_mul_self`×2 |
| Matrix/Factorizations/MaximumVolumeTriangularQR.lean | `.transpose_mul_self`×1 |
| Matrix/Factorizations/NearestPolar.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self`×3; `.transpose_mul_self`×6 |
| Matrix/Factorizations/PolarDecomposition.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self`×2; `.transpose_mul_self`×6; alias: `mul_moorePenroseInverse_isSymm` |
| Matrix/Factorizations/Procrustes.lean | `.transpose_mul_self`×4 |
| Matrix/Factorizations/QR.lean | removed: `pinvL_eq_inv_transpose_mul_mul_transpose`; alias: `exists_orthogonal_completion`; changed: `moorePenroseInverse_eq_pinvL` |
| Matrix/Factorizations/QRConsequences.lean | changed: `moorePenroseInverse_mul_left_of_hasOrthonormalCols` |
| Matrix/Factorizations/ScaledOrthogonal.lean | `.transpose_mul_self`×1 |
| Matrix/Functions/PolynomialCalculus.lean | removed: `quadForm_eq_dotProduct`×2 |
| Matrix/Inequalities/BlockOrderConsequences.lean | removed: `quadForm_eq_dotProduct` |
| Matrix/Inequalities/BlockQuadratic.lean | removed: `quadForm_eq_dotProduct`×3 |
| Matrix/Inequalities/FiniteExponentialGram.lean | removed: `quadForm_vecMulVec_self`, `quadForm_eq_dotProduct` |
| Matrix/Inequalities/HadamardOrder.lean | removed: `quadForm_eq_dotProduct` |
| Matrix/Inequalities/KyFan.lean | removed: `isHermitian_transpose_mul_mul`×2; `.transpose_mul_self`×1 |
| Matrix/Inequalities/KyFanAttainment.lean | `.transpose_mul_self`×3 |
| Matrix/Inequalities/Schur.lean | `.transpose_mul_self`×1 |
| Matrix/Inequalities/SchurHorn.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self`; `.transpose_mul_self`×1 |
| Matrix/Inequalities/SchurHornProjection.lean | `.transpose_mul_self`×1 |
| Matrix/Inequalities/SeparatingPSDVector.lean | removed: `quadForm_vecMulVec_self` |
| Matrix/Inequalities/VonNeumann.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self`; alias: `mul_moorePenroseInverse_isSymm` |
| Matrix/Inequalities/Wielandt.lean | removed: `quadForm_smul_add_smul` |
| Matrix/Norms/Net.lean | removed: `quadForm_eq_dotProduct`×2 |
| Matrix/Norms/NuclearHermitian.lean | `.transpose_mul_self`×1 |
| Matrix/Norms/NuclearNorm.lean | `.transpose_mul_self`×1 |
| Matrix/Norms/RankNorm.lean | removed: `moorePenroseInverse_eq_mul_conjTranspose`×2 |
| Matrix/Norms/SchattenDuality.lean | `.transpose_mul_self`×4 |
| Matrix/Norms/SchattenInvariant.lean | `.transpose_mul_self`×1 |
| Matrix/Norms/SchattenSingularCoefficients.lean | `.transpose_mul_self`×3 |
| Matrix/Perturbation/ConditionNumber.lean | alias: `moorePenroseInverse_mul_left_eq_mul_conjTranspose` |
| Matrix/Perturbation/Conditioning.lean | alias: `mul_moorePenroseInverse_isSymm` |
| Matrix/Perturbation/DavisKahan.lean | removed: `isHermitian_transpose_mul_mul`; `.transpose_mul_self`×1 |
| Matrix/Perturbation/DavisKahanBounds.lean | changed: `residual_eq_one_sub_mul` |
| Matrix/Perturbation/EigenspaceProjector.lean | alias: `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| Matrix/Perturbation/EigenvaluePerturbation.lean | removed: `quadForm_eq_dotProduct`×2 |
| Matrix/Perturbation/EigenvalueTrace.lean | removed: `quadForm_eq_dotProduct` |
| Matrix/Perturbation/EigenvalueVariation.lean | removed: `quadForm_eq_dotProduct` |
| Matrix/Perturbation/LeastSquaresGeometry.lean | alias: `mul_moorePenroseInverse_isSymm`; changed: `moorePenroseInverse_eq_pinvL`, `pinvL_mul` |
| Matrix/Perturbation/PopulationTraceGap.lean | removed: `mul_transpose_symm` |
| Matrix/Perturbation/PseudoinverseBlocks.lean | removed: `transpose_inv_mul_eq` |
| Matrix/Perturbation/PseudoinverseDifference.lean | removed: `transpose_inv_mul_eq`×2 |
| Matrix/Perturbation/PseudoinverseFrobeniusPerturbation.lean | alias: `mul_moorePenroseInverse_isSymm`×4, `moorePenroseInverse_mul_isSymm`×4 |
| Matrix/Perturbation/PseudoinverseProjectors.lean | alias: `mul_moorePenroseInverse_isSymm`×2 |
| Matrix/Perturbation/PseudoinverseSpectralPerturbation.lean | alias: `mul_moorePenroseInverse_isSymm`×3, `moorePenroseInverse_mul_isSymm`×3 |
| Matrix/Perturbation/ResidualBounds.lean | removed: `quadForm_eq_dotProduct` |
| Matrix/Perturbation/SingularFrameTails.lean | removed: `residual_eq_sub_mul_transpose_mul`; `.transpose_mul_self`×1 |
| Matrix/Perturbation/SingularFrames.lean | removed: `residual_eq_sub_mul_transpose_mul`×2 |
| Matrix/Perturbation/SpectralFrameWeights.lean | removed: `transpose_mulVec_dotProduct_self_le`; `.transpose_mul_self`×1 |
| Matrix/Perturbation/WedinResidual.lean | removed: `residual_eq_sub_mul_transpose_mul`×2 |
| Matrix/Spectral/CourantFischer.lean | removed: `quadForm_eq_dotProduct`; alias: `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| Matrix/Spectral/EckartYoung.lean | alias: `mul_moorePenroseInverse_isSymm` |
| Matrix/Spectral/EigenframeDecomposition.lean | `.transpose_mul_self`×1 |
| Matrix/Spectral/Inertia.lean | removed: `quadForm_eq_dotProduct`×2 |
| Matrix/Spectral/InterlacingOrthogonalTransport.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self`; `.transpose_mul_self`×1 |
| Matrix/Spectral/OstrowskiCongruence.lean | alias: `quadForm_transpose_mul_mul`×4 |
| Matrix/Spectral/PowerRayleigh.lean | removed: `quadForm_eq_dotProduct`×2, `rayleighQuotient_eq_div`×2 |
| Matrix/Spectral/ProductSingularValues.lean | `.transpose_mul_self`×1 |
| Matrix/Spectral/RealNormalForm.lean | `.transpose_mul_self`×1 |
| Matrix/Spectral/RealNormalSpecializations.lean | `.transpose_mul_self`×4 |
| Matrix/Spectral/RealPlaneSchur.lean | `.transpose_mul_self`×1 |
| Matrix/Spectral/RealSpectrumSchur.lean | `.transpose_mul_self`×2 |
| Matrix/Spectral/SimultaneousOrthogonal.lean | `.transpose_mul_self`×2 |
| Matrix/Spectral/SingularValueInvariance.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self` |
| Matrix/Spectral/Weyl.lean | changed: `residual_eq_one_sub_mul` |
| Matrix/Structured/KroneckerIdentities.lean | removed: `isMoorePenroseInverse_iff_transpose`, `transpose_inv_mul_eq` |
| Matrix/Structured/Measurable.lean | removed: `pinvL_eq_inv_transpose_mul_mul_transpose`, `residual_eq_sub_mul_transpose_mul`, `pinvR_eq_transpose_mul_inv`×2 |
| Matrix/Structured/SpectralMeasurable.lean | removed: `residual_eq_sub_mul_transpose_mul` |
| Matrix/Subspaces/CSDecomposition.lean | `.transpose_mul_self`×2 |
| Matrix/Subspaces/CSRank.lean | `.transpose_mul_self`×2 |
| Matrix/Subspaces/CanonicalCS.lean | `.transpose_mul_self`×2 |
| Matrix/Subspaces/CanonicalQR.lean | removed: `hasOrthonormalCols_iff_transpose_mul_self` |
| Matrix/Subspaces/ComplexCSDecomposition.lean | `.transpose_mul_self`×2 |
| Matrix/Subspaces/ComplexObliqueSecant.lean | `.transpose_mul_self`×1 |
| Matrix/Subspaces/ComplexObliqueSpectrum.lean | `.transpose_mul_self`×1 |
| Matrix/Subspaces/FrameContractions.lean | `.transpose_mul_self`×1; alias: `frobSq_transpose_mul_le` |
| Matrix/Subspaces/FrameFourthContractions.lean | `.transpose_mul_self`×1 |
| Matrix/Subspaces/GramColumnDeterminant.lean | removed: `pinvL_eq_inv_transpose_mul_mul_transpose`; alias: `mul_moorePenroseInverse_isSymm`; changed: `moorePenroseInverse_eq_pinvL` |
| Matrix/Subspaces/GraphTangent.lean | removed: `transpose_mulVec_dotProduct_self_of_mem_range`; `.transpose_mul_self`×2; alias: `transpose_mul_eq_zero_comm`×2, `mulVec_transpose_mulVec_of_mem_range`, `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`×3 |
| Matrix/Subspaces/InverseOverlapGram.lean | changed: `moorePenroseInverse_eq` |
| Matrix/Subspaces/ObliqueFrameInverse.lean | alias: `mul_transpose_mul_eq_of_range_le`×2 |
| Matrix/Subspaces/ObliqueProjectionBlocks.lean | `.transpose_mul_self`×1; alias: `mul_transpose_mul_eq_of_range_le` |
| Matrix/Subspaces/ObliqueProjectionSecant.lean | `.transpose_mul_self`×2 |
| Matrix/Subspaces/OrthogonalBasisChange.lean | `.transpose_mul_self`×1 |
| Matrix/Subspaces/OrthogonalBlockCompletion.lean | `.transpose_mul_self`×1 |
| Matrix/Subspaces/OrthogonalProducts.lean | `.transpose_mul_self`×4; alias: `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| Matrix/Subspaces/PrincipalAngleDefinitions.lean | `.transpose_mul_self`×2; changed: `frobSq_residual_eq_sub`×2, `residual_eq_one_sub_mul` |
| Matrix/Subspaces/PrincipalAngleInvariance.lean | `.transpose_mul_self`×2; alias: `mul_transpose_mul_eq_of_range_le` |
| Matrix/Subspaces/PrincipalAngleTangent.lean | `.transpose_mul_self`×1 |
| Matrix/Subspaces/PrincipalAngles.lean | alias: `mul_transpose_eq_of_range_eq`, `mul_transpose_mul_eq_of_range_le`×2; changed: `residual_eq_one_sub_mul`×3, `frobSq_residual_eq_sub` |
| Matrix/Subspaces/ProjectionFrobeniusGaps.lean | `.transpose_mul_self`×2; changed: `frobSq_residual_eq_sub`, `residual_eq_one_sub_mul`×2 |
| Matrix/Subspaces/ProjectionGaps.lean | `.transpose_mul_self`×7; alias: `one_sub_mul_transpose_idem`, `mul_transpose_mul_mul_transpose`×2, `mul_transpose_mul_eq_of_range_le`; changed: `residual_eq_one_sub_mul`×5, `frobSq_residual_eq_sub` |
| Matrix/Subspaces/RectangularGramIsometry.lean | `.transpose_mul_self`×4 |
| Matrix/Subspaces/Stiefel.lean | `.transpose_mul_self`×1; alias: `exists_orthogonal_completion`×2 |
| Probability/Concentration/QuadraticForms/Centering.lean | changed: `quadForm_eq_sum_mul_mul`×4 |
| Probability/Concentration/QuadraticForms/CutAverages.lean | changed: `quadForm_eq_sum_mul_mul`×5 |
| Probability/Concentration/QuadraticForms/QuadraticMoments.lean | changed: `quadForm_eq_sum`×3, `quadForm_sq_eq_sum`×2 |
| Probability/Concentration/QuadraticForms/RademacherQuadraticMoments.lean | changed: `quadForm_eq_sum`×2 |
| RandomMatrix/Gaussian/Invariance/Invariance.lean | alias: `exists_orthogonal_completion`×2 |
| RandomMatrix/Gaussian/InverseMoments/FrobeniusMoments.lean | alias: `frobSq_pinvR_eq_trace_inv`×2 |
| RandomMatrix/Gaussian/InverseMoments/Mean.lean | alias: `frobSq_pinvR_eq_trace_inv` |
| RandomMatrix/Gaussian/InverseMoments/Probe.lean | alias: `exists_orthogonal_completion` |
| Sketching/Properties/SubspaceEmbedding/SubspaceEmbedding.lean | alias: `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| Sketching/Sampling/Leverage.lean | `.transpose_mul_self`×2; alias: `mul_moorePenroseInverse_isSymm`×2, `mul_transpose_eq_mul_moorePenroseInverse` |
| Sketching/Sparse/Bands/Heavy/PreservingBound.lean | removed: `quadForm_transpose_mul_self`; alias: `quadForm_transpose_mul_mul` |
| Sketching/Sparse/Bands/Light/HardCoreEmbedding.lean | alias: `quadForm_transpose_mul_mul`×2 |
| Sketching/Sparse/Bands/Light/SynthesisBounds.lean | removed: `quadForm_transpose_mul_self`, `quadForm_eq_dotProduct`×2 |
| Sketching/Sparse/Bands/Light/ZeroBlock.lean | removed: `quadForm_eq_dotProduct` |
| Sketching/Sparse/CountSketch.lean | `.transpose_mul_self`×1; changed: `quadForm_eq_sum` |
| Sketching/Structured/SRHTFlattening.lean | alias: `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols` |
| Solvers/Kaczmarz/KaczmarzExtensions.lean | alias: `moorePenroseInverse_mul_isSymm` |
| Solvers/Kaczmarz/KaczmarzProbability.lean | changed: `moorePenroseInverse_eq_pinvL` |
| Solvers/SketchAndProject/Core.lean | alias: `moorePenroseInverse_mul_isSymm` |

Totals: removed names 112 lines, `.transpose_mul_self` 122, alias names 115, changed names 58.

## Acceptance greps (my files)

```
grep -c "Matrix (Fin" <my files>   → MoorePenrose 17 (IsSVD/rectDiag section: SVD agent's Fintype change),
                                     Projections 6 (exists_unitary_completion/complement and private col: Fin k),
                                     others 0
grep -n "_fin\b" <my files>        → 0
real-typed public statements       → only the 4 RowProjector lemmas in MoorePenrose (not twins, see above)
public names with `transpose` (not conjTranspose) → isSymm_transpose_mul_mul, pinvL_transpose, pinvR_transpose,
                                     moorePenroseInverse_transpose, IsMoorePenroseInverse.transpose (all general over 𝕜)
grep -n "(.* - .*)\.PosSemidef" <my files> → 0
deprecated aliases                 → 23 (Projections 13, QuadForm 1, Pseudoinverse 2, MoorePenrose 3, Projector 1,
                                     Transformations 3)
```

The two `Matrix (Fin` items are outside items 1–4 of this task:
* `exists_unitary_completion` / `exists_unitary_complement` are stated on `Fin k`. The complement's
  output width `r` is existential.
* The `IsSVD` part of MoorePenrose follows the SVD agent's `Fintype` change.

## For the coordinator

* Atlas: tags moved with the merges. `projection-facts`, `orthonormal-completion`,
  `pseudoinverse` and `pinv-frob-moment` now sit only on general declarations. `atlas/atlas.json`
  still names the removed `NLAlib.frobSq_pinvR_eq_re_trace_inv`,
  `NLAlib.frobSq_moorePenroseInverse_eq_re_trace_moorePenroseInverse`, `NLAlib.transpose_mul_residual`,
  `NLAlib.exists_orthogonal_completion`, … until `ExtractDecls` + `sync_atlas.py` is rerun on a green tree.
  Hand-written `usage` strings may name removed declarations.
* The root-namespace `Matrix.IsHermitian.*` / `Matrix.PosSemidef.*` / `Matrix.PosDef.*` lemmas are
  extracted by `ExtractDecls.lean` as γ1 has modified it (module-based membership). I did not check
  `check_names.py` on them, because a full `import NLAlib` is not green.
* `HasOrthonormalCols.transpose_mul_self` has no alias. About 120 call sites in about 60 files use
  `rw [hQ.transpose_mul_self]` (or `congrArg … hQ.transpose_mul_self`) on `ᵀ` goals, and none of them
  would unify with `conjTranspose_mul_self`. This is the largest item for the repair wave.
