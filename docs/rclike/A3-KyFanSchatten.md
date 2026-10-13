# RCLike round, stage A-3, agent β: `Matrix/Norms/{KyFanNorm, Schatten}`

Date: 2026-10-13. Files: `NLAlib/Matrix/Norms/KyFanNorm.lean` (38 → 42 lines) and
`NLAlib/Matrix/Norms/Schatten.lean` (99 → 126 lines). No other file edited, no files created or
deleted, no renames (aggregators and rename maps unchanged). `scripts/check_names.py` OK.

## Build status

* `lake build NLAlib.Matrix.Norms.KyFanNorm`: ✔ (no warnings).
* `NLAlib.Matrix.Norms.Schatten`: **blocked upstream**, not by this file. Its only NLAlib imports
  now are `KyFanNorm` and `Spectral/SingularValueInvariance`, and the latter fails at l.70
  (`rw [HasOrthonormalCols, Matrix.transpose_transpose]`, the predicted A-2 `HasOrthonormalCols`
  unfold; it is in `stageA_breakage.json`). Verified instead on a scratch file
  (`/tmp/a3ks/Scratch.lean`: imports `KyFanNorm`, `GramSingularValues`, `Projections`; body =
  SingularValueInvariance with the one-token fix `HasOrthonormalCols` ↦
  `hasOrthonormalCols_iff_transpose_mul_self` at l.70, followed by the new Schatten.lean
  verbatim). It compiles with `lake env lean`, no warnings. Schatten.lean builds as soon as
  stage B applies that fix.

## Definitions (over `{𝕜 : Type*} [RCLike 𝕜]`, real-valued, bodies unchanged)

| def | at ℝ |
|---|---|
| `kyFanNorm A k := ∑ i ∈ range k, A.toEuclideanLin.singularValues i` | identical term (rfl) |
| `nuclearNorm A := kyFanNorm A (min (card m) (card n))` | identical term |
| `schattenNorm A p := (∑ i ∈ range (min …), singularValues A i ^ p) ^ (1 / p)` | identical term |
| `schattenNormExtended A p := if p = ∞ then specNorm A else schattenNorm A p.toReal` | identical term |

Binder order: `{𝕜} [RCLike 𝕜]` first, then the old binders. `KyFanNorm.lean` still imports only
`Mathlib.Analysis.InnerProductSpace.SingularValues`. Atlas tags (`ky-fan-norms-def (partial)`,
`schatten-norms-def (partial)`) stay on the definitions (D13: the atlas texts say ℝ).

Checked at ℝ on scratch: `unfold nuclearNorm kyFanNorm`, `unfold schattenNorm`,
`simp [kyFanNorm]`, `rw [schattenNormExtended_eq_of_ne_top _ hp]` (𝕜 is solved by unification),
`simp only [schattenNormExtended_eq_of_ne_top _ (…), ENNReal.toReal_one, schattenNorm_one]`,
`rw [← schattenNorm_one, …]`, and passing `hU : Uᵀ * U = 1` to `schattenNorm_orthogonal_mul`.

## Lemmas in Schatten.lean

Generalised in place (same name, statement unchanged at ℝ, no `ᵀ` or cast):

* `schattenNormExtended_top` (simp), `schattenNormExtended_eq_of_ne_top`, `schattenNorm_nonneg`,
  `schattenNorm_one` (simp; `= nuclearNorm A`).
* `schattenNorm_orthogonal_mul` (`HasOrthonormalCols U`, `U : Matrix m m 𝕜`): new field-agnostic
  proof by `singularValues_eq_of_gram_eq` (GramSingularValues, already RCLike), because
  `(UA)ᴴ(UA) = AᴴA`. It no longer uses the real `singularValues_isometry_mul`.
* `schattenNorm_mul_orthogonal` (`HasOrthonormalCols V`, `V` square): new proof by
  `singularValues_eq_of_gram_charpoly_eq` and `Matrix.charpoly_mul_comm`, since
  `(AV)ᴴ(AV) = Vᴴ(AᴴA V)` has the charpoly of `(AᴴA V)Vᴴ = AᴴA` (`VVᴴ = 1` by
  `mul_eq_one_comm`). It no longer uses the real `singularValues_mul_orthogonal`.

The names keep "orthogonal" (D1: names stable; the statements are already the `Uᴴ U = 1` form
through `HasOrthonormalCols`, so no separate real corollary is needed).

Kept real (the singular-value facts they rest on are still real-only; **stage B3 follow-ups**):

| lemma | needs over 𝕜 | where |
|---|---|---|
| `schattenNorm_reindex` | `singularValues_reindex` | Spectral/SingularValueSpectrum (proof looks field-agnostic: `sq_singularValues_eq_eigenvalues₀`, `eigenvalues₀_eq_of_matrix_eq`, `eigenvalues₀_reindex`) |
| `schattenNorm_two` (+ private `schattenNorm_two_fin`) | `frobSq_eq_sum_sq_singularValues` and its private Fin step (uses `frobInner_eq_trace`, `h.transpose_mul_self`), `frobSq_reindex`/`frobNorm_reindex` | SingularValueSpectrum; Norms/Reindex (`frobInner_reindex` unfolds `frobInner` with `simp only`, so it needs the A-1 bridge or a 𝕜 proof) |
| `schattenNorm_transpose` | a general `singularValues_conjTranspose` (`σ(Aᴴ) = σ(A)`; Fin case from `exists_isSVD` + `IsSVD.conjTranspose_eq` + `singularValues_eq_of_eq_mul_rectDiag_mul_conjTranspose`, then general reindex) | Spectral/SingularValueInvariance |

When those exist, the general forms are `schattenNorm_reindex` and `schattenNorm_two` in place
and a new `schattenNorm_conjTranspose`, with `schattenNorm_transpose` kept real (D1). The same
applies to `kyFanNorm_{reindex, transpose, orthogonal_mul, mul_orthogonal}` in KyFanNorms
(stage B/C, not touched).

## Import change in Schatten.lean

`import NLAlib.Matrix.Inequalities.KyFanNorms` (the Ky Fan variational chain: KyFanAttainment,
KyFan, VonNeumann, TraceTail, OrthogonalProducts, MoorePenrose, …) became
`import NLAlib.Matrix.Norms.KyFanNorm` + `import NLAlib.Matrix.Spectral.SingularValueInvariance`,
which is all the file uses. Schatten now sits much earlier in the graph and waits only for the
SingularValueInvariance repair, not the whole Ky Fan chain. Safe for dependants: the only direct
importers are the `Norms` aggregator, `SchattenNorms` (imports `KyFanNorms` itself) and
`SchattenTrace` (imports `NuclearNorm`, which imports `KyFanNorms`), so every transitive
importer still sees `KyFanNorms`.

## Probe of dependants (one `lake build`, log `/tmp/a3ks/probe1.log`)

Targets: Schatten, Inequalities/KyFan, Inequalities/KyFanNorms, Norms/NuclearNorm,
SchattenDuality, SchattenProducts, NuclearGram, SchattenNorms, SchattenTrace, NuclearPSD,
SchattenComparison. **None could be built**: all are blocked by upstream failures that are not
caused by A-3-β.

| upstream failure (stage A cause) | blocks |
|---|---|
| Spectral/SingularValueInvariance l.70 (`HasOrthonormalCols` unfold) | all eleven targets |
| Subspaces/OrthogonalProducts l.30, 49, 61 (`rw [hQ]`) | all except Schatten |
| Basic/MoorePenrose l.84 (`rw [← h.eq]`, IsSVD; A-3-γ owns it) | all except Schatten |
| Spectral/Core l.691 (`pinvR` shape) | all except Schatten |
| Structured/Measurable l.97, 140, 190 (`fun_prop` on `pinvL` with `ᴴ`) | SchattenDuality, SchattenProducts, SchattenComparison |

Deeper predicted failures (KyFanAttainment `rw [hQ]` and `hSVD.eq`, VonNeumann `IsSVD`,
SchattenDuality `IsSVD`) will show only after these are repaired.

**Static scan for breakage caused by this change** (all uses of the generalised names in the
tree, plus every `unfold`/`simp only`/`rw` with the four definitions): one real failure, confirmed
on scratch.

* `Norms/SchattenToolkit.lean` l.76 and l.78: `exact ⟨@NLAlib.schattenNorm_one,
  … @NLAlib.schattenNormExtended_top, …⟩` against a real `∀ {m n} …` clause. The `@` form now
  starts with `{𝕜} [RCLike 𝕜]`, so it is a type mismatch (reproduced). **Fix (tested):**
  `@NLAlib.schattenNorm_one ℝ _` and `@NLAlib.schattenNormExtended_top ℝ _`. This file is not in
  `stageA_breakage.json`; add it to the stage-B list. No other `@`-application of the generalised
  names exists (`KyFanNormToolkit` applies only KyFanNorms lemmas, which stayed real), and no
  named-argument or numeral application (`kyFanNorm 0`, `schattenNorm (A := …)`) needs a 𝕜
  ascription.
* All other uses (SchattenComparison, SchattenDuality, SchattenEndpoints, SchattenInvariant,
  NuclearNorm, NuclearGram, NuclearPSD, NuclearHermitian, KyFan, KyFanNorms, KyFanAttainment,
  SchattenSingularCoefficients, SchattenNorms) unfold to the same terms at ℝ or use lemma
  statements that are unchanged at ℝ, and the patterns were checked on scratch.

## For the coordinator

* Stage B: the one-token fix in SingularValueInvariance l.70 unblocks Schatten.lean; add
  `Norms/SchattenToolkit` (two `@… ℝ _` edits) to the repair list.
* Stage B3: the three real-only Schatten lemmas above, together with `singularValues_reindex`,
  `frobSq_eq_sum_sq_singularValues`, `frobSq_reindex`/`frobNorm_reindex` and a new
  `singularValues_conjTranspose`.
* Atlas D13: `ky-fan-norms-def` and `schatten-norms-def` texts can say "over ℝ or ℂ".
