# RCLike round, stage A-3, agent α: `Matrix/Perturbation/ConditionNumber`

Date: 2026-10-13. File: `NLAlib/Matrix/Perturbation/ConditionNumber.lean` (123 → 149 lines). No
other file was edited. Imports are unchanged (`MoorePenroseTransformations`,
`Spectral/FiniteIndexTransport`, `Functions/FunctionalCalculusEigenvalues`). `scripts/check_names.py`
passes. Work started after `docs/rclike/A3-MoorePenrose.md` appeared and
`lake build NLAlib.Matrix.Basic.MoorePenroseTransformations` succeeded against γ's version.

## Compile status

`lake build NLAlib.Matrix.Perturbation.ConditionNumber` **cannot complete yet**. The module's import
closure contains two known A-2 breakages, so Lake stops before it reaches this file:

* `Subspaces/OrthogonalProducts` l.30, 49, 61 (`rw [hQ]`, A-2 Projections);
* `Spectral/Core` l.691 (`pinvR` unfold, A-2 Pseudoinverse).

FiniteIndexTransport needs both, and SingularValueSpectrum needs `Spectral/Core`.

The file was therefore checked in two scratch files with `lake env lean`. Both compile with no errors
and no warnings:

* `/tmp/a3cn/Scratch.lean` imports only `MoorePenroseTransformations`. It contains the definition,
  every generalised lemma, and the real corollary `conditionNumber_transpose_mul_self`, verbatim from
  the file. It also has real-use checks:
  * `conditionNumber_smul (c := c) hc A` with `c : ℝ`, as in ConditionNumberToolkit;
  * `rw [conditionNumber_mul_left_of_hasOrthonormalCols Q A hQ]` with `hQ : Qᵀ * Q = 1`, as in
    QRConsequences;
  * `rw [conditionNumber_transpose]`, `rw [conditionNumber_eq_mul_specNorm_inv hA]`,
    `unfold conditionNumber`, and `simp` on `conditionNumber 0`;
  * `one_le_conditionNumber` at `ℂ`.
* `/tmp/a3cn/Scratch2.lean` replays the proof of the real `conditionNumber_eq_singularValues_ratio`
  verbatim. The three real lemmas it needs (`specNorm_moorePenroseInverse_eq_fintype`,
  `singularValues_reindex`, `singularValues_zero_eq_specNorm`) are passed as hypotheses with their
  exact statements, which checks that the rewrites still match the generalised definition.
  `conditionNumber_eq_eigenvalues₀_ratio` only rewrites with that lemma, and its text is unchanged.

**Coordinator:** rebuild this module in A-4, after OrthogonalProducts and `Spectral/Core` are repaired.

## Definition

`conditionNumber {𝕜} [RCLike 𝕜] (A : Matrix m n 𝕜) : ℝ := specNorm A * specNorm (moorePenroseInverse A)`.
The body is unchanged, so at ℝ it is the same term, and the `unfold conditionNumber` /
`rw [conditionNumber]` sites downstream see the same goal. Those sites are Conditioning l.58 and
l.317, LeastSquaresPurePerturbation l.87 and l.147, and LeastSquaresPerturbation l.146, 160, 181
and 213. The tag `atlas: condition-number-def (partial)` stays on the definition. D13: the atlas
text may now say "over ℝ or ℂ".

## Generalised in place (same name; the statement has no `ᵀ`)

| lemma | proof uses |
|---|---|
| `conditionNumber_zero` (`@[simp]`) | `moorePenroseInverse_zero` (general) |
| `conditionNumber_nonneg` | |
| `one_le_conditionNumber` | general `mul_moorePenroseInverse_mul`, `specNorm_mul_le` |
| `conditionNumber_transpose` | general `moorePenroseInverse_transpose`, `specNorm_transpose` |
| `conditionNumber_smul` (`c : 𝕜`, `c ≠ 0`) | general `moorePenroseInverse_smul`; `norm_smul`, `norm_inv` instead of `abs` |
| `conditionNumber_mul_left_of_hasOrthonormalCols` (`hQ : HasOrthonormalCols Q`, i.e. `QᴴQ = 1`) | `moorePenroseInverse_mul_left_eq_mul_conjTranspose`; the two isometry facts `‖QB‖₂ = ‖B‖₂` and `‖BQᴴ‖₂ = ‖B‖₂` are local `have`s from Core's general `specNorm_conjTranspose_mul_of_eq_mul` |
| `conditionNumber_eq_mul_specNorm_inv` | general `moorePenroseInverse_eq_inv_of_isUnit` |

The task asked for a real corollary of `conditionNumber_mul_left_of_hasOrthonormalCols` under the
current name. None was needed: the statement contains no `ᵀ`, and real callers that pass
`hQ : Qᵀ * Q = 1` still elaborate (tested). By D1, the general lemma therefore keeps the name.

The general isometry facts (`specNorm (Q * B) = specNorm B`, and the right form with `Qᴴ`) belong
in `Norms/SpectralNormBounds`, whose `specNorm_mul_left_of_hasOrthonormalCols` and
`specNorm_mul_transpose_right_of_hasOrthonormalCols` are still real. This round did not own that
file, so the facts stay as proof-local `have`s. Suggested for B3: generalise those two lemmas there,
or add `specNorm_mul_left_of_conjTranspose_mul_self`, and shorten this proof.

## New general lemmas (𝕜)

* `conditionNumber_conjTranspose : conditionNumber Aᴴ = conditionNumber A`.
* `conditionNumber_conjTranspose_mul_self : conditionNumber (Aᴴ * A) = conditionNumber A ^ 2`. Its
  proof uses `moorePenroseInverse_conjTranspose_mul_self`, `Matrix.l2_opNorm_conjTranspose_mul_self`
  and `specNorm_mul_conjTranspose_self`. Both carry `atlas: condition-number-def (partial)`.

## Kept real (D1, or because the proof needs the real stack)

* `conditionNumber_transpose_mul_self` is the D1 corollary. It keeps its old statement and its atlas
  tag, and is proved by the term `conditionNumber_conjTranspose_mul_self A` (definitional at ℝ). Its
  caller is ConditionNumberToolkit.
* `conditionNumber_eq_singularValues_ratio` stays real, though the task listed it as a candidate. Its
  proof needs `specNorm_moorePenroseInverse_eq_fintype` (Spectral/FiniteIndexTransport, via
  Norms/RankNorm), `singularValues_reindex` (Spectral/SingularValueSpectrum) and
  `singularValues_zero_eq_specNorm` (Spectral/SpectralBounds). All three are real and outside stage
  A, so this lemma is not field-agnostic at the "statements only" level. It can be generalised once
  those three are: `singularValues_reindex`'s proof already works with `ᴴ`, while the other two go
  through the `Fin` lemmas `specNorm_moorePenroseInverse_eq` and
  `singularValues_zero_eq_specNorm_fin`. This is a B3/C4 item.
* `conditionNumber_eq_eigenvalues₀_ratio` stays real (`PosDef`, `eigenvalues₀`, and the ratio
  lemma above).

## Probe (one `lake build` at a time; no dependant edited)

| module | result | note |
|---|---|---|
| Matrix.Perturbation.Conditioning | blocked | OrthogonalProducts (l.30/49/61, `rw [hQ]`), Factorizations/QR l.333 (`unfold pinvL`), Spectral/Core l.691: all A-2, already reported |
| Matrix.Perturbation.DistanceToSingularity | blocked | OrthogonalProducts, Spectral/Core |
| Matrix.Perturbation.LeastSquaresPerturbation | blocked | OrthogonalProducts, QR, Spectral/Core |
| Matrix.Perturbation.LeastSquaresToolkit | blocked | OrthogonalProducts, QR, Spectral/Core |
| Solvers.Kaczmarz.KaczmarzProbability | ✔ | it does not import ConditionNumber; it depends only on `Basic/MoorePenrose` |

None of these could reach ConditionNumber or a file that uses it, so the probe found no failure
caused by this file.

Static scan of every downstream use:
* Lemma uses: `conditionNumber_nonneg`, `_eq_mul_specNorm_inv`, `_smul (c := c)`, `_transpose`,
  `_transpose_mul_self`, `_mul_left_of_hasOrthonormalCols`, `_eq_singularValues_ratio`,
  `_eq_eigenvalues₀_ratio` and `_zero`, in Conditioning, DistanceToSingularity, MapConditioning,
  LeastSquares{Perturbation, PurePerturbation, CoordinateBounds, Toolkit}, ConditionNumberToolkit,
  QRConsequences and QuadraticConditionBounds.
* Unfold sites: the ones listed under Definition.

All of these are either replayed in the scratch file or are unfolds of a body that is unchanged at
ℝ. No downstream breakage is expected from this file. No named-argument or `@conditionNumber` uses
exist, so 𝕜 is always inferred from the matrix.

## For the coordinator

* No files were created, deleted or renamed, and no names were dropped. Every old name keeps a
  statement that still accepts the old real uses.
* A-4: build `NLAlib.Matrix.Perturbation.ConditionNumber` once OrthogonalProducts, QR and
  `Spectral/Core` are repaired.
* B3 follow-ups:
  * generalise `specNorm_mul_left_of_hasOrthonormalCols` /
    `specNorm_mul_transpose_right_of_hasOrthonormalCols` (SpectralNormBounds), then drop the local
    `have`s here;
  * generalise the singular-value stack (`singularValues_zero_eq_specNorm`,
    `specNorm_moorePenroseInverse_eq{,_fintype}`, `singularValues_reindex`), then
    `conditionNumber_eq_singularValues_ratio`.
