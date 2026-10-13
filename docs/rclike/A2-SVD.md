# RCLike round, stage A-2, agent γ: `Matrix/Spectral/SVD`

Date: 2026-10-13. File: `NLAlib/Matrix/Spectral/SVD.lean` (511 → 660 lines; no other file edited).
`lake build NLAlib.Matrix.Spectral.SVD` succeeds with no warnings; `scripts/check_names.py` OK.
Imports unchanged (`Mathlib.Analysis.InnerProductSpace.SingularValues`, `NLAlib.Matrix.Norms.Core`).
Index types unchanged: `IsSVD`, `rectDiag` stay `Fin`-indexed (D10, §3.3 item 7).

## Definitions (over `{𝕜 : Type*} [RCLike 𝕜]`)

| def | new form | at ℝ |
|---|---|---|
| `rectDiag σ : Matrix (Fin m) (Fin n) 𝕜` | `of fun i j => if (i : ℕ) = j then (σ i : 𝕜) else 0`, `σ : ℕ → ℝ`, 𝕜 implicit | definitional to the old matrix (`rectDiag_eq_of`, `rfl`) |
| `structure IsSVD A U V` | fields `conjTranspose_mul_left : Uᴴ * U = 1`, `conjTranspose_mul_right : Vᴴ * V = 1`, `eq : A = U * rectDiag (singularValues A) * Vᴴ` | anonymous constructor `⟨hU, hV, h⟩` with `ᵀ` proofs still works; `h.2` is accepted as `Vᵀ * V = 1` (tested) |

`atlas: svd-def` stays on `rectDiag` and `IsSVD` (D13: the atlas text still says ℝ).

## Generalised (𝕜)

* In place, same name and statement shape (no `ᵀ`/cast at ℝ): `rank_eq_card_singularValues_ne_zero`,
  `transpose_rectDiag` (transpose is field-agnostic), `rectDiag_add`, `exists_isSVD`,
  `IsSVD.mul_right`.
* `exists_isSVD` (atlas `svd`): the proof was ported with `inner 𝕜`, `((σ i : 𝕜))⁻¹ • A vᵢ` for the
  left singular vectors and `RCLike.ofReal_ne_zero` before `field_simp`; about 25 lines changed.
  It now subsumes the existence statements of `ComplexRectangularSVD`/`ComplexSquareSingularBasis`
  (C4 merges them).
* `eigenvalues₀_eq_of_eq_mul_diagonal_mul` generalised in place (hypotheses `Wᴴ * W = 1`,
  `S = W * diagonal (fun i => (μ i : 𝕜)) * Wᴴ`). It has no users outside this file, so no real
  corollary.
* New general lemmas (Mathlib `conjTranspose` names):
  `rectDiag_apply_ofReal`, `conjTranspose_rectDiag`, `conjTranspose_rectDiag_mul_rectDiag`
  (`= diagonal fun j => if j < m then ((σ j ^ 2 : ℝ) : 𝕜) else 0`),
  `rectDiag_mul_conjTranspose_rectDiag`, `conjTranspose_mul_self_of_orthonormalBasis`,
  `IsSVD.mul_conjTranspose_left/right`, `IsSVD.conjTranspose_mul`, `IsSVD.conjTranspose_mul_mul`,
  `IsSVD.conjTranspose_eq` (`Aᴴ = V Σ Uᴴ`), `IsSVD.conjTranspose_mul_self`,
  `IsSVD.mul_conjTranspose_self` (diagonals `((σ ^ 2 : ℝ) : 𝕜)`), `IsSVD.apply_eq_sum_mul_star`
  (`A i j = ∑ (σ_k : 𝕜) U i k * star (V j k)`), `IsSVD.eq_head_add_tail_mul_conjTranspose`
  (atlas `svd`), `singularValues_eq_of_eq_mul_rectDiag_mul_conjTranspose` (uniqueness, atlas `svd`).

## Kept real under the current names (D1), each a term proof (definitional at ℝ)

`rectDiag_apply`, `transpose_rectDiag_mul_rectDiag`, `rectDiag_mul_transpose_rectDiag`,
`transpose_mul_self_of_orthonormalBasis` (no callers; kept for uniformity),
`IsSVD.transpose_mul_left`, `IsSVD.transpose_mul_right` (theorems now, so `h.transpose_mul_left`
still resolves), `IsSVD.mul_transpose_left/right`, `IsSVD.transpose_mul`, `IsSVD.transpose_mul_mul`,
`IsSVD.transpose_eq`, `IsSVD.transpose_mul_self`, `IsSVD.mul_transpose_self`, `IsSVD.apply`,
`IsSVD.eq_head_add_tail` (keeps its `atlas: svd` line), `singularValues_eq_of_eq_mul_rectDiag_mul`
(keeps `atlas: svd`). No `simpa` was needed: `ᴴ ≡ ᵀ`, `star ≡ id` and `RCLike.ofReal ≡ id` at ℝ
are all accepted by term-mode elaboration.

## Bridges (ℝ, `rfl`)

* `IsSVD.eq_mul_transpose : A = U * rectDiag (singularValues A) * Vᵀ` (real form of the field `eq`).
* `rectDiag_eq_of : (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) = of fun i j => if i = j then σ i else 0`.
* `rectDiag_apply` (above) is also the bridge for entrywise unfolding.

## Deviation from the design: `rectDiag_apply` stays real

The design (§3.1) says "`rectDiag_apply` general" and "at ℝ `simp` closes the cast". Tested: false
for the forms used downstream. With a general `rectDiag_apply` instantiated at ℝ, both
`simp only [rectDiag_apply, …]` and full `simp [rectDiag_apply]` leave `↑(σ i)`
(`@RCLike.ofReal ℝ _`, not simp-normalised; `RCLike.ofReal_real_eq_id` is not `@[simp]`), and
`ring` then fails (`x * ↑(σ i) = x * σ i`). `rectDiag_apply` is used in `simp only`/`simp` lists in
20 downstream files, so the general lemma takes the name `rectDiag_apply_ofReal` and
`rectDiag_apply` keeps its real statement (D1). Likewise for every lemma whose ℝ instance would
contain a cast. A real file that *unfolds* `rectDiag` itself would see the cast; there are no such
sites (grep: 0), and `rectDiag_eq_of` is the recipe if one appears.

## What breaks downstream, and the fix

Only `h.eq` used as a **rewrite rule** (`rw [h.eq]`, `rw [← h.eq]`, `conv_lhs => rw [h.eq]`,
`nth_rw … [h.eq]`) followed by `ᵀ`-shaped steps: the rewritten goal now contains `Vᴴ`.
Definitional uses (`exact`, `congrArg _ h.eq`, passing `h.eq` to a `Vᵀ` hypothesis, calc steps
with a stated type) keep working (tested). Fix: `h.eq` ↦ `h.eq_mul_transpose`. A record
constructor `{ transpose_mul_left := … }` would also break; there are none.

## Probe (no downstream file edited; one `lake build` at a time)

Direct importers of `Spectral/SVD`: 6 (RangeFinder, MoorePenrose, ComplexSquareSingularBasis,
the `Spectral` aggregator, SingularValueSpectrum, SvdPowers). The probe covered those plus the
named second-ring dependants. The tree also held the concurrent A-2 edits to `Subspaces/Projections`
(α) and `Basic/Pseudoinverse` (β), and several builds were blocked by them.

| module | result | first error / note |
|---|---|---|
| Matrix.Spectral.SingularValueSpectrum | ✔ | uses `h.transpose_mul_right`, `transpose_mul_self` |
| Matrix.Spectral.ComplexSquareSingularBasis | ✔ | |
| Matrix.Norms.KyFanNorm | ✔ | |
| Matrix.Spectral.SvdPowers | ✖ **SVD** | l.41 `conv_lhs => arg 2; rw [h.eq]` leaves `* Vᴴ` vs `* Vᵀ` (predicted, IsSVD) |
| Matrix.Spectral.RealDilation | ✖ **SVD** | l.171 `rw [← h.eq, h.transpose_eq, …]`: pattern `U * rectDiag … * Vᴴ` not found (**not predicted**) |
| Matrix.Basic.MoorePenrose | ✖ **SVD** | l.84 `rw [← h.eq] at hP` in `IsSVD.isMoorePenroseInverse` (**not predicted**). A-3 owns this file |
| Matrix.Spectral.SingularValueInvariance | ✖ not SVD | l.70 `rw [HasOrthonormalCols, …]` (α's Projections, HasOrthonormalCols unfold). Its `singularValues_eq_of_eq_mul_rectDiag_mul h.transpose_mul_right h.transpose_mul_left …` at l.27 elaborates |
| Matrix.Spectral.SpectralBounds | blocked | `Spectral/Core` l.691 fails: `pinvR`-shape `Aᴴ * (A * Aᴴ)⁻¹` (β's Pseudoinverse) |
| Matrix.Spectral.ComplexRectangularSVD | blocked | same `Spectral/Core` failure |
| Matrix.Spectral.SingularValueScaling, Functions.DiagonalFilter, Norms.RectangularDiagonal | blocked | `Spectral/Core` and/or SingularValueInvariance |
| Matrix.Spectral.SvdBlocks, SquareSingularBasis, Norms.InvariantNormRepresentation | blocked | MoorePenrose (SVD), Spectral/Core (β), Subspaces/OrthogonalProducts (α) |
| Matrix.Factorizations.RankRevealingLeading | blocked | OrthogonalProducts (α: `rw` with HasOrthonormalCols), Structured/Measurable (β: `fun_prop` on `pinvL` with `ᴴ`), MoorePenrose |
| Matrix.Spectral.EckartYoung, Norms.RankNorm, LowRank.Structural.RangeFinder | not built | all import `Basic/MoorePenrose` |

The three SVD-caused failures were fixed on scratch copies (`/tmp/svdA2/fix/`, one-token edit
`h.eq` ↦ `h.eq_mul_transpose`) and each copy compiles with `lake env lean`.

**Static scan** of the remaining `IsSVD` `.eq` rewrites (not buildable yet; same fix expected):
`Inequalities/KyFanAttainment` l.89 (`conv_lhs => rw [hSVD.eq]` then `simp only [mul_assoc]` has to
close against `Rᵀ * R`), `Inequalities/VonNeumann` l.266, `Factorizations/ProcrustesRotations`
l.108 (`nth_rw 1 [hB.eq]`), `Factorizations/NearestPolar` l.101 (`← hSVD.eq`; l.87
`simpa … using hSVD.eq.symm` should survive because `simp` normalises `ᴴ` to `ᵀ`),
`Norms/SchattenSingularCoefficients` l.78, `Perturbation/SingularFrames` l.110 and l.121, and
`Structured/KroneckerSingularValues` l.31. Definitional uses that should keep working:
`SingularValueScaling` l.32 and `InvariantNormRepresentation` l.56.

**Add to the stage-B list** (not in `stageA_breakage.json` under `IsSVD`): `Basic/MoorePenrose`,
`Spectral/RealDilation`, `Factorizations/ProcrustesRotations`, and `KyFanAttainment`,
`VonNeumann`, `NearestPolar` for the `IsSVD` cause (they are listed only for other causes).

## For the coordinator

* No new files, so the aggregators are unchanged. No renames: every old name still exists with
  its old statement, and all new names are additive.
* Atlas D13: the `svd-def`/`svd` texts should say `A = U Σ Vᴴ` with `U`, `V` unitary over RCLike.
  The general lemmas `exists_isSVD`, `IsSVD.eq_head_add_tail_mul_conjTranspose` and
  `singularValues_eq_of_eq_mul_rectDiag_mul_conjTranspose` carry `atlas: svd`, and so do the
  real forms `IsSVD.eq_head_add_tail` and `singularValues_eq_of_eq_mul_rectDiag_mul`.
* A-3 (MoorePenrose owner): `IsSVD.isMoorePenroseInverse` can be generalised with γ-A1's
  `IsMoorePenroseInverse.unitary_transform` plus `h.conjTranspose_mul_left/right` and `h.eq`.
  The minimal real fix is `rw [← h.eq_mul_transpose] at hP`.
* C4 can now delete the existence parts of `ComplexRectangularSVD`/`ComplexSquareSingularBasis`
  in favour of `exists_isSVD` at `𝕜 := ℂ` (tested: `exists_isSVD (A : Matrix (Fin m) (Fin n) ℂ)`
  elaborates).
