# RCLike round, stage A-2: `Matrix/Basic/Pseudoinverse`

Date: 2026-10-13. File: `NLAlib/Matrix/Basic/Pseudoinverse.lean` (188 → 335 lines). No other file
was edited. `lake build NLAlib.Matrix.Basic.Pseudoinverse` passes with no warnings, and
`scripts/check_names.py` passes. Imports are unchanged (`NLAlib.Matrix.Norms.Core` only). The
design names Core as the import, and dependants may use `specNorm` through this import.

## Definitions (over `{𝕜 : Type*} [RCLike 𝕜]`)

| def | body | at ℝ |
|---|---|---|
| `pinvL G` | `(Gᴴ * G)⁻¹ * Gᴴ` | `rfl` to `(Gᵀ * G)⁻¹ * Gᵀ` |
| `pinvR G` | `Gᴴ * (G * Gᴴ)⁻¹` | `rfl` to `Gᵀ * (G * Gᵀ)⁻¹` |

The `rfl` claims were checked in a scratch file (`/tmp/a2pinv/T.lean`), and so was the ℂ instance.

## ℝ bridges (`rfl`; design §3.1 names)

* `pinvL_eq_inv_transpose_mul_mul_transpose : pinvL G = (Gᵀ * G)⁻¹ * Gᵀ`
* `pinvR_eq_transpose_mul_inv : pinvR G = Gᵀ * (G * Gᵀ)⁻¹`

Recipe for real files: replace `unfold pinvL` with `rw [pinvL_eq_inv_transpose_mul_mul_transpose]`,
and replace `pinvL` with that bridge inside a `simp only` list. The same holds for `pinvR`. This
was tested on scratch copies of all four predicted unfold files (see the probe below).

## Generalised in place (same name, same statement, now over 𝕜)

* `pinvL_transpose : (pinvL G)ᵀ = pinvR Gᵀ` and `pinvR_transpose`. These are true over any
  RCLike field: both sides are `Ḡ (Gᵀ Ḡ)⁻¹`. The proof uses
  `conjTranspose_transpose_eq_transpose_conjTranspose`.

## New general lemmas (𝕜)

* `pinvL_conjTranspose : (pinvL G)ᴴ = pinvR Gᴴ` and `pinvR_conjTranspose`.
* One-sided inverses and Penrose identities. They are named with
  `_of_isUnit_conjTranspose_mul_self` (hypothesis `IsUnit (Gᴴ * G)`) or
  `_of_isUnit_mul_conjTranspose_self` (hypothesis `IsUnit (G * Gᴴ)`):
  `pinvL_mul_of_…`, `mul_pinvR_of_…`, `mul_pinvL_mul_of_…`, `pinvL_mul_pinvL_of_…`,
  `mul_pinvR_mul_of_…`, `pinvR_mul_pinvR_of_…`, `mul_pinvL_isIdempotentElem_of_…`,
  `pinvR_mul_isIdempotentElem_of_…`.
* Hermitian projectors: `mul_pinvL_isHermitian` and `pinvR_mul_isHermitian`, which need no
  hypothesis, and `pinvL_mul_isHermitian (h : IsUnit (Gᴴ * G))` and
  `mul_pinvR_isHermitian (h : IsUnit (G * Gᴴ))`.
* `frobSq_pinvR_eq_re_trace_inv : frobSq (pinvR G) = RCLike.re ((G * Gᴴ)⁻¹).trace` and
  `frobSq_pinvL_eq_re_trace_inv`. Both hold unconditionally: in the singular case both sides are 0.

## Kept real under the current names (D1)

Each one is a term-mode one-liner from the general lemma. The hypothesis is passed definitionally,
and `IsSymm` comes from `Matrix.isHermitian_iff_isSymm.mp`.

`pinvL_mul`, `mul_pinvR`, `mul_pinvL_mul`, `pinvL_mul_pinvL`, `mul_pinvR_mul`, `pinvR_mul_pinvR`,
`mul_pinvL_isIdempotentElem`, `pinvR_mul_isIdempotentElem` (hypothesis `IsUnit (Gᵀ * G)` or
`IsUnit (G * Gᵀ)`); `mul_pinvL_isSymm`, `pinvR_mul_isSymm`, `pinvL_mul_isSymm`, `mul_pinvR_isSymm`;
`frobSq_pinvR_eq_trace_inv`, `frobSq_pinvR`, `frobSq_pinvL` (the trace is taken without `re`).
`mul_pinvL_isIdempotentElem`, `pinvR_mul_isIdempotentElem`, `frobSq_pinvR` and `frobSq_pinvL`
have no current callers. They are kept so that the family stays uniform.

**Why the hypothesis-only lemmas could not be generalised in place.** My first attempt kept
`pinvL_mul` under its name with the `IsUnit (Gᴴ * G)` hypothesis. A real caller that passes
`hM : IsUnit (Mᵀ * M)` for a *variable* `M` elaborates fine. A caller with a *compound* matrix,
such as SketchedRegression's `hG₁ : IsUnit ((Ψᵀ * Q)ᵀ * (Ψᵀ * Q))`, does not. Lean solves
`?Gᴴ =?= (Ψᵀ * Q)ᵀ` by unfolding both sides and instantiates `G` with the unfolded entry function
(`fun j i => Quot.lift … (Ψᵀ j ·) * …`). The result no longer matches `pinvL (Ψᵀ * Q)`, so
`rw [pinvL_mul hG₁]` fails. Hence the split: the general lemma gets the `_of_isUnit_…` name, and
the real lemma keeps the short name and the `ᵀ` hypothesis.

## Atlas tags

The tags stay where they were: `pseudoinverse` is on the defs and on the real lemmas that carried
it, and `pinv-frob-moment` is on `frobSq_pinvR_eq_trace_inv`. The general counterparts carry the
same ids: `pinvL_mul_of_…`, `mul_pinvR_of_…`, `mul_pinvL_mul_of_…`, `pinvL_mul_pinvL_of_…`,
`mul_pinvL_isHermitian`, `mul_pinvL_isIdempotentElem_of_…` carry `pseudoinverse`, and
`frobSq_pinvR_eq_re_trace_inv` carries `pseudoinverse, pinv-frob-moment`. D13: the `pseudoinverse`
entry text can now say `(GᴴG)⁻¹Gᴴ`.

## Downstream snippet checks (scratch, all pass)

The pinv lines below were copied into `/tmp/a2pinv/S.lean` against the new module, because their
files cannot be built yet (see the probe):
GaussianSketch / Moments.Conditioning `h1`/`h2` (`simp only [… pinvL_transpose …]` and
`rw [← frobSq_transpose, pinvL_transpose, …]`), OptimalError
(`simpa only [Matrix.mul_assoc, mul_pinvR hfull, Matrix.mul_one] using he`), Mean and
FrobeniusMoments (`rw [frobSq_pinvR_eq_trace_inv]; rfl`), RawNystromBridge (`have := pinvL_mul hM`,
calc steps, `exact mul_pinvL_isSymm M`), and SketchedRegression (`rw [pinvL_mul hG₁]` with the
compound `G`).

## Probe (`lake build`, one module at a time; no dependant edited)

The tree was in flux: the Projections (A-2) and SVD (A-2) agents were editing at the same time.

| module | result | first error / cause |
|---|---|---|
| Matrix/Basic/MoorePenrose | ✔ on the first run; ✖ on the second | first run: builds with `pinvL_mul hA`, `⟨mul_pinvL_mul h, …, (mul_pinvL_isSymm A).eq, …⟩`. Second run: l.84 `rw [← h.eq] at hP` (**IsSVD, the SVD agent**) |
| Matrix/Spectral/Core | ✖ (**pinv, predicted**) | l.683 `unfold specNorm pinvR` leaves `ᴴ`, and the later `rw` fails at l.691. Fix tested: `unfold specNorm; rw [pinvR_eq_transpose_mul_inv]` |
| Matrix/Structured/Measurable | ✖ (**pinv, predicted**) | l.92/136/186 `simp only [pinvL/pinvR, Matrix.transpose_apply, …]` leaves `ᴴ`, so `fun_prop` fails. Fix tested: `pinvL` ↦ `pinvL_eq_inv_transpose_mul_mul_transpose`, `pinvR` ↦ `pinvR_eq_transpose_mul_inv` in the three lists |
| Matrix/Factorizations/QR | ✖ (**pinv, predicted**) | l.332 `unfold pinvL`, then the `rw` at l.333 fails. Fix tested: `rw [pinvL_eq_inv_transpose_mul_mul_transpose]` |
| Matrix/Subspaces/GramColumnDeterminant | ✖ (**pinv, predicted**) | l.45 `simp only [pinvL, Matrix.mul_assoc]`. Fix tested: `simp only [pinvL_eq_inv_transpose_mul_mul_transpose, Matrix.mul_assoc]` |
| LowRank/Nystrom/SketchedRegression | ✖ (not pinv) | l.145 `unfold residual` (Projections); l.162/171 `frobSq_mul_left_of_orthonormal hQ` (see the note below). The pinv lines 90 and 137 elaborate |
| LowRank/Structural/RangeFinder | ✖ (not pinv) | l.95 `frobSq_mul_left_of_orthonormal hU₂` (see the note below). The `mul_pinvR hunit` at l.73 elaborates |
| LowRank/Nystrom/RawNystromBridge | blocked | by SketchedRegression and MoorePenrose (SVD) |
| Matrix/Perturbation/LeastSquaresGeometry | blocked | by Subspaces/OrthogonalProducts (`rw [hQ]`, Projections) and MoorePenrose |
| Matrix/Perturbation/Conditioning | blocked | by OrthogonalProducts, MoorePenrose and Spectral/Core |
| RandomMatrix/Gaussian/InverseMoments/Mean | blocked | by OrthogonalProducts and Measurable |
| RandomMatrix/Gaussian/InverseMoments/FrobeniusMoments | blocked | by OrthogonalProducts and Measurable |
| Sketching/Properties/SubspaceEmbedding | blocked | by OrthogonalProducts, MoorePenrose and Spectral/Core |
| LowRank/Nystrom/RawGaussianNystrom | blocked | by OrthogonalProducts and Measurable |
| RandomMatrix/Gaussian/Moments/Conditioning | blocked | by Measurable |

**Pinv-caused breakage: exactly the four predicted unfold files** (Spectral/Core, Measurable, QR,
GramColumnDeterminant), each with a tested one-token fix. No call site of a renamed or
re-hypothesised lemma failed.

**Note for the coordinator: a new breakage pattern, not caused by pinv, that the design does not
list.** Passing a definition-typed `hQ : HasOrthonormalCols Q`, which now means `Qᴴ * Q = 1`, to a
*real* lemma whose hypothesis is `Qᵀ * Q = 1` fails inside `rw`. An example is α's real corollary
`frobSq_mul_left_of_orthonormal`. Lean solves `?Qᵀ =?= U₂ᴴ` by unfolding and instantiates
`Q := fun y x => star (U₂ᵀ x y)`, so the rewrite pattern is not found (RangeFinder l.95,
SketchedRegression l.162/171). This is the mirror image of the compound-`G` problem above. Possible
fixes:
- at the call site, pass `hQ.transpose_mul_self` instead of `hQ`;
- at the call site, use the general lemma (`frobSq_mul_left_of_conjTranspose_mul_self hQ`);
- in Norms/Core, state the real corollaries with a `HasOrthonormalCols` hypothesis. This is not
  possible there, because Core does not import Projections.
