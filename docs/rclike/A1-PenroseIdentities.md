# A-1 (agent γ): `Matrix/Basic/PenroseIdentities`

File: `NLAlib/Matrix/Basic/PenroseIdentities.lean` (`IsMoorePenroseInverse` and its namespace).
Compiles cleanly (`lake build NLAlib.Matrix.Basic.PenroseIdentities`, no warnings).
Imports: `Mathlib.Analysis.RCLike.Basic`, `Mathlib.LinearAlgebra.Matrix.ConjTranspose`,
`Mathlib.LinearAlgebra.Matrix.ToLin` (it was `ToLin` + `Data.Real.Basic`; RCLike.Basic covers ℝ).

## Generalised (over `{𝕜 : Type*} [RCLike 𝕜]`)

* `structure IsMoorePenroseInverse (A : Matrix m n 𝕜) (B : Matrix n m 𝕜)` with fields
  `mul_mul_eq : A * B * A = A`, `inv_mul_inv_eq : B * A * B = B` (unchanged names),
  `conjTranspose_mul_eq : (A * B)ᴴ = A * B`, `conjTranspose_inv_mul_eq : (B * A)ᴴ = B * A`
  (were `transpose_mul_eq` / `transpose_inv_mul_eq` with `ᵀ`).
* `unique`, `swap`, `submatrix`, `mul_isIdempotentElem`, `inv_mul_isIdempotentElem`,
  `mulVec_eq_self_iff`, `range_mul_eq`: same names and statements, now over 𝕜.
* `transpose : IsMoorePenroseInverse Aᵀ Bᵀ`: same name, now general (the transpose of a
  Hermitian matrix is Hermitian, via `conjTranspose_transpose_eq_transpose_conjTranspose`).
* New general lemmas: `conjTranspose : IsMoorePenroseInverse Aᴴ Bᴴ`,
  `unitary_transform` (hypotheses `Uᴴ * U = 1`, `Vᴴ * V = 1`; conclusion
  `IsMoorePenroseInverse (U * A * Vᴴ) (V * B * Uᴴ)`), `conjTranspose_mul_self`
  (`IsMoorePenroseInverse (Aᴴ * A) (B * Bᴴ)`).

Scope choice: `[RCLike 𝕜]`, as the design's §1.1 table says. The algebra alone would go through
for `[CommRing 𝕜] [StarRing 𝕜]`, but every consumer (`moorePenroseInverse`, existence through the
SVD) is RCLike, and a second instance path to `Star ℝ` buys nothing.

## Stayed real (D1 corollaries, old names and statements)

* `IsMoorePenroseInverse.transpose_mul_eq : (A * B)ᵀ = A * B` and
  `IsMoorePenroseInverse.transpose_inv_mul_eq : (B * A)ᵀ = B * A` (theorems now, so
  `h.transpose_mul_eq` still resolves by dot notation; 21 + 15 use sites).
* `IsMoorePenroseInverse.orthogonal_transform` (`Uᵀ * U = 1`, `Vᵀ`): `h.unitary_transform …`.
* `IsMoorePenroseInverse.transpose_mul_self` (`(AᵀA, BBᵀ)`): `h.conjTranspose_mul_self`.

All four are proved by term (definitional at ℝ); no `simpa` needed.

## Bridge

* `isMoorePenroseInverse_iff_transpose` (ℝ):
  `IsMoorePenroseInverse A B ↔ A*B*A = A ∧ B*A*B = B ∧ (A*B)ᵀ = A*B ∧ (B*A)ᵀ = B*A`.

Definitional checks (scratch `/tmp/gamma/T.lean`, all pass): at ℝ
`((A*B)ᴴ = A*B) = ((A*B)ᵀ = A*B)` is `rfl`; `h.conjTranspose_mul_eq` and `h.4` are accepted
as `(A*B)ᵀ = A*B`; the anonymous constructor `⟨h1, h2, h3, h4⟩` with `ᵀ` proofs works;
`constructor` followed by `exact hSymm.eq` works; `rw [..., h.transpose_mul_eq]` on `ᵀ` goals
works; the instance at `ℂ` elaborates.

## What breaks downstream, and the fix

Only one pattern: `constructor` (on an `IsMoorePenroseInverse` goal at ℝ) followed by a
*rewriting* tactic proof of the third/fourth field, because the goal now shows `ᴴ`
(`simp only [Matrix.transpose_apply, …]`, `rw [← Matrix.kroneckerMap_transpose]`,
`simp only [Matrix.transpose_smul, …]`, `simpa … using congrArg Matrix.transpose …`).
`constructor <;> simp …` and `constructor` + `exact`/`calc` closes keep working.

Fix (tested on scratch copies of all three broken files, each then compiles):

```
  constructor                              ↦   rw [isMoorePenroseInverse_iff_transpose]
                                               refine ⟨?_, ?_, ?_, ?_⟩
```

## Probe (`lake build`, one module at a time; no downstream file edited)

| module | result |
|---|---|
| Matrix/Basic/MoorePenrose | ok |
| Matrix/Basic/MoorePenroseProjector | ok |
| Matrix/Basic/MoorePenroseRank | ok |
| Matrix/Norms/RankNorm | ok |
| Matrix/Subspaces/GramColumnDeterminant | ok |
| Matrix/Spectral/EckartYoung | ok |
| Matrix/Perturbation/PseudoinverseDifference (+ PseudoinverseProjectors, PseudoinverseBlocks, ProjectionGaps, ProjectorBlocks, GoldenRatioBlock, PseudoinverseSpectralPerturbation, FiniteIndexTransport rebuilt on the way) | ok |
| Matrix/Perturbation/InversePerturbation | ok |
| LowRank/Nystrom/RawNystromBridge (`constructor` + `exact mul_pinvL_isSymm`) | ok |
| Matrix/Basic/SingletonInverse | **breaks**: l.28, l.30 (`simp only [Matrix.transpose_apply, …]` after `constructor`) |
| Matrix/Structured/KroneckerIdentities | **breaks**: l.51, l.53 (`rw [← Matrix.kroneckerMap_transpose]`) |
| Matrix/Basic/MoorePenroseTransformations | **breaks**: l.36, l.38 (`Matrix.transpose_smul`), l.75, l.88 (`simp only [Matrix.transpose_mul, …]` / `simpa using congrArg Matrix.transpose`) |

These three files are not in `stageA_breakage.json` (cause: `IsMoorePenroseInverse` constructor);
add them to stage B. A scan for `constructor`/`refine ⟨` within four lines of an
`isMoorePenroseInverse` use finds no further sites (the other ones are MoorePenrose l.66, l.212,
RawNystromBridge, and the `constructor <;> simp` in MoorePenroseTransformations l.47, all of which
build). Probe builds ran against the tree as it was at 09:00–09:10 (Norms/Core and QuadForm were
in α's and β's hands; no failure came from them).

Stage-B notes: KroneckerIdentities can instead be generalised with `Matrix.conjTranspose_kronecker`;
MoorePenrose's `moorePenroseInverse` (A-3) can use `unitary_transform` with the general SVD.
