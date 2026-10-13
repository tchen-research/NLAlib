# RCLike round, stage A-3, agent γ: `Matrix/Basic/MoorePenrose*`

Date: 2026-10-13. Files: `NLAlib/Matrix/Basic/{MoorePenrose, MoorePenroseProjector,
MoorePenroseRank, MoorePenroseTransformations}.lean` (345/73/20/101 → 437/87/21/113 lines). No other
file was edited. `lake build` of all four modules passes with no warnings, and
`scripts/check_names.py` passes (7060 declarations).
Imports: unchanged except that `MoorePenroseTransformations` drops `Mathlib.Tactic.FieldSimp` (the
`smul` proof no longer uses `field_simp`). Scratch checks are in `/tmp/a3mp/scratch/T.lean` and `T2.lean`.

## Definition

`moorePenroseInverse {𝕜} [RCLike 𝕜] (A : Matrix m n 𝕜) : Matrix n m 𝕜 :=
(exists_isMoorePenroseInverse A).choose`. Existence goes through the general `exists_isSVD` and
`IsSVD.isMoorePenroseInverse`: `V * rectDiag σ⁻¹ * Uᴴ`, transported by
`IsMoorePenroseInverse.unitary_transform`. The private helpers (`rectDiag_mul_reversed`,
`rectDiag_mul_inverse_mul`, `isMoorePenroseInverse_rectDiag`) are over 𝕜. The diagonal is written as
`diagonal (fun i => ((if i < n then σ i * τ i else 0 : ℝ) : 𝕜))`, so Hermitian-ness comes from a
private `isHermitian_diagonal_ofReal`. At ℝ, `moorePenroseInverse` is the old definition up to the
existence proof (proof irrelevance; nothing unfolds it). The `atlas: pseudoinverse` tag stays.
The ℂ instance elaborates (scratch).

## Generalised in place (same name; the statement has no `ᵀ` at ℝ)

- **MoorePenrose:** `exists_isMoorePenroseInverse`, `isMoorePenroseInverse`,
  `mul_moorePenroseInverse_mul`, `moorePenroseInverse_mul_moorePenroseInverse`,
  `mul_moorePenroseInverse_isIdempotentElem`, `moorePenroseInverse_mul_isIdempotentElem`,
  `range_mul_moorePenroseInverse_eq`, `moorePenroseInverse_transpose` (field-agnostic),
  `moorePenroseInverse_moorePenroseInverse`, `moorePenroseInverse_zero`,
  `moorePenroseInverse_eq_zero_iff`.
- **Rank:** `rank_mul_moorePenroseInverse`.
- **Projector:** `trace_mul_moorePenroseInverse` (`= (A.rank : 𝕜)`). At ℝ, `rw [← …]` still matches
  `(A.rank : ℝ)` despite the `Nat.cast` instance path (scratch; this is Leverage's usage).
- **Transformations:**
  - `moorePenroseInverse_smul` (now `c : 𝕜`; real `simp only [moorePenroseInverse_smul]` still fires);
  - `moorePenroseInverse_eq_inv_of_isUnit`;
  - `moorePenroseInverse_posSemidef` (stated under `open scoped ComplexOrder`). At ℝ it accepts a
    `PosSemidef` over the real order and composes with `.conjTranspose_mul_mul_same`. The scratch file
    checks this, and so does GeneralizedSchurComplement, which builds.
- **Generalised although the ℝ form gains `ᴴ`** (zero callers outside the file, and the name has no
  `transpose`):
  - `IsSVD.isMoorePenroseInverse` (`… * Uᴴ`);
  - `specNorm_moorePenroseInverse_sq` (`specNorm ((A * Aᴴ)⁺)`).

## New general lemmas (𝕜)

- `mul_moorePenroseInverse_isHermitian`, `moorePenroseInverse_mul_isHermitian`.
- `moorePenroseInverse_conjTranspose` (`(Aᴴ)⁺ = (A⁺)ᴴ`).
- `moorePenroseInverse_conjTranspose_mul_self` (`(AᴴA)⁺ = A⁺A⁺ᴴ`) and
  `moorePenroseInverse_self_mul_conjTranspose` (`(AAᴴ)⁺ = A⁺ᴴA⁺`).
- `frobSq_moorePenroseInverse_eq_re_trace_moorePenroseInverse` (`= re tr (AAᴴ)⁺`; atlas `pseudoinverse`).
- `IsSVD.moorePenroseInverse_eq_mul_conjTranspose` (`A⁺ = V Σ⁺ Uᴴ`).
- `isMoorePenroseInverse_pinvL_of_isUnit_conjTranspose_mul_self`,
  `isMoorePenroseInverse_pinvR_of_isUnit_mul_conjTranspose_self`,
  `moorePenroseInverse_eq_pinvL_of_isUnit_conjTranspose_mul_self`,
  `moorePenroseInverse_eq_pinvR_of_isUnit_mul_conjTranspose_self`. These follow A-2's split
  convention, for the compound-`G` unification reason given in A2-Pseudoinverse.md.
- `mul_conjTranspose_eq_mul_moorePenroseInverse` (Projector: `QQᴴ = YY⁺`, hypothesis
  `Q * (Qᴴ * Y) = Y`; the proof uses `frobInner_eq_re_trace` and `RCLike.natCast_re`).
- `moorePenroseInverse_isHermitian` (`A.IsHermitian → A⁺.IsHermitian`).
- `moorePenroseInverse_mul_left_eq_mul_conjTranspose` (`(QA)⁺ = A⁺Qᴴ` for `HasOrthonormalCols Q`).

## Kept real under the current names (D1, term-mode or the old proof)

- **MoorePenrose:** `mul_moorePenroseInverse_isSymm`, `moorePenroseInverse_mul_isSymm`,
  `IsSVD.moorePenroseInverse_eq` (`Uᵀ`), `isMoorePenroseInverse_pinvL`, `isMoorePenroseInverse_pinvR`,
  `moorePenroseInverse_eq_pinvL`, `moorePenroseInverse_eq_pinvR` (hypotheses `IsUnit (Aᵀ * A)` /
  `IsUnit (A * Aᵀ)`), `moorePenroseInverse_transpose_mul_self`,
  `moorePenroseInverse_self_mul_transpose`, `frobSq_moorePenroseInverse_eq_trace_moorePenroseInverse`.
- **Projector:** `mul_transpose_eq_mul_moorePenroseInverse`.
- **Transformations:** `moorePenroseInverse_isSymm`, `moorePenroseInverse_mul_left_of_hasOrthonormalCols`.
  The latter now carries only `[DecidableEq m]`: the unused `[DecidableEq n] [DecidableEq p]` were
  dropped. The explicit arguments `Q A hQ` are unchanged.
- **No caller, kept for uniformity:** `isMoorePenroseInverse_pinvL/R`, `moorePenroseInverse_eq_pinvR`,
  `moorePenroseInverse_self_mul_transpose`, `frobSq_moorePenroseInverse_eq_trace_moorePenroseInverse`.
  Retire them in the D1 cleanup.

**Stayed real** (real dot-product statements, as in Norms/Core): the `RowProjector` section of
MoorePenrose, which holds `dotProduct_self_sub_moorePenroseInverse_mul_mulVec`,
`dotProduct_moorePenroseInverse_mul_mulVec_le_dotProduct_self`,
`inv_specNorm_moorePenroseInverse_sq_mul_dotProduct_le` and
`inv_specNorm_pinvL_sq_mul_dotProduct_le` (Kaczmarz / sketch-and-project helpers).

## Known breakages repaired in my files

- MoorePenrose l.84 `rw [← h.eq] at hP`: the proof is now general, using
  `rwa [← h.eq] at hP` on the `unitary_transform` of the 𝕜 `rectDiag` inverse.
- MoorePenroseTransformations l.36/38/75/88 (`constructor` + `transpose_smul` /
  `simp only [transpose_mul]` / `congrArg transpose`): the proofs are rewritten over 𝕜 with
  `refine ⟨?_,?_,?_,?_⟩`. They use the auxiliary equalities `(cA)(c⁻¹B) = AB` / `(c⁻¹B)(cA) = BA`
  and `B Qᴴ (Q A) = B A`, plus the `unitary_transform`-style calc for `(Q(AB)Qᴴ)ᴴ`.

## Probe (one `lake build` at a time; no dependant edited)

ConditionNumber was not built separately (another agent is editing it). Neither were KyFanNorm and
Schatten. ObliqueFrameInverse imports ConditionNumber transitively; its build stopped earlier, at
OrthogonalProducts, QR and Spectral/Core.

| module | result | first error / cause |
|---|---|---|
| Matrix.Basic.GeneralizedSchurComplement | ✔ | uses `moorePenroseInverse_isSymm`, the general `moorePenroseInverse_posSemidef` at ℝ, and `moorePenroseInverse_transpose` |
| Solvers.SketchAndProject.Core | ✔ | |
| Solvers.Kaczmarz.KaczmarzProbability | ✔ | `rw [… moorePenroseInverse_eq_pinvL A hA …]` |
| Matrix.Basic.SingletonInverse | ✖ (A-1, known) | l.28/30: `constructor` then `simp only [Matrix.transpose_apply, …]` on a `ᴴ` field. Fix: `rw [isMoorePenroseInverse_iff_transpose]; refine ⟨?_,?_,?_,?_⟩` |
| Matrix.Structured.KroneckerIdentities | ✖ (A-1, known) | l.51/53: `rw [← Matrix.kroneckerMap_transpose]` after `constructor`. Same fix, or generalise with `Matrix.conjTranspose_kronecker` |
| Matrix.Subspaces.GramColumnDeterminant | ✖ (A-2 pinv, predicted) | l.45: `simp only [pinvL, Matrix.mul_assoc]` leaves `Bᴴ` (error reported at l.38). Fix: `pinvL_eq_inv_transpose_mul_mul_transpose`. Its `rw [moorePenroseInverse_eq_pinvL B hG]` at l.44 elaborates |
| LowRank.Structural.RangeFinder | ✖ (A-2, known) | l.95: `frobSq_mul_left_of_orthonormal hU₂` (pass `hU₂.transpose_mul_self`) |
| Matrix.Subspaces.InverseOverlapGram, Matrix.Norms.RankNorm, Sketching.Sampling.Leverage, Matrix.Spectral.EckartYoung, Solvers.Kaczmarz.KaczmarzExtensions | blocked | Spectral/Core l.691 (`unfold specNorm pinvR`; A-2 pinv) |
| Matrix.Perturbation.PseudoinverseProjectors, PseudoinverseDifference, Matrix.Subspaces.GramIsometry | blocked | Subspaces/OrthogonalProducts l.30/49/61 (`rw [hQ]`; A-2) and Spectral/Core |
| LowRank.Nystrom.Structural | blocked | OrthogonalProducts, SketchedRegression (l.145/162/171), Structured/Measurable (pinv `fun_prop`), RangeFinder, Spectral/Core |
| Matrix.Factorizations.PolarDecomposition | blocked | OrthogonalProducts, Measurable |
| Matrix.Subspaces.ObliqueFrameInverse | blocked | OrthogonalProducts, Factorizations/QR l.333 (`unfold pinvL`), Spectral/Core |

No probe failure is caused by the changes in this stage. The rewrites with my lemmas that the
blocked files perform were replayed at ℝ in `/tmp/a3mp/scratch/T2.lean`, and all pass:

- `rw [h.moorePenroseInverse_eq, transpose_mul …]` (RankNorm);
- `rw [moorePenroseInverse_transpose_mul_self, …]` (Nyström Structural, ConditionNumber);
- `rw [← moorePenroseInverse_eq_inv_of_isUnit C hC]` (InverseOverlapGram);
- `rw [moorePenroseInverse_mul_left_of_hasOrthonormalCols Q R hQ, …]` (QRConsequences,
  ConditionNumber);
- `rw [← trace_mul_moorePenroseInverse A]` and `rw [← mul_transpose_eq_mul_moorePenroseInverse hU hUA hr]`
  (Leverage).

## For the coordinator

- No files created or deleted, so the aggregators are unchanged. Nothing was renamed: every old name
  keeps its old ℝ statement. The two exceptions with zero callers, `IsSVD.isMoorePenroseInverse` and
  `specNorm_moorePenroseInverse_sq`, now show `ᴴ` at ℝ.
- Stage B additions from this probe: none new. SingletonInverse and KroneckerIdentities were already
  reported by A-1.
- For ConditionNumber (the other A-3 agent), these general forms are available:
  - `moorePenroseInverse_smul` (`c : 𝕜`);
  - `moorePenroseInverse_transpose` and `moorePenroseInverse_conjTranspose`;
  - `moorePenroseInverse_conjTranspose_mul_self`;
  - `moorePenroseInverse_mul_left_eq_mul_conjTranspose`.
- D11 (`complexColumnProjector` → `B * moorePenroseInverse B`) is now expressible over ℂ.
  `mul_conjTranspose_eq_mul_moorePenroseInverse` and `trace_mul_moorePenroseInverse` are the C2
  tools.
- Atlas D13: the `pseudoinverse` entry text can say "over ℝ or ℂ, `V Σ⁺ Uᴴ`".
