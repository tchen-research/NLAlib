# RCLike round: Matrix-layer vocabulary over `[RCLike 𝕜]`

Owner's decision (2026-10-12): "we should handle complex case like mathlib." This is the design
produced for it (by the design agent, Lean-checked prototypes in `docs/rclike/Proto.lean`), with
the coordinator's decisions on its open points recorded first.

## Decisions taken (coordinator, 2026-10-13)

- **D1**: keep the ~70 one-line real corollaries under their current names (proved `by simpa using`
  the general lemma); retiring them is a later cleanup, not this round.
- **D2, D6, D7, D9, D10, D14**: as recommended by the design.
- **D3**: `quadForm A z := star z ⬝ᵥ (A *ᵥ z)` is `𝕜`-valued (Mathlib's `PosSemidef` form);
  `rayleighQuotient` is real-valued; `frobInner` takes the real part.
- **D4**: raw `Qᵀ * Q = 1` hypotheses stay as they are (they still elaborate against
  `HasOrthonormalCols Q := Qᴴ * Q = 1` over ℝ); no real abbreviation.
- **D5**: complex statements in merged files and the Frobenius-scope files use `specNorm` /
  `frobNorm`; `‖A‖` stays in the CFC and Probability files. STANDARDS §3 is updated accordingly.
- **D8**: only the Krylov space definitions (`krylovSpace`, `blockKrylovSpace`, `subspaceIterate`)
  are generalised to any field; the Krylov methods stay real.
- **D11/D12**: delete `complexColumnProjector` in favour of `B * moorePenroseInverse B`; build the
  RPCholesky and volume-sampling keepers over RCLike from the complex stacks.
- **D13**: the 12 atlas definition entries that say ℝ are reworded by the coordinator after the
  round; tags move to keepers via the docstrings (sync picks them up).

# RCLike round: design (2026-10-13)

Owner's decision (2026-10-12, docs/DEDUP_FOLLOWUP.md): the Matrix-layer vocabulary is stated once over
`{𝕜 : Type*} [RCLike 𝕜]` with `conjTranspose`, as Mathlib does for `PosSemidef`, `IsHermitian`, the
L2 operator norm and `LinearMap.singularValues`. Real theorems keep their statements; Probability,
RandomMatrix and Sketching stay real.

This design is read-only analysis of the tree at /home/tyler/Documents/prove2me/lean (1106 `.lean`
files, 520 in `NLAlib/Matrix`). Machine-readable companion: `design.json` (inventory, per-file
breakage list with dependency waves, file classification, stage C families, decisions). Raw scan
data is in `tools/*.json`; the scripts that produced it are `tools/*.py`. Lean claims marked
"tested" were checked with `lake env lean` on the scratch files `T1.lean`–`T4.lean` and
`Proto.lean` in this directory. `Proto.lean` is a compiling prototype of the core of stage A.

Counting conventions. *refs* = files (comments stripped, aggregators excluded) containing the name
as a token. *unfold* = files where the name is used as a rewrite rule: `unfold`/`delta`, or a bare
item in a `rw`/`simp only`/`simp_rw`/`dsimp only`/`nth_rw`/`rwa`/`simpa only` list. An unfold only
costs something when the unfolded body changes shape over ℝ; the column "form change" says whether
it does.

---

## 0. The strategy in one paragraph

Every vocabulary definition is generalised so that at `𝕜 := ℝ` it is **definitionally equal** to
the current one (tested for every critical case: `Qᴴ ≡ Qᵀ`, `star x ⬝ᵥ v ≡ x ⬝ᵥ v`, `RCLike.re` and
`star` on ℝ are identities, `(σ i : ℝ) ≡ σ i`, the L2 instance is the same term). Lemma statements
that contain no `ᵀ` or dot product are generalised in place and nothing downstream notices. A
lemma whose statement contains `ᵀ` becomes a general `conjTranspose` lemma (Mathlib naming) and the
real `ᵀ` statement **keeps its current name** as a one-line corollary (`by simpa using …`, since
`Matrix.conjTranspose_eq_transpose_of_trivial` is `@[simp]`). Each changed unfolding gets an ℝ bridge
lemma proved by `rfl`. Only three patterns then break downstream: `rw [hQ]` with
`hQ : HasOrthonormalCols Q` on a `Qᵀ` goal, unfolding a definition whose body gained `star`/`re`/`ᴴ`
(`quadForm`, `frobInner`, `residual`, `pinvL/R`, `rayleighQuotient`, `HasOrthonormalCols`), and
`IsSVD` field uses. All three have a mechanical fix. Predicted repair: about 100 files (range
100–130), against about 170 if the real lemmas are renamed instead (decision D1).

---

## 1. Inventory

### 1.1 Vocabulary generalised in stage A

| def (file) | current | proposed over `[RCLike 𝕜]` | ℝ specialisation | refs | unfold files (sites) | form change on unfold |
|---|---|---|---|---|---|---|
| `frobInner` (Norms/Core) | `∑ i, ∑ j, A i j * B i j : ℝ` | `RCLike.re (∑ i, ∑ j, star (A i j) * B i j) : ℝ` | rfl (tested) | 44 | 16 (34) | yes (`re`, `star`) |
| `frobSq` (Norms/Core) | `frobInner A A` | unchanged body | rfl | 93 | 29 (43) | no: `rw [frobSq, frobInner_eq_trace]` keeps working |
| `frobNorm` (Norms/Core) | `Real.sqrt (frobSq A)` | unchanged body | rfl | 61 | 11 (27) | no |
| `specNorm` (Norms/Core) | `‖A‖`, L2 op norm | same; `Matrix.instL2OpNormedAddCommGroup` is already `[RCLike 𝕜]` | same term (rfl, tested) | 156 | 13 (19) | no |
| `HasOrthonormalCols` (Subspaces/Projections) | `Qᵀ * Q = 1` | `Qᴴ * Q = 1` | rfl both ways (tested) | 165 | 12 (15) + `rw [hQ]` in 30 files (55 sites) | yes |
| `residual` (Projections) | `A - Q * (Qᵀ * A)` | `A - Q * (Qᴴ * A)` | rfl | 25 | 11 (20) | yes |
| `IsBestRankApprox` (Projections) | rank ≤ k ∧ frobSq-minimal | unchanged body | rfl | 8 | 0 | no |
| `quadForm` (Basic/QuadForm) | `z ⬝ᵥ (A *ᵥ z) : ℝ` | `star z ⬝ᵥ (A *ᵥ z) : 𝕜` | rfl (tested) | 60 | 29 (55) | yes (`star`) |
| `rayleighQuotient` (QuadForm) | `quadForm A x / (x ⬝ᵥ x)` | `RCLike.re (quadForm A x) / RCLike.re (star x ⬝ᵥ x) : ℝ` | rfl | 10 | 6 (10) | yes |
| `IsMoorePenroseInverse` (Basic/PenroseIdentities) | 4 Penrose identities with `ᵀ` | same with `ᴴ` | rfl | 5 | 0 | fields only |
| `moorePenroseInverse` (Basic/MoorePenrose) | `(exists_isMoorePenroseInverse A).choose` | same, existence via general SVD | defeq (proof irrelevance) | 45 | 0 | no |
| `pinvL` / `pinvR` (Basic/Pseudoinverse) | `(GᵀG)⁻¹Gᵀ` / `Gᵀ(GGᵀ)⁻¹` | `(GᴴG)⁻¹Gᴴ` / `Gᴴ(GGᴴ)⁻¹` | rfl | 13 / 16 | 4 / 3 | yes |
| `IsSVD` (Spectral/SVD, `Fin`) | fields `Uᵀ U = 1`, `Vᵀ V = 1`, `A = U Σ Vᵀ` | fields `conjTranspose_mul_left/right`, `eq : A = U Σ Vᴴ` | rfl | 17 | 0 | field names, `eq` shape |
| `rectDiag` (SVD) | `Matrix (Fin m) (Fin n) ℝ` | `Matrix (Fin m) (Fin n) 𝕜`, entries `(σ i : 𝕜)` | rfl, `simp [rectDiag]` ok (tested) | 37 | 1 | no |
| `kyFanNorm`, `nuclearNorm` (Norms/KyFanNorm) | singular-value sums | same over 𝕜 | rfl | 13 / 15 | 8 / 5 | no |
| `schattenNorm`, `schattenNormExtended` (Norms/Schatten) | same | same over 𝕜 | rfl | 9 / 6 | 5 / 1 | no |
| `conditionNumber` (Perturbation/ConditionNumber) | `specNorm A * specNorm A⁺` | same over 𝕜 | rfl | 12 | 4 | no |

Already general before this round: `singularValues` (RCLike, Fintype), `spectralTraceTail`,
`choleskyStep` (`[Field K]`), `dilation`, `sampledColumnMatrix`/`sampledRowMatrix`, the PSD
zero-diagonal and projector-trace lemmas.

**Design choices, with reasons.**

* **`frobInner` is real-valued (the real part).** All 44 consumer statements are real: `≤`, `|·|`,
  `IsGreatest`/`sSup` duality (nuclear, Schatten and Ky Fan duality, von Neumann), and the Pythagoras
  identities `frobSq (A+B) = frobSq A + 2 frobInner A B + frobSq B`. With `Re` they stay true
  verbatim over ℂ, because this is the inner product of the underlying real Hilbert space, Mathlib's
  `real_inner` situation. The 𝕜-valued pairing is `(Aᴴ * B).trace` and needs no definition of its
  own. Mathlib has no Frobenius inner product (checked), so nothing pushes the other way. The scalar
  lemmas `frobInner_smul_left/right` and `frobSq_smul` keep `c : ℝ`; rewriting with them at ℝ still
  matches despite the Algebra-vs-Mul `•` path (tested). The 𝕜-scalar version has `‖c‖ ^ 2`.
* **`quadForm` is 𝕜-valued, `star z ⬝ᵥ (A *ᵥ z)`.** This is exactly Mathlib's `PosSemidef`/`PosDef`
  characterisation (`Matrix.posSemidef_iff_dotProduct_mulVec`, `PosSemidef.dotProduct_mulVec_nonneg`,
  `posDef_iff_dotProduct_mulVec`). So `quadForm_nonneg` is a one-liner, and congruence and rank-one
  identities hold in 𝕜. Real-valued consumers take `RCLike.re`, as Mathlib does
  (`ContinuousLinearMap.reApplyInnerSelf`, `rayleighQuotient`). That makes `rayleighQuotient`
  real-valued and turns `matrixQuadraticFormReal A u` into `RCLike.re (quadForm A u)` by `rfl`. Over
  ℂ, `0 ≤ quadForm A z` needs `open scoped ComplexOrder` (tested: `LE 𝕜` fails otherwise). At ℝ the
  general lemma's `≤` is accepted by `linarith` (tested).
* **`HasOrthonormalCols Q := Qᴴ * Q = 1`.** At ℝ, `exact hQ`, `have h : Qᵀ * Q = 1 := hQ` and
  `show Qᵀ * Q = 1 from hQ` all keep working (tested), and so does passing `hQ` to a lemma whose
  hypothesis is `Qᵀ * Q = 1`. What breaks is `rw [hQ]` and `simp only [hQ]` on a goal containing
  `Qᵀ * Q`, because `rw` sees through the definition but finds `Qᴴ * Q` (tested). The fix is
  `rw [hQ.transpose_mul_self]`.
* **`specNorm` is free.** The scoped L2 instance is already RCLike, and the real term is the same.
  Mathlib has `Matrix.l2_opNorm_conjTranspose` but **no** `l2_opNorm_transpose` (checked). The
  general `specNorm_transpose` therefore needs a short proof, for example through `Aᵀ = (Aᴴ).map star`
  or through `singularValues`.
* **`IsSVD` keeps `Fin` indices** (D10). The proof of `exists_isSVD` is already written with
  `inner`, `eigenvectorBasis` and `exists_orthonormalBasis_extension_of_card_eq`, all RCLike in
  Mathlib. Generalising it touches about 80 lines (`inner 𝕜`, `(σ : 𝕜)` casts, `field_simp`) and
  subsumes `ComplexSquareSingularBasis` and `ComplexRectangularSVD`.

### 1.2 Definitions outside stage A

| def | current | plan |
|---|---|---|
| `schurComplement` (Basic/GeneralizedSchurComplement) | `C - Bᵀ A⁺ B` | optional B3 (`Bᴴ`); 1 file |
| `bestRankFrobSq`, `singularValueTailSq`, `truncatedSVD`, `IsSVD.truncatedMatrix` (Spectral/EckartYoung) | ℝ | C6, free once `IsSVD`/`frobSq` are general; absorb `complexBestRankFrobSq`, `complexGramTail`, `complexTruncatedSVD` |
| `principalAnglesFintype`, `sinePrincipalAngles`, `tangentPrincipalAngles`, `sinThetaMax`, `tanThetaMax` (Subspaces) | `Pᵀ Q` | C7: `Pᴴ Q`, angles stay real; absorb `complexPrincipalAnglesFintype` |
| `subspaceTangent` (Subspaces/GraphTangent) | `U₂ᵀ x`, `Submodule ℝ` | C11: `ᴴ`, `Submodule 𝕜`; absorb `complexSubspaceTangent` |
| `krylovSpace`, `blockKrylovSpace`, `subspaceIterate`, `krylovGrade` (Krylov/Spaces) | `Submodule ℝ` spans | C11: `[Field K]`, rfl at ℝ; absorb `complexBlockKrylovSpace`, `complexSubspaceIterate` (D8) |
| `complexColumnProjector`, `complexColumnSpace` (Subspaces/ComplexVolumeProjection) | ℂ, `starProjection` | C2: prove `= B * moorePenroseInverse B`, delete (D11); 10 + 6 files |
| `complexCholeskyResidualStep` | ℂ | C9: `= choleskyStep (K := ℂ)` by `rfl` |
| `matrixQuadraticFormReal`, `matrixVectorSqNorm` (Probability/…/LocalSecondMoment) | ℂ | C12: `RCLike.re (quadForm A u)`, `‖A *ᵥ u‖²` |
| `polarFrame`, `orthonormalBasisMatrix`, `topEigenframe`/`sortedEigenframe`/`complementaryEigenframe`, `eigenvalueProjector`, `headColumns` | ℝ | optional B3; Mathlib's `eigenvectorBasis` and `CFC.sqrt` are RCLike. Do it only when a merge needs it |
| `sigmaMin`, `sigmaMinSq`, `lamMin` (Spectral/Core) | ℝ infima | **stay real** (D6); 24 refs, 11 in RandomMatrix; the general spelling is `singularValues A (card n - 1)` (`sigmaMin_eq_singularValues_last`) |
| `Stiefel` + orthogonal-group instances | ℝ, Haar | **stay real**; unaffected (`HasOrthonormalCols` at ℝ is definitional) |
| `IsQR`, `IsFullQR`, `IsUpperTrapezoidal`, `IsLU`, `IsCholesky`, and the LU/Cholesky/Householder/Givens/Gram–Schmidt/Hessenberg algorithms | ℝ | **stay real** (D9). `IsQR` is free to generalise later (no sign convention in the predicate; its `orth` field is `HasOrthonormalCols`) |
| `IsSubspaceEmbedding` (Sketching) | raw dot products, ℝ | **stays real** (D7): no vocabulary in its body, so it is untouched by stage A; 7 Sketching files need `HasOrthonormalCols` repairs |
| `IsLeastSquaresSolution`, `regularizedGram`/GramSoftMin family, `OrthogonallyInvariantNorm`/`SymmetricGauge`, `Majorized`, `planeRotation`, `mapAbsCondition`, Walsh/Hadamard/structured matrices | ℝ | stay real |
| `lambdaMax`, `lambdaMin`, `matrixExp`, `matrixLog`, `traceExp` (Functions/ExpLog) | ℂ-only, Tropp port | out of scope; could become RCLike later |

### 1.3 Other numbers

* `Xᵀ * X = 1` written raw: 76 files, 180 occurrences; 32 of these files never mention
  `HasOrthonormalCols`. All of them keep compiling (D4).
* `IsSymm` appears in 41 files (140 occurrences). The bridge `Matrix.isHermitian_iff_isSymm` is `@[simp]`
  and is already used 43 times. `orthogonalGroup n R` is Mathlib's `abbrev` for `unitaryGroup n R`, so
  general statements over `unitaryGroup` specialise syntactically.
* L2 operator scope: 370 opens. Complex-matrix files using `‖A‖` with it: 54 in Probability and 33 in
  Matrix outside the `Complex*` files. Frobenius scope `‖A‖`: 23 files. Four files open both scopes.
* Explicit `@`-applications of vocabulary: one (`@NLAlib.IsSVD`). Named-argument
  `rectDiag (m := _) (n := _)` sites that need a 𝕜 ascription: 12.

---

## 2. What stays real, what generalises

Heuristic classification of the 509 Matrix files (from the statement signatures in
`atlas/declarations.json` plus proof tokens; per-file list in `design.json` →
`matrix_file_classification`):

| area | already ℂ/RCLike | no scalar | real-essential (R) | general with work (W) | likely free (F) |
|---|---|---|---|---|---|
| Basic | 5 | 6 | 3 | 4 | 13 |
| Calculus | – | – | 1 | 4 | 6 |
| Factorizations | 1 | – | 15 | 13 | 8 |
| Functions | 4 | – | 4 | 4 | 9 |
| Inequalities | 4 | – | 31 | 10 | 36 |
| Norms | 2 | – | 4 | 14 | 15 |
| OperatorTheory | 6 | 1 | 2 | 4 | 6 |
| Perturbation | 6 | 1 | 9 | 22 | 27 |
| Spectral | 35 | 21 | 18 | 11 | 54 |
| Structured | – | – | 5 | 1 | 9 |
| Subspaces | 17 | – | 15 | 8 | 15 |
| **total** | **80** | **29** | **107** | **95** | **198** |

The heuristic over-counts F: for example, the `Real*` Schur and normal-form files land in F, but they
are intrinsically real. A curated list follows.

**Stays real** (the statement is about real structure):
- Real canonical forms: Spectral/Real\* (17 files), MatrixPowerReal, SimpleEigenvalueReal.
- Direct algorithms (ALGORITHM_CONVENTIONS): Factorizations/{LU\*, Cholesky\* except CholeskyStep,
  Householder, Givens, GramSchmidt, Hessenberg, QR\*, MaximumVolume\*, RankRevealing\*,
  StrongRankRevealingQR, Triangular, ScaledOrthogonal}. They use sign conventions, `|·|` pivoting
  and positive real diagonals.
- Entry order, real determinant inequalities, real-vector majorization: Inequalities/{Hadamard\*,
  Majorization\*, Fischer/Minkowski/OverlappingBlock/PrincipalOverlap determinants,
  ColumnDeterminantBound, LogDetConcavity, KyFanSums, VonNeumann, SeparatingPSDVector}.
- Real analysis in real parameters: Calculus/\*, PlaneRotation\*, MapConditioning, TracePowerConvexity.
- Measure, Haar and Gaussian: Stiefel, CanonicalQR, the measurability half of PolarFrame,
  Structured/\*Measurable, `sigmaMin`/`lamMin`, and all of Probability, RandomMatrix and Sketching.
- Structured real matrices (Walsh, Cauchy/Hilbert/Toeplitz/Hankel, circulant).
- Krylov methods (Lanczos, Arnoldi, Golub–Kahan, CG, GMRES, Gauss quadrature, spectral measure on ℝ).

**General for free** (field-agnostic statements and proofs; the ℝ statement becomes an instance):
the stage-A API, Norms/{Reindex, RankNorm, Schatten, SchattenComparison, SchattenProducts,
NuclearGram, NuclearPSD, KyFanNorm}, Basic/{PenroseIdentities, MoorePenroseProjector,
MoorePenroseRank, Selection}, Spectral/{SingularValueInvariance, SquareSingularBasis, SvdBlocks,
SvdPowers, SingularValueSpectrum, FiniteIndexTransport}, Subspaces/{CSDecomposition, CSRank,
CanonicalCS, OrthogonalBlockCompletion, RectangularGramIsometry, ObliqueProjectionBlocks,
ObliqueProjectionNorms, GramColumnDeterminant}, Functions/DiagonalFilter (once `rectDiag` is 𝕜),
and Perturbation/Pseudoinverse\*.

**General with work** (real inner-product or quadratic-form proofs): CourantFischer and its
consumers (Weyl, Interlacing\*, LowRankInterlacing, EigenvalueOrder), Projections (`IsSymm`
lemmas), GramIsometry, SVD existence, principal angles, Procrustes/Polar, Spectral/Core.

**Policy for stage B.** A real file is *converted* only when (a) it is vocabulary API, or (b) a
stage-C keeper needs it. Every other file is repaired and keeps its real statements. Further
conversion is opportunistic and tracked as follow-ups.

---

## 3. Conversion recipe

### 3.1 Per definition

| def | generalised definition | bridges added in stage A | typical user-site edit (real file) |
|---|---|---|---|
| `HasOrthonormalCols` | `Qᴴ * Q = 1` | `HasOrthonormalCols.conjTranspose_mul_self` (𝕜); ℝ: `HasOrthonormalCols.transpose_mul_self`, `hasOrthonormalCols_iff_transpose_mul_self` (`Iff.rfl`) | `rw [hQ]` → `rw [hQ.transpose_mul_self]`; `unfold HasOrthonormalCols at hQ` → `rw [hasOrthonormalCols_iff_transpose_mul_self] at hQ`; `have h : Qᵀ * Q = 1 := hQ` unchanged |
| `frobInner` | `re (∑∑ star a * b)` | 𝕜: `frobInner_eq_re_trace` (`= re (Aᴴ * B).trace`); ℝ: `frobInner_eq_trace` (old name, `simpa`), `frobInner_eq_sum_mul` (`rfl`) | `unfold frobInner` / `simp only [frobInner, …]` → `simp only [frobInner_eq_sum_mul, …]`; plain `simp [frobInner]` works unchanged at ℝ (tested) |
| `frobSq`, `frobNorm`, `specNorm` | unchanged bodies | 𝕜: `frobSq_eq_sum_norm_sq`, `frobSq_eq_frobenius_norm_sq`, `specNorm_conjTranspose`; ℝ: `frobSq_eq_sum_sq` (old) | none |
| `quadForm` | `star z ⬝ᵥ (A *ᵥ z)` | ℝ: `quadForm_eq_dotProduct` (`rfl`); 𝕜: `quadForm_nonneg` (`ComplexOrder`), `quadForm_conjTranspose_mul_mul` | `rw [quadForm]` / `simp only [quadForm, …]` → `quadForm_eq_dotProduct` (tested on the `quadForm_eq_sum` proof) |
| `rayleighQuotient` | `re (quadForm A x) / re (star x ⬝ᵥ x)` | ℝ: `rayleighQuotient_eq_div` (`rfl`) | same substitution |
| `residual` | `A - Q * (Qᴴ * A)` | ℝ: `residual_eq_sub_mul_transpose_mul` (`rfl`) | `rw [residual]` → `rw [residual_eq_sub_mul_transpose_mul]` |
| `pinvL`/`pinvR` | `ᴴ` | ℝ: `pinvL_eq_inv_transpose_mul_mul_transpose`, `pinvR_eq_transpose_mul_inv` (`rfl`) | `unfold pinvL` → `rw [pinvL_eq_…]` |
| `IsSVD` | fields `conjTranspose_mul_left/right`, `eq` with `Vᴴ` | ℝ theorems `IsSVD.transpose_mul_left/right` (old names, so dot notation still resolves), `IsSVD.eq_mul_transpose` | `h.eq` → `h.eq_mul_transpose` where a `Vᵀ` shape is rewritten; `{ transpose_mul_left := … }` → anonymous constructor |
| `IsMoorePenroseInverse` | two `ᴴ` symmetry fields | ℝ corollaries for the two symmetric fields under the old names | as for `IsSVD` |
| `rectDiag` | `(σ i : 𝕜)` entries | `rectDiag_apply` general | add `(𝕜 := ℝ)` or a type ascription at the 12 named-argument sites |
| `ᵀ`-shaped API lemmas (about 70: 55 with `transpose` in the name in Core/Projections/QuadForm/Penrose/MoorePenrose\*/Pseudoinverse/SVD, plus `⬝ᵥ` ones) | general version named with `conjTranspose`/`star` | ℝ version keeps the current name and statement: `by simpa using <general>` | none |

### 3.2 Writing a generalised lemma

Add `variable {𝕜 : Type*} [RCLike 𝕜]`. Replace `ᵀ` by `ᴴ` and the `transpose_*` lemmas by
`conjTranspose_*`. Watch `conjTranspose_smul` (it introduces `star c`) and
`Matrix.vecMul_conjTranspose`/`dotProduct_mulVec` (they introduce `star`). Order-valued statements
take `RCLike.re` or `open scoped ComplexOrder`. Then add the ℝ corollary if a downstream file
rewrites with the old statement. `Proto.lean` contains worked examples: `frobInner_comm`,
`frobInner_eq_re_trace`, `frobSq_eq_sum_norm_sq`, `frobSq_eq_zero_iff`,
`conjTranspose_mul_residual`/`transpose_mul_residual`, `frobInner_mul_residual`, `quadForm_nonneg`.

### 3.3 Pitfalls (all checked or counted)

1. **`rw` with a definition-typed hypothesis.** `rw [hQ]` unfolds `HasOrthonormalCols` but now finds
   `Qᴴ * Q`, so it fails on `ᵀ` goals (30 files). Definitional uses (`exact`, `have`, `show`, lemma
   arguments) keep working.
2. **`simp only` / `rw` unfoldings leave `star` and `RCLike.re`** in real goals. Use the ℝ bridge
   lemma, or add `star_trivial, RCLike.re_to_real` to the simp set. Full `simp` normalises both and
   also normalises `ᴴ` to `ᵀ` (`conjTranspose_eq_transpose_of_trivial` is `@[simp]`).
3. **Order on 𝕜.** `0 ≤ (x : 𝕜)` needs `open scoped ComplexOrder` (`RCLike.toPartialOrder` is scoped).
   At ℝ the general statement interoperates with `linarith` (tested).
4. **Norm instances.** `specNorm` and `frobNorm` hide the instance choice. Files that open both
   `Matrix.Norms.L2Operator` and `Matrix.Norms.Frobenius` (4 files) have ambiguous `‖A‖`; the merged
   statements should use the named vocabulary. The scoped L2 instances for ℝ and for 𝕜 are the same
   declaration, so there is no diamond. `NormedRing` (square) and `NormedAddCommGroup` give the same
   norm, as before. `CFC.sqrt`/`CFC.log` on 𝕜-matrices need the same scopes as on ℂ today (see the
   `matrixLog` retirement notes).
5. **Scalars.** A real-scalar lemma `(c : ℝ) • A` with `A : Matrix m n 𝕜` rewrites fine at ℝ (tested).
   Keep real-scalar statements under the old names; the 𝕜-scalar ones carry `‖c‖`.
6. **Casts.** `rectDiag` entries `(σ i : 𝕜)`, `RCLike.ofReal` in statements; at ℝ the simp lemma
   `RCLike.ofReal_real_eq_id` and `rfl` close them (tested). The complex twins' `.map Complex.ofReal`
   wrappers become unnecessary inside the merged statements. The real↔complex transport lemmas
   (`singularValues_map_ofReal`, `map_ofReal_mul`, `norm_map_ofReal_eq_specNorm`) stay as bridges.
7. **`Fintype.card` vs `Fin`.** `IsSVD`, `rectDiag`, `EckartYoung` and the complex twins are
   `Fin`-indexed and `singularValues` is Fintype. Do not change index types in this round; keep the
   existing `simpa only [Fintype.card_fin]` glue.
8. **Implicit 𝕜.** It is inferred from the matrix argument everywhere except numerals and
   named-argument-only applications (`specNorm (1 : Matrix n n ℝ)` is already ascribed in the tree;
   the 12 `rectDiag (m := …)` sites need checking). There is one explicit `@NLAlib.IsSVD`.
9. **`IsSymm` vs `IsHermitian`.** General statements use `IsHermitian`. Real callers with `IsSymm`
   pass `Matrix.isHermitian_iff_isSymm.mpr` (`@[simp]`, already used 43 times).
10. **`omit` lints.** New section variables trigger `unusedSectionVars`; add `omit … in` as the files
    already do.

---

## 4. Staged plan with file ownership

At most four Lean-loading agents at once. Agents build only their own modules
(`lake build NLAlib.Matrix.…`). Only the coordinator runs full `lake build`s.

### Stage A: vocabulary and API (13 files, 3 agents, three steps)

| step | agent α | agent β | agent γ |
|---|---|---|---|
| A-1 (no NLAlib imports between them; parallel) | `Matrix/Norms/Core` (frobInner, frobSq, frobNorm, specNorm; 690 lines, 570 dependents) | `Matrix/Basic/QuadForm` (quadForm, rayleighQuotient; 114 lines, 261 dependents) | `Matrix/Basic/PenroseIdentities` (IsMoorePenroseInverse; 223 lines, 241 dependents) |
| A-2 (each imports only Norms/Core; parallel, after α's A-1) | `Matrix/Subspaces/Projections` (HasOrthonormalCols, residual, IsBestRankApprox; 486 lines, 422 dependents) | `Matrix/Basic/Pseudoinverse` (pinvL, pinvR; 188 lines) | `Matrix/Spectral/SVD` (rectDiag, IsSVD, general `exists_isSVD`; 511 lines, 341 dependents) |
| A-3 (after A-2) | `Matrix/Perturbation/ConditionNumber` (statements only, after γ) | `Matrix/Norms/{KyFanNorm, Schatten}` (definitions) | `Matrix/Basic/{MoorePenrose, MoorePenroseProjector, MoorePenroseRank, MoorePenroseTransformations}` (moorePenroseInverse) |
| A-4 | coordinator: one full `lake build`; compare failures with `design.json` → `stageA_predicted_breakage` | | |

Each stage-A file gets: general definitions, general API (conjTranspose names), the ℝ `rfl` bridges
of §3.1, and ℝ corollaries under the current names for every `ᵀ`-shaped lemma used downstream. The
heavily rewritten ones are `frobInner_eq_trace` (23 files), `frobSq_mul_left_of_orthonormal` (14),
`mulVec_dotProduct_mulVec_self` (13), `frobSq_transpose` (9), `residual_eq_one_sub_mul` (8),
`transpose_rectDiag_mul_rectDiag` (6) and `moorePenroseInverse_eq_pinvL` (5).

**Predicted downstream breakage after stage A: 100 files**, listed in `design.json` with reasons and
waves. Allow 100–130 for heuristic misses. By area: Matrix/Spectral 16, Subspaces 12,
Perturbation 12, Inequalities 11, Norms 6, Factorizations 5, Structured 4, Calculus 2, Functions 1,
Basic 1, Sketching 7, LowRank 7, Krylov 6, Estimation 5, RandomMatrix 4, Probability 1. By cause:
`rw [hQ]` 29, quadForm unfold 28, frobInner unfold 15, IsSVD 15, HasOrthonormalCols unfold 11,
residual 10, rayleighQuotient 6, pinvL/R 5. If the real lemmas were renamed instead (no
corollaries), the count would be 172.

### Stage B: repair, then selective conversion

* **B0** (one agent, no Lean). Apply the §3.1 substitutions to the 100 predicted files.
* **B1 Matrix repair** (about 70 files). The broken files form 10 dependency waves; wave sizes are 19,
  16, 6, 15, 16, 12, 9, 4, 2 and 1, spread across areas. Use three agents by subdirectory group:
  {Basic, Norms, Spectral}, {Subspaces, Factorizations, Structured, Calculus, Functions} and
  {Inequalities, Perturbation, OperatorTheory}. A file is claimed once its broken ancestors build.
  The coordinator's full build after each wave yields the next wave's error list: Lake builds every
  module whose imports succeeded.
* **B2 downstream repair** (about 30 files), after Matrix is green: Krylov 6, Probability 1,
  RandomMatrix 4, Sketching 7, LowRank 7, Estimation 5. Use two agents in layer order:
  {Krylov, Probability, RandomMatrix, Sketching}, then {LowRank, Estimation, Solvers}. Several of
  these files are in early waves because their broken ancestors are few, so B2 can overlap B1 once
  their ancestors are green.
* **B3 selective conversion** (about 20 files, optional, parallel by subdirectory). Convert the
  vocabulary API files and the stage-C prerequisites listed in §2 ("general for free"). Every
  converted file keeps ℝ corollaries for names used by real files.

### Stage C: merge the ℝ/ℂ twin families

45 `Complex*` files (5,393 lines, all except ComplexQZ) are losers or are renamed into keepers. Only 7
non-twin files import them: HermitianPart, HoffmanWielandtNormal, NormalBlocks, SchurFrobenius,
UnitaryBlockCompletion, LeverageSampling, SamplingMultiplication.

| id | family | keeper | losers | difficulty | needs |
|---|---|---|---|---|---|
| C1 | Frobenius | Norms/Core | Norms/ComplexFrobenius, ComplexFrobeniusTrace; the 23 Frobenius-scope files restate `‖A‖^2` as `frobSq` when touched | easy | A |
| C2 | projections, projection bounds, column projector, full-row inverse | Subspaces/{Projections, ProjectorTrace, ProjectionGaps, GramColumnDeterminant}, Basic/Pseudoinverse | Subspaces/{ComplexProjectionBounds, ComplexProjectionComposition, ComplexVolumeProjection, ComplexVolumeProjectorTrace, ComplexGramColumnDeterminant}, Basic/ComplexFullRowInverse; fix importers HoffmanWielandtNormal, NormalBlocks, SchurFrobenius | medium | A, C1, D11 |
| C3 | Gram isometry, block completion | Subspaces/{GramIsometry, RectangularGramIsometry, OrthogonalBlockCompletion} over `unitaryGroup` | ComplexGramIsometry, UnitaryBlockCompletion | easy–medium | A |
| C4 | SVD, singular transport | Spectral/{SVD, SquareSingularBasis, SingularValueInvariance} | ComplexSquareSingularBasis, ComplexRectangularSVD, ComplexSingularTransport (its `map ofReal` bridges move to FiniteIndexTransport); merges `complex_singularValues_{isometry_mul, mul_unitary, zero_eq_norm}` and the three singular-basis existence statements | medium | A-2 |
| C5 | Courant–Fischer, variational principle, trace tail | Spectral/CourantFischer over 𝕜 (`re (quadForm A x)`, `Submodule 𝕜`; ℝ corollaries for Weyl and interlacing) | ComplexRayleigh, ComplexVariationalPrinciple, ComplexVariationalExtrema, Inequalities/ComplexTraceTail | **hard** (~650 lines, P_spectral #35) | A |
| C6 | Eckart–Young, best rank approximation | Spectral/EckartYoung over 𝕜 | ComplexEckartYoung, ComplexGramTruncation, ComplexBestRankApproximation, ComplexVolumeSpectrum | medium–hard | C1, C2, C4 |
| C7 | CS, oblique projections, complex principal angles | Subspaces/{CSDecomposition, CSRank, CSToolkit, CanonicalCS, ObliqueProjection{Blocks, Canonical, Secant, Spectrum, Norms}, Oblique{CanonicalSpectrum, ComplementSpectrum, FrameInverse}, PrincipalAngle\*} | ComplexCS{Decomposition, Rank, Toolkit}, ComplexOblique{Blocks, Canonical, Secant, Spectrum}, ComplexIdempotentRealForm, ComplexFrameTransport | **hard** | C3, C4 |
| C8 | diagonal filter | Functions/DiagonalFilter | ComplexDiagonalFilter (its `map ofReal` algebra lemmas move to ForMathlib) | easy | A-2 |
| C9 | RPCholesky | RCLike versions of LowRank/Cholesky/Complex{CholeskyHistories, RandomPivotedCholesky}, renamed; CholeskyStep | Factorizations/ComplexCholeskyPivot (`= choleskyStep`, `rfl`); real CholeskyHistories (~45 declarations become corollaries); plan in docs/dedup/P_randnla.md | medium–hard | C5 (TraceTail) |
| C10 | volume sampling | LowRank/Sampling complex stack over 𝕜 | real VolumeSampling (or the Complex\* names after renaming) | medium | C2, C6 |
| C11 | subspace iteration, block Krylov, polynomial filter | Krylov/Spaces/{Basic, Block, Grade} over `[Field K]`, GraphTangent, LowRank/RangeFinding/SubspaceConvergence, PolynomialMethods/PolynomialFilter | Krylov/Spaces/ComplexBlock, ComplexSubspace{Convergence, Angles}, ComplexPolynomialFilter{, Bounds} | medium–hard | C2, C8 |
| C12 | complex Hermitian form in Probability | `RCLike.re (quadForm A u)` | `matrixQuadraticFormReal`, `matrixVectorSqNorm` (4 files) | easy | A-1 |
| C13 | misc pairs | Inequalities/Schur (`RCLike.re (A i i)`), Norms/Core `abs_dotProduct_mulVec_le_specNorm` (𝕜, `re`), Basic PSD trace lemmas | ComplexDiagonalMajorization (importer HermitianPart), Perturbation/ComplexEmbedding (importer LeverageSampling), ComplexPosSemidefTrace | easy | A |
| – | ComplexQZ | stays: RealQZ is a different theorem | – | – | – |

**Parallel tracks for stage C** (disjoint files, at most four agents):

* Wave C-α: track 1 does C4; track 2 does C1 then C2; track 3 does C5; track 4 does C8, C12 and C13.
* Wave C-β: track 1 does C6; track 2 does C3 then C7 (needs C4); track 3 does C9; track 4 does C11.
* Wave C-γ: C10.

Shared files with a single owner: SingularValueInvariance belongs to C4 (C7 reads it) and
ProjectorTrace to C2 (C6 reads it). After each wave: run
`python3 scripts/reorg.py --gen-aggregators` for deleted files, then `ExtractDecls` +
`sync_atlas.py`, and write a rename map `docs/renames/2026-10-xx-rclike.json`.

---

## 5. Risks and decisions for the owner

* **D1: ℝ corollaries.** Keep about 70 thin `ᵀ`-statement lemmas under their current names, with
  the general lemma taking the `conjTranspose` name, or rename everything? Recommendation: keep them
  (Mathlib precedent `real_inner_*`). This means about 100 repaired files instead of about 170 and no
  rename map in stage A. Delete corollaries whose callers all became general at the end of the round.
* **D2: `frobInner` real part.** Recommendation: yes. The 𝕜-valued pairing is `(Aᴴ * B).trace`.
* **D3: `quadForm` 𝕜-valued, `rayleighQuotient` real-valued.** Recommendation: yes. The
  alternative, a real-part `quadForm`, would also be definitional at ℝ but departs from Mathlib's
  `PosSemidef` shape.
* **D4: raw `Qᵀ * Q = 1`** (76 files, 180 occurrences; 32 files never mention the predicate).
  Recommendation: leave them, since they compile unchanged. Do not introduce a real abbreviation
  (that would be a second spelling). Normalise only in files that are touched.
* **D5: complex `‖A‖`.** Recommendation: statements in merged Matrix/LowRank files use
  `specNorm`/`frobSq`/`frobNorm`, and the 23 Frobenius-scope files follow. CFC/exp/log/Tropp-port and
  Probability keep the L2 `‖A‖` (normed-algebra use; about 87 files). This needs a STANDARDS §3
  edit, which currently prescribes `‖A‖` for complex matrices.
* **D6: `sigmaMin`/`lamMin`/`sigmaMinSq` stay real.** Recommendation: yes.
* **D7: `IsSubspaceEmbedding` stays real.** Recommendation: yes. It has no vocabulary in its body,
  Sketching is the randomized real layer, and only 7 Sketching files need repairs.
* **D8: Krylov.** Recommendation: generalise only `krylovSpace`, `blockKrylovSpace`,
  `subspaceIterate` (and optionally `krylovGrade`) to `[Field K]`. This is definitional at ℝ and
  needed for C11. The processes, solvers and quadrature stay real.
* **D9: factorization predicates stay real** (IsQR free later). Recommendation: yes.
* **D10: `IsSVD` stays `Fin`-indexed** this round. Recommendation: yes.
* **D11: column projector.** `B * moorePenroseInverse B` is canonical; delete `complexColumnProjector`.
  Recommendation: yes.
* **D12: merge direction for RPCholesky and volume sampling.** Recommendation: RCLike keepers built
  from the complex stacks, with real statements as corollaries.
* **D13: atlas.** Tags stay on the generalised definitions. The informal text of 12 definition entries
  says ℝ: orthonormal-columns-def, residual-def, quadform-def, matrix-norms-def, pseudoinverse,
  svd-def, svd, best-rank-approx-def, condition-number-def, principal-angles-def, ky-fan-norms-def,
  schatten-norms-def. Stage C moves tags from losers to keepers for courant-fischer,
  cs-decomposition, volume-sampling, rpcholesky, subspace-iteration-convergence,
  polynomial-filter-range-finder and block-krylov-subspace. ComplexCSToolkit carries the full
  `cs-decomposition` tag, which ties into the open toolkit-tag policy question.
* **D14: real theorem statements keep `ᵀ`.** Recommendation: yes. `ᵀ` is the ℝ simp normal form.

Risks:

* The heuristic breakage list misses `show`/`conv`/`calc`-step shapes and `decide`-style closes; that
  is why the range is 100–130.
* `specNorm_transpose` over 𝕜 needs a new proof (Mathlib has none).
* C5 and C7 are the long poles. C5 rewrites about 650 lines of Courant–Fischer; C7 needs C3 and C4
  first.
* Full rebuilds are expensive: Norms/Core has 570 dependents. Batch all of stage A before the first
  full build.
* Proof irrelevance makes `moorePenroseInverse` at ℝ definitional only up to the existence proof.
  Nothing unfolds it (0 sites), so this is harmless.
* `CFC.sqrt` in a generalised `polarFrame` needs the MatrixOrder/L2 scopes, the same issue as the
  `matrixLog` retirement.

---

## 6. Summary

* **Plan.** (A) Generalise 20 definitions in 13 files, in three steps of three parallel agents, each
  definitional at ℝ, with ℝ bridges and old-name ℝ corollaries. (B) Pre-apply mechanical
  substitutions, repair about 100 files in dependency waves (Matrix first, then Krylov, Probability,
  RandomMatrix, Sketching, LowRank and Estimation), and convert only vocabulary API and stage-C
  prerequisites (about 20 files). (C) Merge 13 twin families in three waves of up to four parallel
  tracks. The hard ones are Courant–Fischer (C5) and CS/oblique (C7).
* **Blast radius.** Stage A edits 13 files. Stage B repairs 100–130 files and converts about 20.
  Stage C deletes or merges 45 `Complex*` files (5,393 lines), generalises about 55 keeper files and
  updates 7 external importers. Optionally, 23 Frobenius-scope files are respelled. Docs and atlas:
  STANDARDS §3, DEDUP_FOLLOWUP, 12 atlas definition texts, tag moves for 7 ids, and a rename map.
  In total about **230 files touched (≈21% of 1106)**, 45 files removed.
* **Decisions needed:** D1 (ℝ corollaries vs renames), D3 (`quadForm` 𝕜-valued), D4 (leave raw
  `Qᵀ Q = 1`), D5 (`specNorm` vs `‖A‖` for complex; STANDARDS edit), D8 (Krylov spaces only),
  D11/D12 (merge directions), D13 (atlas texts and tag moves). D2, D6, D7, D9, D10 and D14 are
  recommendations that need only a nod.
