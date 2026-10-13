# Matrix layer: things an outside reader will find odd

Read-only review of `NLAlib/Matrix/**` (branch `nlalib-f2`, 2026-10-13), written for a numerical
analyst reading the atlas, the docs, or `atlas/declarations.json`. Line numbers are the
declaration lines recorded in `atlas/declarations.json` (the docstring start; the `def`/`theorem`
keyword is a few lines lower). Signatures are quoted from that file with universes dropped.
Every item gives **why** a reader stumbles and the **fix** at port time, or "intentional, document".
The order is roughly how likely a reader is to notice.

## Top 10

1. **Two different norms print as `‖A‖`.** `frobNorm_eq_norm : frobNorm A = ‖A‖`
   (Norms/Frobenius.lean:465) and `specNorm_eq_norm : specNorm A = ‖A‖` (Norms/Core.lean:54) look
   contradictory, because the scoped instance does not show in a signature. The same applies to
   `frobenius_norm_sq_eq_diagonal_add_off_diagonal : ‖T‖ ^ 2 = …` (Spectral/SchurFrobenius.lean:64,
   Frobenius) and `exists_mem_spectrum_distance_le_norm_perturbation_of_normal : … ‖ν - μ‖ ≤ ‖E‖`
   (Perturbation/BauerFike.lean:110, operator 2-norm). The core itself states results with `‖H‖`
   (`abs_re_star_dotProduct_mulVec_le_norm`, Norms/Core.lean:425;
   `norm_mulVec_sq_bounds_of_norm_gram_sub_one_le`, :445), although STANDARDS §3 says the core uses
   `specNorm`. A `‖`-applied-to-a-capital pattern occurs in about 110 Matrix theorem signatures (most of them matrix norms).
   *Fix:* outside the two bridge lemmas, matrix norms in statements are always `specNorm`/`frobNorm`,
   and a lint rejects `‖` applied to a `Matrix` in a signature.
2. **`conditionNumber` is finite for singular matrices.**
   `def conditionNumber (A : Matrix m n 𝕜) : ℝ := specNorm A * specNorm (moorePenroseInverse A)`
   (Perturbation/ConditionNumber.lean:25). This gives κ(0) = 0 (`conditionNumber_zero`, :31) and
   σ₁/σ_r for rank-deficient `A` (`conditionNumber_eq_singularValues_ratio`, :110). GVL §2.6.2
   defines κ(A) = ∞ for singular square A. The definition is tagged `(partial)` and needs
   `[DecidableEq m]`. *Fix:* either rename it to make the meaning visible (`pinvConditionNumber`,
   or "effective condition number" in the docstring and the atlas), or make it `ℝ≥0∞`-valued with
   `⊤` off full rank. Keep the σ₁/σ_r formula as a theorem.
3. **Two independent notions of "smallest singular value / eigenvalue".**
   `def sigmaMin (A : Matrix m n ℝ) : ℝ := ⨅ x : {x // x ⬝ᵥ x = 1}, √((A *ᵥ x) ⬝ᵥ (A *ᵥ x))`
   (Spectral/Core.lean:61) is real-only. It is 0 for every wide matrix and for empty `n`, and it is
   never identified with `singularValues A (card n - 1)`: the module doc says "Follow-up: … not
   proved". There are also `lambdaMin`/`lambdaMax (A : Matrix d d ℂ) := sInf/sSup (spectrum ℝ A)`
   (Functions/ExpLog.lean:28/22), which are ℂ-only and junk for non-Hermitian A, and Mathlib's
   `hA.eigenvalues₀ ⟨Fintype.card n - 1, _⟩`, the official spelling per STANDARDS. Two theorems are
   still named `lamMin_eq_of_…` after the deleted definition and state the raw `⨅` instead
   (Spectral/SpectralMinimum.lean:21, :40). *Fix:* prove `sigmaMin A = singularValues A (card n - 1)`
   for tall A and then make `sigmaMin` an abbreviation of it (over 𝕜). Give the last eigenvalue one
   name (`IsHermitian.eigenvalueMin`, or `lambdaMin` defined from `eigenvalues₀`), and rename the
   `lamMin_*` lemmas.
4. **Singular values are 0-indexed, ℕ-indexed and zero-padded, and `IsSVD` is the full SVD only.**
   `singularValues A : ℕ → ℝ` (Spectral/SVD.lean:73) has `σ 0` largest, so textbook σ_{k+1} is
   `singularValues A k`, σ_r is `singularValues A (A.rank - 1)`, and Eckart–Young's tail starts at
   index `k`. `IsSVD A U V` (SVD.lean:327) forces `U : m × Fin p` to be unitary, so `p = card m`.
   There is no thin or compact SVD, which is the form HMT and most NLA papers use.
   `exists_isSVD` fills `p`, `q` by an auto-param `by first | exact Fintype.card_fin _ | rfl`
   (:347), which shows up in the signature. *Fix:* intentional (it avoids casts across shapes);
   document the off-by-one in the atlas `svd-def` entry and in every docstring that quotes a
   1-indexed source. At port, add an `IsThinSVD` (U : m × r, r = rank) predicate.
5. **Junk-value "equalities" carry atlas tags.**
   `specNorm_inv_self_mul_transpose_eq : specNorm (A * Aᵀ)⁻¹ = 1 / sigmaMin Aᵀ ^ 2` and
   `specNorm_pinvR_sq : specNorm (pinvR A) ^ 2 = specNorm (A * Aᵀ)⁻¹` (Spectral/Core.lean:609, :654)
   hold "for every real A" only because both sides are 0 when A Aᵀ is singular (`M⁻¹ = 0`,
   `1/0 = 0`). Both are tagged `atlas: pseudoinverse`. The same pattern appears elsewhere.
   `tanThetaMax` returns 0, meaning "aligned", exactly when the angle is π/2
   (Subspaces/PrincipalAngles.lean:56). `mapAbsCondition f x := ‖fderiv ℝ f x‖` gives condition
   number 0 at non-differentiable points (Perturbation/MapConditioning.lean:26). `pinvL`/`pinvR`
   are 0 on rank-deficient input (Basic/Pseudoinverse.lean:43/47). *Fix:* add the
   `IsUnit (A * Aᵀ)` hypothesis to the tagged statements (keep the total form as a `_total` helper).
   Make `tanThetaMax` `ℝ≥0∞`-valued, or require invertibility of `QᵀX`. Make
   `mapAbsCondition` require `DifferentiableAt`.
6. **The "spectral core" is not yet uniform.** STANDARDS §2 says the core is stated once over `𝕜`
   and `Fintype`. Still:
   - `Inequalities/Mirsky.lean` is ℝ and `Fin` (:25 `sum_abs_singularValues_add_sub_le_sum_prefix
     (A E : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin (min m n)))`), so the F1 acceptance grep
     prints four lines of it.
   - Mirsky's Frobenius inequality `sum_sq_singularValues_add_sub_le_frobSq` (Spectral/Weyl.lean:212)
     is ℝ-only because von Neumann `frobInner_le_sum_singularValues_mul` is `Fin`/ℝ
     (Inequalities/VonNeumann.lean:253).
   - `sigmaMin` and `eigenvalues₀_last_eq_iInf` in `Spectral/Core.lean` are ℝ-only.
   - `exists_unitary_complement` takes `Q : Matrix (Fin k) (Fin q) 𝕜` (Subspaces/Projections.lean:434).
   - The isometry invariances `singularValues_isometry_mul` etc. are ℝ-only
     (Spectral/SingularValueInvariance.lean:34).

   *Fix:* finish F1 on these, or remove Mirsky.lean from the core list.
7. **Orthonormality is spelled three ways, sometimes in one file.** `HasOrthonormalCols` lives in
   `Subspaces/Projections.lean:66`, downstream of `Norms`, so core norm lemmas take raw
   `(hP : Pᴴ * P = 1)` (`specNorm_le_one_of_orthonormal`, Norms/Core.lean:219;
   `specNorm_sub_mul_conjTranspose_mul_le`, :352, which spells `residual` by hand). The real twins
   `specNorm_mul_left_of_hasOrthonormalCols` and `specNorm_mul_transpose_right_of_hasOrthonormalCols`
   (Norms/SpectralNormBounds.lean:82, :90) take `(hP : Pᵀ * P = 1)`: the name says one thing and
   the hypothesis says another, and they are transpose twins that STANDARDS forbids. A third ℂ
   copy is `norm_mul_left_of_conjTranspose_mul_eq_one (hU : Uᴴ * U = 1) : ‖U * B‖ = ‖B‖`
   (Subspaces/ComplexProjectionBounds.lean:49). *Fix:* move `HasOrthonormalCols` and `residual`
   to `Matrix/Basic`, restate the core with them, delete the two twins and the ℂ copy.
8. **The factorizations look half-generalised.** The predicates take `[LinearOrder n]`
   (`IsLU`, LU.lean:43; `IsCholesky`, Cholesky.lean:38; `IsQR`, QR.lean:55), but every algorithm
   and every existence theorem is `Fin n` and ℝ. `exists_isCholesky_iff_posDef` (Cholesky.lean:223)
   says "general index follows by transport (not formalized here)". Symmetry is `A.IsSymm` in
   `choleskySucceeds_iff_posDef` (Cholesky.lean:208) but `A.IsHermitian` in `sylvester_criterion`
   (Spectral/SylvesterCriterionToolkit.lean:19), on the same objects. `givens i j c s` is the
   *transpose* of GVL's G(i,j,θ) (Givens.lean:47; documented, but surprising). *Fix:* intentional
   for the recursions; state the existence theorems for `[LinearOrder n]` via
   `Fintype.orderIsoFinOfCardEq`, use `IsHermitian` throughout, and adopt GVL's orientation for
   `givens`.
9. **Atlas-tagged bundles and `Fintype.equivFin` transports.** 64 Matrix theorems that merely
   conjoin other lemmas carry atlas tags. The largest are `davis_kahan_toolkit_properties`
   (Perturbation/DavisKahanToolkit.lean:16, a 5.9k-character signature), `ky_fan_norm_toolkit_properties`
   (5.4k) and `schatten_toolkit_properties` (4.8k). Statements like
   `singular_subspace_perturbation_bounds_fintype` (Perturbation/WedinFiniteIndex.lean:19, tagged
   `wedin-sin-theta`) hypothesise `IsSVD (reindex (equivFin m) (equivFin n) A) (reindex … U) …`,
   and `specNorm_moorePenroseInverse_eq_fintype` (Norms/RankNorm.lean:166) has
   `singularValues (reindex (equivFin m) (equivFin n) A)`. That reindex is a no-op now that
   `singularValues` is Fintype-generic. *Fix:* drop the bundles (manifest already plans it)
   and move their tags to the component theorems. Restate the transports directly on `m`, `n`.
10. **Citations a reader cannot follow.** There are 14 "(label to verify)" in core docstrings
    (Weyl.lean:77–111, :216; CourantFischer.lean:428, :483, :512; Cholesky.lean:242, :257). Over 100 docstrings
    (117 lines mention a "manuscript", 113 an `sa:`-style key) cite internal keys or unpublished notes ("manuscript `sa:volume`", "`rt:power`",
    "the matrix-toolkit operator manuscript, equations (19)–(20)", "Schur–Horn variational
    rederivation, equations (1),(6)"). There are 33 "Audit G0 B3"-style references. 155 files use
    "actual"/"genuine" ("the actual complex orthogonal projector", "a genuine norm"), which reads as
    defensive. *Fix:* resolve the labels before the atlas is advertised. Replace internal keys by
    published sources or drop them. Strip "actual/genuine" at port.

## 1. Definitions a mathematician would find odd

- **`frobInner A B : ℝ := RCLike.re (∑ i, ∑ j, star (A i j) * B i j)`** (Norms/Frobenius.lean:48).
  Over ℂ the Frobenius inner product is 𝕜-valued; this is its real part. Intentional: it makes
  `frobSq`, Pythagoras and the real-Hilbert-space arguments uniform. Document it in the atlas
  `matrix-norms-def` entry. At port, consider the name `frobInnerRe`, with a 𝕜-valued
  `frobInner` = `(Aᴴ * B).trace`.
- **`rayleighQuotient A x := re (quadForm A x) / re (star x ⬝ᵥ x)`** (Basic/QuadForm.lean:198),
  real-valued next to a 𝕜-valued `quadForm` (:42). Intentional (the Rayleigh quotient of a Hermitian
  matrix is real); document that it is meaningful only for Hermitian A.
- **`residual Q A := A - Q * (Qᴴ * A)`** (Subspaces/Projections.lean:70). In NLA "residual" means
  `b − Ax`. This is `(I − QQᴴ)A`, a projection only when `Q` is orthonormal, although the docstring
  says "after projecting". It also collides with Mathlib's root `residual` (comeager filter,
  `atlas/import_usage.json` collisions). *Fix:* `projResidual` or `orthCompl Q A`, kept in
  `NLAlib` and never `_root_`.
- **`IsBestRankApprox (k : ℕ) (C Y : Matrix m n 𝕜)`** (Projections.lean:74) is Frobenius-only, but
  the name does not say so. The spectral analogue is an `IsLeast` (`isLeast_specNorm_sub_of_rank_le`,
  Weyl.lean:200). The argument order is also inconsistent: `IsBestRankApprox k A Y` and
  `bestRankFrobSq k A` (EckartYoung.lean:336) against `singularValueTailSq A k` (:117) and
  `truncatedSVD A k` (:303). *Fix:* `IsBestFrobRankApprox`, with `A` first everywhere.
- **`IsSVD.truncatedMatrix (_h : IsSVD A U V) (k : ℕ)`** (EckartYoung.lean:230) takes a proof it
  never uses (dot notation only). `truncatedSVD` (:303) is `(exists_isSVD A).choose…`, so it is
  not canonical when σ_k = σ_{k+1}. `singularValueTailSq` sums over `range (card m)`, not
  `min m n`, which looks asymmetric. Intentional; document all three.
- **`moorePenroseInverse A := (exists_isMoorePenroseInverse A).choose`**
  (Basic/MoorePenrose.lean:106) is defined by choice. Uniqueness makes it well defined, but readers
  expect the formula `V Σ⁺ Uᴴ`. Intentional; state `moorePenroseInverse_eq_svd` prominently.
- **`specNorm [DecidableEq n]`** (Norms/Core.lean:50) and **`singularValues [DecidableEq n]`**
  (SVD.lean:73). Both inherit the instance from Mathlib's `toEuclideanLin`. Intentional; the
  docstring already explains `specNorm`, and `singularValues` should say the same.
- **Three rectangular-diagonal constructors.** `rectDiag (σ : ℕ → ℝ) : Matrix (Fin m) (Fin n) 𝕜`
  (SVD.lean:207), `rectangularDiagonal (x : Fin (min m n) → ℝ)` (Norms/RectangularDiagonal.lean:18),
  and `rectangularDiagonalMatrix (x : Fin (min (card m) (card n)) → ℝ) : Matrix m n ℝ :=
  (rectangularDiagonal x).reindex (Fintype.equivFin m).symm …` (Norms/InvariantNormRepresentation.lean:123).
  The last one is a "diagonal" whose position depends on an unspecified `equivFin`. There is also
  `diagonalSequence` (Inequalities/VonNeumann.lean:103), the inverse operation. *Fix:* keep
  `rectDiag`; express the gauge results through it. Note that FOUNDATIONS_BRIEF §1, which "wins",
  still prescribes an `equivFin`-indexed `rectDiag : Matrix m n 𝕜`, contradicting decision E′
  and STANDARDS §3. Update the brief.
- **`principalAnglesFintype (P Q : Matrix m n ℝ) : Fin (card n) → ℝ := arccos (singularValues
  ((Pᵀ*Q).reindex (equivFin n) (equivFin n)) i)`** (Subspaces/PrincipalAngleDefinitions.lean:19).
  The name carries the index type, the reindex is redundant, it is ℝ-only (ℂ twin
  `complexPrincipalAnglesFintype`, ComplexObliqueSecant.lean:16), and `arccos` silently clamps for
  non-orthonormal frames. *Fix:* `principalAngles`, without the reindex, over 𝕜, taking frames as
  hypotheses in the theorems.
- **`sinThetaMax Q X := specNorm (residual Q X)`** (PrincipalAngles.lean:49) is asymmetric. It is
  the sine of the largest angle only when `X` is orthonormal and has at most as many columns as
  `Q`; otherwise it is just a number. Intentional (index-free); document this in the def and the
  atlas.
- **Four Schur-complement / elimination-step definitions.** `schurComplement A B C := C - Bᵀ *
  moorePenroseInverse A * B` (Basic/GeneralizedSchurComplement.lean:35) is ℝ-only and only for
  the symmetric block `[[A,B],[Bᵀ,C]]`, though its name is fully general. There is also
  `pivotSchur` (Basic/SchurComplement.lean:35, `Fin (n+1)`), `choleskyStep A t` (CholeskyStep.lean:35:
  any field, but it is a Gaussian-elimination step, not Cholesky), and `complexCholeskyResidualStep`
  (ComplexCholeskyPivot.lean:20), which is `choleskyStep` by `rfl`. *Fix:*
  `generalizedSchurComplement` (𝕜, `Bᴴ`); keep `pivotSchur`; rename `choleskyStep` to
  `eliminationStep`; delete the ℂ copy.
- **`IsUpperHessenberg (H : Matrix (Fin n) (Fin n) ℝ)`** (Structured/Hessenberg.lean:31) and
  `IsTridiagonal` (:37) are tagged `atlas: givens-rotation-def`. They are ℝ and `Fin` although
  they are pure zero patterns, while `IsUpperQuasiTriangular` (Spectral/QuasiTriangular.lean:16)
  is over any `[Zero K]`. *Fix:* state them over `[LinearOrder n] [Zero α]` like Mathlib's
  `IsUpperTriangular`, and retag them `hessenberg-def`.
- **Leading minors, four ways.** `leadingSubmatrix A k (hk : k ≤ n)` (Factorizations/LU.lean:97,
  takes a proof); `leadingMinor M k` (Spectral/Inertia.lean:200, junk 0 for k > m);
  `trailingMinor` (SylvesterCriterion.lean:17); `principalMinor A S` (Inequalities/PrincipalMinorProducts.lean:17).
  *Fix:* one `leadingSubmatrix` with a `Fin`-free index, `leadingMinor := det ∘ leadingSubmatrix`,
  both in `Basic`.
- **Prefix sums of sorted values, three ways.** `eigenvaluePrefix hA (hk : k ≤ card n)`
  (Inequalities/KyFan.lean:21), `sumLargest x k` (Majorization.lean:29), `kyFanNorm A k`
  (Norms/KyFanNorm.lean:26). `kyFanNorm` is itself defined with the spelling STANDARDS forbids,
  `A.toEuclideanLin.singularValues i`, and is called a norm at `k = 0`. *Fix:* define the first
  and third through `sumLargest` or the `singularValues` API.
- **Schatten: two spellings and an unrestricted exponent.** `schattenNorm A (p : ℝ)` (Schatten.lean:28)
  is defined for every real `p`, with junk at `p = 0`. `schattenNormExtended A (p : ℝ≥0∞)` (:37)
  is the one that matches Bhatia. `schattenSeminorm p hp` and `schattenInvariantNorm p hp` are
  further spellings. *Fix:* a single `schattenNorm (p : ℝ≥0∞)`.
- **Rotations, three ways.** `givens i j c s` (Givens.lean:47), `givensRotation i j x` (:139), and
  `planeRotation u v c s` (Inequalities/PlaneRotation.lean:18, "Schur–Horn variational rederivation").
  *Fix:* `planeRotation` is the basis-free one; define `givens` as its coordinate case.
- **Two eigenprojectors with near-identical names.** `eigenvalueProjector hA ℓ : Matrix n n ℝ`
  (Perturbation/EigenspaceProjector.lean:21) projects onto the whole eigenspace of `ℓ`.
  `eigenProj A hA i : Matrix d d ℂ` (Functions/HermitianCalculus.lean:299) is the rank-one
  projector onto the i-th eigenvector. *Fix:* `eigenspaceProjector` against
  `eigenvectorProjector`, over 𝕜.
- **`sortedEigenframe hA := eigenvectorUnitary.submatrix id (Fintype.equivOfCardEq (card_fin _))`**
  (Spectral/Eigenframes.lean:17) is correct only because it reproduces Mathlib's internal
  definition of `IsHermitian.eigenvalues`. `complementaryEigenframe` takes an unused `_hk` (:43).
  *Fix:* use `hA.eigenvectorBasis` with `eigenvalues₀` order directly, and document the coupling.
- **`complexColumnProjector B`** (Subspaces/ComplexVolumeProjection.lean:24) is the only
  definition of the orthogonal projector onto `range B`. It is ℂ-only and lives in a
  volume-sampling support file. Real code spells the projector `A * moorePenroseInverse A` or
  `Q * Qᴴ`. *Fix:* `rangeProjector` over 𝕜 in `Subspaces/Projections`, with
  `rangeProjector_eq_mul_moorePenroseInverse`.
- **`OperatorConvexOn I f`** quantifies over `∀ d (_ : NeZero d) (A H : Matrix (Fin d) (Fin d) ℂ)`
  (OperatorTheory/Basic.lean:27). `Fin d` is the right universe-safe encoding, but `NeZero d` is
  superfluous and the definition is ℂ-only. Intentional apart from `NeZero`; document it.
- **Algorithms with total junk.** `lu`, `cholesky` (LU.lean:158, Cholesky.lean:114) return junk
  via `x/0 = 0` and `√(neg) = 0`, and `cholesky` on `n = 0` returns `A`. `LUSucceeds` also
  demands the n-th pivot ≠ 0 although `A = LU` needs only n−1 (LU.lean:170). Intentional, per
  ALGORITHM_CONVENTIONS; already documented.

## 2. Theorem statements weaker, stranger or more hypothesis-laden than the textbook

- **Weyl with a redundant hypothesis.** `IsHermitian.eigenvalues₀_add_le (hA : A.IsHermitian)
  (hB : B.IsHermitian) (hAB : (A + B).IsHermitian) (i j : Fin (card n)) (hij : ↑i + ↑j < card n) :
  hAB.eigenvalues₀ ⟨i + j, hij⟩ ≤ …` (Spectral/CourantFischer.lean:362). `hAB` follows from `hA`,
  `hB`. The same applies to `hB : (Qᴴ * A * Q).IsHermitian` in the compression lemmas (:404, :426).
  Intentional (eigenvalues₀ depends on the proof term); add `_of_add` variants that use
  `hA.add hB`.
- **Smallest-eigenvalue statements.** `eigenvalues₀_last_eq_iInf (hM : M.IsHermitian)
  (hn : 0 < card n) : hM.eigenvalues₀ ⟨card n - 1, _⟩ = ⨅ …` (Spectral/Core.lean:209) is ℝ-only
  inside the 𝕜 core and needs the index arithmetic in every consumer. `conditionNumber_eq_eigenvalues₀_ratio
  [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosDef)` (ConditionNumber.lean:128) is ℝ-only next to
  𝕜 siblings. *Fix:* a named last eigenvalue (Top 10 #3).
- **`conditionNumber_eq_singularValues_ratio (hr : 0 < A.rank)`** (ConditionNumber.lean:110):
  the hypothesis exists only because κ(0) = 0 (Top 10 #2).
- **Existence theorems over `Fin` for `Fintype` predicates.** `exists_isLU_of_forall_det_ne_zero`,
  `exists_isLU_iff_forall_det_ne_zero` (LU.lean:311, :320), `exists_isCholesky_iff_posDef`,
  `exists_eq_mul_transpose_of_posSemidef` (Cholesky.lean:223, :256), `exists_isFullQR` (QR.lean:398),
  `invariantNorm_sub_polar_le_sub_isometry_fin` (Factorizations/NearestPolar.lean:102, tagged
  `polar-decomposition`). A reader sees the predicate generalised and the theorem not.
- **SVD-shaped results via `equivFin`.** `exists_orthogonal_transpose_mul_mul_eq_diagonal_singularValues
  : ∃ V W, … Vᵀ * A * W = diagonal fun i => singularValues A ↑(equivFin p i)` (Spectral/SquareSingularBasis.lean:18)
  orders the diagonal by an unspecified bijection. *Fix:* derive it from `IsSVD` and drop it.
- **Atlas tags on results that are not the tagged theorem.** `dense_separable_charpoly`
  (Spectral/SeparableCharpolyDensity.lean:55), a density result, is tagged `schur-triangularization`.
  `frobenius_norm_sq_eq_diagonal_add_off_diagonal` (SchurFrobenius.lean:64) is also tagged
  `schur-triangularization`. `sinThetaMax`, `regularizedGram` and similar helpers get atlas
  *definition* ids (`inverse-power-gram-def`, Calculus/GramSoftMin.lean:25). *Fix:* retag as
  helpers; atlas definitions should be concepts a reader would look up.
- **Mirsky, named and placed oddly.** `Inequalities/Mirsky.lean` holds Bhatia IV.3.4 (weak
  majorization of |σ(A+E) − σ(A)| by σ(E)) and is tagged `lidskii (partial)`. "Mirsky's
  inequality" in the Frobenius form lives in `Spectral/Weyl.lean:212`, tagged `weyl-mirsky`.
  *Fix:* rename the file `SingularValueMajorization` and retag it.
- **`(B - A).PosSemidef` hypotheses** survive in 7 files (Inequalities/HadamardOrder.lean:46, :73;
  Inequalities/HadamardExponential.lean:58; Basic/GeneralizedSchurComplement.lean:142, :261, :282;
  Factorizations/CholeskyStep.lean:185; Factorizations/ComplexCholeskyPivot.lean:103;
  Spectral/SpectralMinimum.lean:21; Inequalities/TraceTail.lean:142) against the `≤` rule.
- **Least squares in three vocabularies.** `exists_least_squares_angle` (Perturbation/LeastSquaresAngle.lean:52)
  is stated with `Matrix.toEuclideanLin` and `EuclideanSpace` norms. `leastSquaresCos/Tan/Eta`
  (LeastSquaresCoordinateBounds.lean:16–30) are defined with `Real.sqrt (v ⬝ᵥ v)`.
  `IsLeastSquaresSolution` (Basic/LeastSquares.lean:36) uses dot products. All are ℝ-only.
  *Fix:* one vector-norm spelling (§3).

## 3. Vocabulary inconsistencies that survive

- **Matrix norms:** `specNorm`/`frobNorm` against raw `‖A‖` in roughly 110 Matrix signatures,
  including core files (Norms/Core.lean:425, :445; Norms/Frobenius.lean:454
  `frobenius_norm_sq_eq_sum_norm_sq` restating a Mathlib fact with Frobenius `‖·‖`), the ℂ
  `Functions`/`OperatorTheory` files (allowed by the CFC exemption), `Subspaces/ComplexProjectionBounds` (11),
  `Perturbation/BauerFike`, `Spectral/MatrixPowerBounds`.
- **Vector 2-norm, three spellings:** `‖WithLp.toLp 2 x‖` (23 files, including Norms/Core.lean:418
  `norm_toLp_sq_eq_re_star_dotProduct`), `√(x ⬝ᵥ x)` (12 files; `sigmaMin` itself), and unit
  vectors as `{x // x ⬝ᵥ x = 1}` (17 files). *Fix:* pick `‖WithLp.toLp 2 x‖` (or a local
  `vecNorm`) and give `sigmaMin` the same.
- **Symmetric real matrices:** `.IsSymm` in 35 theorem signatures across 17 files, against
  `.IsHermitian` in about 240 real-only signatures across 72 files. Both appear in
  `Perturbation/EigenspaceProjector` and `Spectral/SylvesterCriterion`.
- **Orthonormal columns:** `HasOrthonormalCols` (~480 uses) against raw `Pᴴ * P = 1` or `Pᵀ * P = 1`
  hypotheses in about 40 statements (a few private), including the core (Top 10 #7),
  `Structured/KroneckerSpectrum.lean:21, :36`, `Spectral/SpectralMinimum.lean:40`, and
  `Factorizations/QR.lean:206`.
- **Transpose in real leaves:** Factorizations, Perturbation and Inequalities state `Aᵀ * A`,
  `IsUnit (Aᵀ * A)`, `Qᵀ * A * Q` (`trace_compression_le_eigenvaluePrefix`, Inequalities/KyFan.lean:27),
  next to core lemmas stated with `ᴴ`. Expected for frozen leaves, but a reader comparing two
  adjacent atlas entries sees two conventions.
- **Deprecated names still used in proofs:** `mul_moorePenroseInverse_isSymm` (about 10 call
  sites, e.g. Inequalities/VonNeumann.lean:39, Perturbation/PseudoinverseProjectors.lean:27),
  `specNorm_le_one_of_isSymm_of_isIdempotentElem` (8), `mul_transpose_mul_eq_of_range_le` (7),
  `exists_orthogonal_completion` (4). They are not in statements, but they will warn at port.
- **`_fintype` / `_fin` / `Fin` suffixes** naming an index type: `principalAnglesFintype`,
  `complexPrincipalAnglesFintype`, `specNorm_moorePenroseInverse_eq_fintype`,
  `singular_subspace_perturbation_bounds_fintype`, `exists_cholesky_of_posSemidef_fintype`,
  `det_cauchyMatrix_eq_vandermonde_fintype`, `invariantNorm_sub_polar_le_sub_isometry_fin`,
  `toSymmetricGaugeFin`, `walshMatrixFin`. *Fix:* one statement per result, named for its content.
- **`ℝ` names for 𝕜 objects and vice versa:** `OrthogonallyInvariantNorm` (Norms/InvariantNorm.lean:21,
  ℝ, a bundled `Seminorm` rather than a norm class) carries the atlas id
  `unitarily-invariant-norm-def`. `HasOrthonormalCols.toLinearIsometry` is ℝ-only
  (Subspaces/OrthogonalProducts.lean:76). At port the generic version should take the
  "unitarily" name.

## 4. Structural oddities

- **Subdirectories are topics, not layers, but their names suggest layers.** `Basic/MoorePenrose`
  imports `Spectral/SVD`. `Spectral/SpectralMinimum` imports `Calculus/GramSoftMinSpectral`.
  `Spectral/EigenframeDecomposition` imports two `Perturbation` files. `Norms` imports
  `Inequalities` 12 times. `Basic/` holds theorem files (CauchyBinet, JacobiMinor,
  GeneralizedSchurComplement, RankInequalities). *Fix:* either document that only `Matrix` as a
  whole is a layer, or enforce `Basic < Norms < Spectral < …` in `check_layers.py` at port.
- **`Matrix/Calculus` is one proof.** Nine of eleven files (GramSoftMin, InversePower*,
  UnshiftedGramSoftMin, GramCutoffCalculus, GramTrace) are the deterministic half of
  `wishart-lambda-min-tail`. Their only consumers are `RandomMatrix/Gaussian/InverseMoments/*` and
  `Wishart/SimpleSpectrum`, and they mint atlas "definitions" such as `inverse-power-gram-def`.
  `Structured/GramSoftMinMeasurable.lean` belongs to the same proof. The manifest keeps 9 of
  them as files. *Fix:* move them next to the consumer
  (`RandomMatrix/Gaussian/Wishart/SoftMin*.lean`); keep only `DeterminantDerivative*` in Calculus.
- **Files whose content does not match the name or directory:** `Inequalities/Mirsky.lean` (see
  §2). `Structured/{Measurable,SpectralMeasurable,GramSoftMinMeasurable}` are measurability, not
  structured matrices (F2 rebuilds the first two). `Perturbation/MapConditioning.lean` is about
  general normed spaces and belongs in ForMathlib or a `Conditioning` area.
  `OrthogonallyInvariantNorm.transpose` is defined in `Factorizations/NearestPolar.lean:172`, not
  `Norms/InvariantNorm`. `realMatrixComplexification` and its Loewner/CFC API sit in
  `Spectral/Core.lean:689` (a `loewner-heinz-real` helper) inside the extreme-singular-value file.
  The inverse-Gram norm identities also live in `Spectral/Core`.
- **Definitions far from their API.** `HasOrthonormalCols`/`residual` sit in `Subspaces/Projections`
  but are needed by `Norms` (hence raw hypotheses). `leadingMinor` is in `Spectral/Inertia` but used
  by LU and Sylvester. `lambdaMin`/`lambdaMax`/`matrixExp`/`matrixLog`/`traceExp`
  (Functions/ExpLog.lean) are ℂ-only definitions that the whole concentration layer uses, away from
  `Spectral`. `IsUpperHessenberg` (Structured) and `IsHessenbergForm` (Factorizations/Hessenberg.lean:45)
  are split.
- **`Complex*` files that are vocabulary twins, not topics:** 15 under `Subspaces/` (CS
  decomposition, oblique projections, projection bounds, volume projector) plus
  `Basic/ComplexFullRowInverse`, `Basic/ComplexPosSemidefTrace`, `Norms/ComplexFrobeniusTrace`,
  `Factorizations/ComplexCholeskyPivot`, `Functions/ComplexDiagonalFilter`,
  `Inequalities/ComplexDiagonalMajorization`. They are outside F1, but an atlas reader sees two of
  each concept (`complexColumnProjector`, `complexPrincipalAnglesFintype`, `complex_cs_decomposition_properties`).
- **Size skew:** `Spectral/` has 128 files (15.3k lines), 17 of them `Real*` files (mostly real Schur and
  normal-form variants). `Inequalities/` has 80 files. A reader browsing by directory sees `Spectral`
  as everything.
- **Docs disagree with code:** FOUNDATIONS_BRIEF §1 (which "wins") specifies the `equivFin`
  `rectDiag : Matrix m n 𝕜` and says `ls Matrix/Spectral/Complex*` must be empty, but
  `Spectral/ComplexQZ.lean` is present (STANDARDS exempts it; the brief does not). The F1 acceptance
  grep fails on `Inequalities/Mirsky.lean` today.
