# F1b-α: Fintype SVD (decision E′), twin deletions, FiniteIndexTransport

Date: 2026-10-13. Status: done. `lake build NLAlib.Matrix NLAlib.LowRank NLAlib.Sketching
NLAlib.Probability` completes (4875 jobs) with β's concurrent EckartYoung/CourantFischer/Weyl work
in the tree. `scripts/check_names.py`: OK; `scripts/check_layers.py`: OK.

## Decision (owner, 2026-10-13): E′

`IsSVD {p q : ℕ} (A : Matrix m n 𝕜) (U : Matrix m (Fin p) 𝕜) (V : Matrix n (Fin q) 𝕜)` with
`m n` arbitrary `Fintype`s; `rectDiag (σ : ℕ → ℝ) : Matrix (Fin p) (Fin q) 𝕜` stays positional;
`exists_isSVD` fills `p = card m`, `q = card n` by an auto-param.

Justification.
* The brief's `rectDiag` via `Fintype.equivFin` cannot carry the promised `@[simp]` `Fin` form:
  `Fintype.equivFin α = (truncEquivFin α).out` is `Quot.out` (choice), so `equivFin (Fin a)` is an
  unspecified permutation and `rectDiag` at `Fin` would be a permuted diagonal (§0 below).
* Mathlib precedent: sorted spectral data are indexed by `Fin (card n)` /`ℕ`
  (`Matrix.IsHermitian.eigenvalues₀ : Fin (card n) → ℝ`, `LinearMap.singularValues : ℕ →₀ ℝ`),
  while the `n`-indexed `eigenvalues = eigenvalues₀ ∘ equivFin` loses the order. Singular vectors
  are ordered data, so their column index is `Fin p`; rows are the arbitrary `m`, `n`.
* With free `p q` and the auto-param `by first | exact Fintype.card_fin _ | rfl`, Fin callers get
  square `Fin a` factors and keep every statement unchanged (measured in §1).

**Acceptance-grep exemption.** The brief's `grep -rl "Matrix (Fin" …` must exempt `rectDiag` (its
type is `Matrix (Fin p) (Fin q) 𝕜`, and type ascriptions of it) and the `Fin p` column index of SVD
factors. In my files every remaining `Matrix (Fin` is a `rectDiag` ascription or a docstring.

## 0. The brief's `rectDiag` decision cannot be implemented as written

`Fintype.equivFin α` is `(Fintype.truncEquivFin α).out`, i.e. `Quot.out`, i.e. `Classical.choice`.
So `Fintype.equivFin (Fin a)` is an *unspecified* permutation of `Fin a`; it is not provably
`Equiv.refl` / `finCongr (card_fin a).symm`. With

```lean
rectDiag σ : Matrix m n 𝕜 := of fun i j =>
  if (equivFin m i : ℕ) = equivFin n j then (σ (equivFin m i) : 𝕜) else 0
```

the promised `@[simp]` lemma "at `Fin`, `rectDiag σ i j = if (i : ℕ) = j then σ i else 0`" is
unprovable (it is independent: a model may pick a non-identity permutation). This is the same wart
as Mathlib's `Matrix.IsHermitian.eigenvalues = eigenvalues₀ ∘ equivFin`. The `IsSVD`/`rectDiag`
index change is on hold until the owner decides; the measurements below are for that decision.

## 1. Options measured

Population: 48 files outside `Spectral/SVD.lean` mention `rectDiag`, `IsSVD` or `exists_isSVD`
(358 lines). 35 `obtain … := exists_isSVD …` sites; 42 `(h : IsSVD A U V)` hypotheses in public
statements across 16 files; `rectDiag_apply` used 40 times in 18 files. 35 of the 48 files
compute *positionally* (`rectDiag_apply`, `Fin.castLE`, `Fin.ext`, `(i : ℕ) = j`,
`headColumns`/`tailColumns`, `IsSVD.apply`, `transpose_mul_self` with `diagonal fun j => σ j ^ 2`);
13 use the SVD only abstractly (`h.eq`, unitarity, `singularValues_eq_of_eq_mul_rectDiag_mul`).

### (A) `equivFin`-indexed, `U : Matrix m m 𝕜`, `V : Matrix n n 𝕜` (brief-literal)

* At `Fin` indices the meaning changes: the `k`-th singular vector is column
  `(equivFin m).symm k`, `Aᴴ A = V diag(σ (equivFin j)²) Vᴴ`, `rectDiag s : Matrix (Fin k) (Fin k)`
  is `diagonal (s ∘ equivFin)`.
* Breakage: all 35 positional files fail in proofs. About 10 of them also have **statements**
  that become false or must be rewritten with `equivFin` (examples below), e.g.
  `InverseOverlapGram.rectDiag_square_eq_diagonal`, `SingularFrames.IsSVD.mul_headColumns`
  (head columns of `U` are no longer the leading singular vectors), `RealDilation.rectDiag_mul_rectDiag`
  proofs (`Fin.ext` on `(i : ℕ) = j`), `SvdPowers.IsSVD.gram_pow_mul` (proof), `IsSVD.apply`
  (`U i (castLE k)` becomes `U i ((equivFin _).symm (castLE k))`).
* Typical repair: re-prove over `Fintype` with `equivFin` arithmetic, i.e. generalise the leaf
  (forbidden by the freeze), or restate the leaf with `equivFin` (statement change). The 13
  abstract files need little or nothing.
* Includes β's EckartYoung/Weyl/Mirsky/Interlacing, which are positional (truncation by
  `if i < k`, `headColumns`).

### (E) Mathlib-style sorted index, `U : Matrix m (Fin (card m)) 𝕜` (coordinator's proposal)

* `rectDiag : Matrix (Fin p) (Fin q) 𝕜` stays positional (so `Spectral/SVD.lean` keeps
  `Matrix (Fin` in the acceptance grep).
* At `Fin a`, `Fintype.card (Fin a)` is **not** definitionally `a` for a variable `a`
  (`List.length (List.finRange a)`), so `U : Matrix (Fin a) (Fin (card (Fin a)))`. Every Fin user
  that writes `{U : Matrix (Fin m) (Fin m) ℝ} (h : IsSVD A U V)` (42 hypotheses, 16 files) or uses
  `obtain ⟨U, V, h⟩ := exists_isSVD A` and then `U` at type `Matrix (Fin m) (Fin m)` (35 sites)
  breaks at the type level; repair is a `finCongr (card_fin _)` reindex at every site. Large.

### (E′) refinement of (E): free column sizes `p q : ℕ` (recommended)

```lean
structure IsSVD {p q : ℕ} (A : Matrix m n 𝕜) (U : Matrix m (Fin p) 𝕜) (V : Matrix n (Fin q) 𝕜)
  -- fields: Uᴴ * U = 1, Vᴴ * V = 1, A = U * rectDiag (singularValues A) * Vᴴ,
  --         plus U * Uᴴ = 1, V * Vᴴ = 1 (equivalently p = card m, q = card n)
theorem exists_isSVD (A : Matrix m n 𝕜) {p q : ℕ}
    (hp : Fintype.card m = p := by first | exact Fintype.card_fin _ | rfl)
    (hq : Fintype.card n = q := by first | exact Fintype.card_fin _ | rfl) :
    ∃ (U : Matrix m (Fin p) 𝕜) (V : Matrix n (Fin q) 𝕜), IsSVD A U V
```

* Tested (`/tmp/f1ba/Auto.lean`): with this auto-param, `obtain ⟨U, V, h⟩ := exists_isSVD A` at
  `A : Matrix (Fin a) (Fin b)` yields `U : Matrix (Fin a) (Fin a)` (the tactic unifies `p := a`),
  and at general `m` yields `U : Matrix m (Fin (card m))`.
* At `Fin` every existing statement keeps its meaning and type (`m := Fin a`, `p := a`):
  `rectDiag_apply`, `IsSVD.apply`, `headColumns U`, `diagonal fun j => σ j ^ 2` unchanged.
* Breakage: only anonymous constructors / destructuring of `IsSVD` (two extra fields):
  `SingularFrames.IsSVD.transpose` (`refine ⟨_, _, ?_⟩`) and any `obtain ⟨hU, hV, h⟩ := h`
  (grep: ≤ 5 sites), and uniqueness `singularValues_eq_of_eq_mul_rectDiag_mul*` gains
  `U * Uᴴ = 1`-type hypotheses only for non-square-typed `U` (Fin callers pass square `U`, the
  lemma keeps a square form). Estimated < 10 sites, all mechanical.
* Generic users (the `_fin` + `reindex` pattern) can then apply `exists_isSVD` directly at `m n`
  and the private `*_fin` lemmas become deletable file by file.
* Cost: `rectDiag` and `Matrix m (Fin p)` keep `Fin` in layer 0 (inherent to sorted singular
  values indexed by `ℕ`, like `eigenvalues₀`); the brief's grep must exempt `rectDiag`.


## 2. `Spectral/SVD.lean` (owned)

* `singularValues`, its API, `sq_singularValues_eq_eigenvalues₀` unchanged (proof now uses Mathlib
  `sq_singularValues_of_lt`, not `sq_singularValues_fin`).
* Moved into the general section and restated over `Fintype`: `rank_eq_card_singularValues_ne_zero`
  (`range (min (card m) (card n))`; Fin users add `Fintype.card_fin` after the rewrite, 1 site).
* New, general (F1 needs): `singularValues_map_ofReal` (over 𝕜, `A.map (algebraMap ℝ 𝕜)`; replaces
  the ℂ lemma of ComplexSingularTransport), `mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one`
  (`card m = p`, `UᴴU = 1 ⇒ UUᴴ = 1`), `card_eq_of_conjTranspose_mul_eq_one` (trace),
  `IsSVD.card_left/right`.
* `rectDiag` section: unchanged (positional; `rectDiag_apply`, `rectDiag_apply_ofReal`,
  `rectDiag_eq_of`, `transpose/conjTranspose_rectDiag`, products, `rectDiag_add`).
* `conjTranspose_mul_self_of_orthonormalBasis`: basis indexed by any `ι`, space `EuclideanSpace 𝕜 m`.
  Its 0-use real twin `transpose_mul_self_of_orthonormalBasis` is deleted (renames file).
* `IsSVD` fields, in order: `conjTranspose_mul_left`, `conjTranspose_mul_right`, `eq`,
  `mul_conjTranspose_left`, `mul_conjTranspose_right` (the last two were theorems; names kept).
* `exists_isSVD` proved once over 𝕜 and `Fintype` directly (eigenbasis of `AᴴA` indexed by
  `Fin (card n)`, orthonormal completion indexed by `Fin (card m)`); no `Fin` base case, no
  reindexing.
* API restated over E′: `mul_right`, `conjTranspose_mul(_mul)`, `conjTranspose_eq`,
  `conjTranspose_mul_self`, `mul_conjTranspose_self`, `apply_eq_sum_mul_star` (`Fin (min p q)`),
  `eq_head_add_tail_mul_conjTranspose`, and the real forms (`transpose_mul_left/right`,
  `eq_mul_transpose`, `mul_transpose_left/right`, `transpose_mul(_mul)`, `transpose_eq`,
  `transpose_mul_self`, `mul_transpose_self`, `apply`, `eq_head_add_tail`).
* `eigenvalues₀_eq_of_eq_mul_diagonal_mul`: `W : Matrix n (Fin q)`, extra `hq : card n = q`
  (0 outside users). Uniqueness `singularValues_eq_of_eq_mul_rectDiag_mul(_conjTranspose)`: over
  `m n` with `U : Matrix m (Fin p)`, `V : Matrix n (Fin q)`, trailing auto-param
  `hq : card n = q`. Callers that used `apply …` followed by bullets must switch to `exact … (hk)`
  (the auto-param changes goal order): 2 sites repaired.
* Acceptance: `grep _fin\b` 0 hits (only `card_fin`); `Matrix (Fin` only `rectDiag`/docstrings.

## 3. `Basic/MoorePenrose.lean` (owned) and `Basic/PenroseIdentities.lean`

* `IsSVD.isMoorePenroseInverse`, `IsSVD.moorePenroseInverse_eq` over E′.
* `exists_isMoorePenroseInverse` now `exists_isSVD A` directly (the `Fin (card)` reindex is gone).
* `IsMoorePenroseInverse.unitary_transform` widened to `U : Matrix p m`, `V : Matrix q n`
  (same proof, only `UᴴU = 1`, `VᴴV = 1` used); needed because SVD factors are not square-typed.
* Moved here from FiniteIndexTransport: `moorePenroseInverse_reindex`.
* The private rectDiag lemmas (`rectDiag_mul_reversed`, …) stay `Fin`-typed (rectDiag-exempt).

## 4. Deleted files and where their content went

| file | public declarations → replacement | users repointed |
|---|---|---|
| `Spectral/ComplexRectangularSVD` | `exists_complex_rectangular_svd` → `exists_isSVD` + `conjTranspose_mul_mul` | Subspaces/ComplexObliqueCanonical (5-line local `hSVD`) |
| `Spectral/ComplexSquareSingularBasis` | `exists_unitary_conjTranspose_mul_mul_eq_diagonal_singularValues` → `exists_isSVD` (columns reindexed by `equivFin`) | Subspaces/ComplexCSDecomposition (local `V := V₀.submatrix id ep`) |
| `Spectral/ComplexSingularTransport` | `singularValues_map_ofReal` → general in SVD.lean; `complex_singularValues_isometry_mul`/`_mul_unitary` → `singularValues_eq_of_gram_charpoly_eq` (inlined, 1 use); `complex_singularValues_zero_eq_norm` → `singularValues_zero_eq_specNorm`; `norm_map_ofReal_eq_specNorm` → `singularValues_zero_eq_specNorm` + `singularValues_map_ofReal`; `rank_eq_of_complex_real_singularValues_eq` → `singularValues_ne_zero_iff` + `eq_of_forall_lt_iff` | ComplexIdempotentRealForm, ComplexObliqueSecant (`show … = map (algebraMap ℝ ℂ) from rfl`), ComplexFrameTransport (imports only) |
| `Perturbation/ComplexEmbedding` | `norm_toLp_sq_eq_re_star_dotProduct`, `abs_re_star_dotProduct_mulVec_le_norm`, `norm_mulVec_sq_bounds_of_norm_gram_sub_one_le` → same names over 𝕜 in `Norms/Core` (`RCLike.re`) | ComplexSubspaceAngles, LeverageSampling (import only) |
| `Functions/RealComplexCFC` | `realMatrixComplexification` (+ `_apply`, `_le_iff`, `_cfc`, `_inv`, `posSemidef_…_iff`, `posDef_…`, `continuous_…`) → same names, `Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n 𝕜`, in `Spectral/Core` (section RealExtension; Spectral/Core now imports `Mathlib.Analysis.Matrix.Order`) | HermitianPartConverse, LoewnerHeinz, RelativeSpectrum: `(… (𝕜 := ℂ))` at each use (49 sites, mechanical) |
| `Norms/RealComplexNorm` | `specNorm_le_norm_map_ofReal`, `norm_toLp_ofReal_eq` → same names over 𝕜 in `Norms/Core` (`A.map (algebraMap ℝ 𝕜)`) | MatrixPowerReal (2), MatrixPowerBounded, SRHT, SRHTWithReplacement: typed `have … := specNorm_le_norm_map_ofReal (𝕜 := ℂ) …` |
| `Spectral/FiniteIndexTransport` | `mul_reindex` → `Norms/Reindex`; `moorePenroseInverse_reindex` → `Basic/MoorePenrose`; `specNorm_moorePenroseInverse_eq_fintype` → `Norms/RankNorm`; the five Eckart–Young declarations → β's `EckartYoung` (two kept general, three dropped by β) | Spectral aggregator, SquareSingularBasis, VonNeumann, ConditionNumber, ProjectionGaps, HansonWright, Sketching/…/FiniteIndexTransport, ComplexFrameTransport → `EckartYoung`+`RankNorm`+`Reindex`+`OrthogonalProducts`; OptimalError(Continuity) repointed by β |

Renames recorded in `docs/renames/2026-10-F1.json` (8 entries; moved-same-name declarations are not
renames and are not listed).

## 5. Private `*_fin` detours removed (generic users now call `exists_isSVD` at `m n`)

`frobSq_eq_sum_sq_singularValues_fin` (SingularValueSpectrum), `singularValues_zero_eq_specNorm_fin`
and `sigmaMin_eq_singularValues_last_fin` (SpectralBounds; `IsSVD.mulVec_dotProduct_mulVec_eq_sum`
widened to E′, same proof), `singularValues_transpose_fin` (SingularValueInvariance),
`singularValues_smul_of_nonneg_fin` (SingularValueScaling), `singularValues_mul_add_le_fin`
(ProductWeyl, on β's general `truncatedSVD`), `frobSq_le_rank_mul_specNorm_sq_fin` (RankNorm;
`frobSq_eq_sum_rank_singularValues_sq` widened, same proof),
`exists_trace_twoSided_compression_eq_kyFanNorm_fin` (KyFanAttainment),
`exists_orthogonal_pair_attaining_fin` (ProcrustesRotations; `IsSVD.frobInner_mul_rectDiag_mul_transpose`
widened to E′, same proof).

**Remaining `_fin` (not my files; each needs a leaf rewrite, i.e. widening a chain of `Fin`
public lemmas, so left per the freeze):** ProductSingularValues (`IsSVD.det_gram_mul_submatrix_eq_prod_sq_singularValues`
is `Fin`), KyFan, KyFanNorms, SchattenTrace, Schatten, NuclearNorm ×4 (`nuclearNorm_eq_sum_rank_singularValues`
is `Fin`), SchattenDuality ×2 (`IsSVD.schattenDualCoefficients_attain`/`schattenNorm_mul_rectDiag_mul_transpose`
are `Fin`), NearestPolar (public `invariantNorm_sub_polar_le_sub_isometry_fin`); not SVD-related:
HadamardDeterminantLower, GoldenThompson ×2, LiebConcavity. β's: Weyl, Mirsky, MirskyPadded.

## 6. Call-site repairs outside my files (minimal)

* IsSVD constructor (5 fields): SingularFrames `IsSVD.transpose`.
* Auto-param goal order: NearestPolar `singularValues_eq_one_of_hasOrthonormalCols`,
  ObliqueCanonicalSpectrum (explicit `(U := (1 : Matrix (Fin _) (Fin _) ℝ))`).
* `rank_eq_card_singularValues_ne_zero` now with `card`: SchattenDuality (+ `Fintype.card_fin`).
* Caused by β's EckartYoung (`singularValueTailSq` over `range (card m)`, `truncatedMatrix` with
  `Vᴴ`): SvdBlocks (`Fintype.card_fin`), SingularFrames ×2, SingularFrameTails
  (`Matrix.conjTranspose_eq_transpose_of_trivial` in `simp only`).
* Missing transitive import after twin deletion: ComplexObliqueSpectrum (+ `Functions.ComplexDiagonalFilter`).

## 7. Notes for the coordinator

* `scripts/AuditNewProofs.lean` still names the deleted modules `RealComplexCFC`, `ComplexEmbedding`,
  `FiniteIndexTransport`, `RealComplexNorm` in its selection list (harmless: they select nothing).
  `Perturbation/ConditionNumber` docstring still mentions `Spectral/FiniteIndexTransport` (cosmetic).
* The brief's `Matrix (Fin` acceptance grep over whole `Spectral/`/`Norms/`/`Basic/` directories
  also hits many non-core leaves unrelated to SVD (RealSchur*, Sylvester*, QuasiTriangular, …) and
  `Subspaces/Projections.lean` (`exists_unitary_complement`, `Fin k` frames); those are not F1b-α's.
* Pre-existing deprecation warnings at RankNorm l.127/144 (`IsSVD.moorePenroseInverse_eq_mul_conjTranspose`)
  were left (R2 policy).
