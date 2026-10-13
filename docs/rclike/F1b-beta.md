# F1b-β: Courant–Fischer, Weyl, interlacing, Eckart–Young, Mirsky over `RCLike`/`Fintype`

Date: 2026-10-13. Built against F1b-α's E′ `IsSVD` (`U : Matrix m (Fin p) 𝕜`, positional `rectDiag`).

```
lake build NLAlib.Matrix.Spectral NLAlib.Matrix.Inequalities NLAlib.Matrix.Perturbation \
  NLAlib.Matrix.Factorizations NLAlib.LowRank NLAlib.Krylov NLAlib.Matrix.Norms
Build completed successfully (4557 jobs).
```

No new warnings in any file I edited. Renames: 44 β entries in `docs/renames/2026-10-F1.json`
(re-read and merged; no clashes).

## Acceptance (my part)

```
$ ls NLAlib/Matrix/Spectral/Complex*
NLAlib/Matrix/Spectral/ComplexQZ.lean        # not an F1 twin (see "Remaining")
$ grep -rl "ℂ" NLAlib/Matrix/Spectral        # CourantFischer/EckartYoung appear only through "ℝ or ℂ" in docstrings; no file with an ℝ sibling except ComplexQZ/RealQZ
$ grep -n "Matrix (Fin\|_fin\b" NLAlib/Matrix/Spectral/{CourantFischer,Weyl}.lean   # 0
```

## 1. Courant–Fischer (`Spectral/CourantFischer.lean`), one statement over `{𝕜} [RCLike 𝕜] [Fintype n]`

Quadratic form `RCLike.re (quadForm A x)`, norm `RCLike.re (star x ⬝ᵥ x)`, subspaces
`Submodule 𝕜 (n → 𝕜)`. At ℝ both are definitionally `x ⬝ᵥ (A *ᵥ x)` / `x ⬝ᵥ x`. Lemmas taking
`hA : A.IsHermitian` are in `Matrix.IsHermitian` (`_root_`), so `hA.eigenvalues₀_add_le` works.

| name | content |
|---|---|
| `Matrix.IsHermitian.eigenvalues₀_le_of_forall_mem` | min-max half (codim ≤ k ⇒ `λ_k ≤ c`) |
| `Matrix.IsHermitian.le_eigenvalues₀_of_forall_mem` | max-min half (dim ≥ k+1 ⇒ `c ≤ λ_k`) |
| `Matrix.IsHermitian.exists_submodule_eigenvalues₀_mul_le`, `…exists_submodule_le_eigenvalues₀_mul` | attaining subspaces |
| **new** `Matrix.IsHermitian.eigenvalues₀_eq_iSup_iInf` | `λ_k = ⨆ S : {S // k+1 ≤ finrank S}, ⨅ x : {x // x ∈ S ∧ x ≠ 0}, rayleighQuotient A x` |
| **new** `Matrix.IsHermitian.eigenvalues₀_eq_iInf_iSup` | `λ_k = ⨅ W : {W // card n ≤ finrank W + k}, ⨆ x : {…}, rayleighQuotient A x` |
| `card_le_finrank_inf_add` | over 𝕜 |
| `Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_of_le` | Loewner monotonicity, hypothesis `A ≤ B` (`open scoped MatrixOrder`; a `(B - A).PosSemidef` term still elaborates, `Matrix.le_iff` is `Iff.rfl`) |
| `Matrix.IsHermitian.eigenvalues₀_add_le` | eigenvalue Weyl |
| `Matrix.IsHermitian.eigenvalues₀_compression_le`, `…eigenvalues₀_le_eigenvalues₀_compression` | interlacing for `Qᴴ * A * Q`, `HasOrthonormalCols Q` |
| **new** `Matrix.IsHermitian.eigenvalues₀_submatrix_le`, `…eigenvalues₀_le_eigenvalues₀_submatrix` | interlacing for `A.submatrix e e`, `e : r ↪ n`, Hermitian proof `hA.submatrix e` |
| `singularValues_le_of_forall_mem`, `le_singularValues_of_forall_mem`, `exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul`, `exists_submodule_sq_singularValues_mul_le_mulVec_dotProduct` | over 𝕜, forms `RCLike.re (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x))` |

The proof is the old real proof, ported: the coordinates are `star uⱼ ⬝ᵥ x`, and the expansion
`re q(x) = ∑ λⱼ ‖⟨uⱼ,x⟩‖²` comes from Mathlib's `conjStarAlgAut_star_eigenvectorUnitary`. The private
coordinate maps are now linear maps, not `Fin`-row matrices. `isHermitian_transpose_mul_self` (ℝ,
0 uses) is deleted. Its replacement is Mathlib's `isHermitian_conjTranspose_mul_self`.

Deleted: `ComplexVariationalPrinciple.lean`, `ComplexVariationalExtrema.lean`, `ComplexRayleigh.lean`
(ComplexRayleigh had no consumer besides the variational files). Also deleted:
`Inequalities/ComplexTraceTail.lean`, the ℂ twin of the Loewner/TraceTail wrapper (DESIGN C5). Its one
consumer, `LowRank/Cholesky/ComplexRandomPivotedCholesky`, now calls the general core
`sq_max_re_trace_sub_spectralTraceTail_le_of_eigenvalues₀_le` with
`Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_of_le`. The attained `IsGreatest`/`IsLeast` forms of
ComplexVariationalExtrema map to the equational forms plus the attaining-subspace lemmas.

## 2. Weyl (`Spectral/Weyl.lean`)

These are now over 𝕜 and `Fintype`: `singularValues_add_add_le`, `singularValues_add_le_add_specNorm`,
`singularValues_le_singularValues_add_add_specNorm`, `abs_singularValues_add_sub_le_specNorm`,
`singularValues_mul_le_specNorm_mul`, `singularValues_mul_le_mul_specNorm`, `singularValues_residual_le`
(`I − QQᴴ`), `singularValues_le_specNorm_sub_of_rank_le` and `isLeast_specNorm_sub_of_rank_le`
(no longer `Fin`). The proofs use Euclidean norms `‖WithLp.toLp 2 u‖`. `σ_k(AC) ≤ σ_k(A)‖C‖` is now
proved directly (the preimage of the min-max subspace under `C`), because `singularValues_transpose`
is ℝ-only. The eigenvalue Weyl inequality is `hA.eigenvalues₀_add_le` (§1).

## 3. Eckart–Young (`Spectral/EckartYoung.lean`), over 𝕜 and `Fintype m n`

`singularValueTailSq (A : Matrix m n 𝕜) k := ∑ i ∈ range (card m), if k ≤ i then σ_i² else 0`. At
`Fin a` use `Fin.sum_univ_eq_sum_range` and `Fintype.card_fin`. `IsSVD.truncatedMatrix` is
`U * rectDiag … * Vᴴ`. `truncatedSVD`, `isBestRankApprox_truncatedSVD`, `IsSVD.frobSq_sub_truncatedMatrix`,
`IsSVD.specNorm_sub_truncatedMatrix`, `specNorm_sub_truncatedSVD_eq`, `bestRankFrobSq`,
`bestRankFrobSq_eq_singularValueTailSq` and `frobSq_sub_truncatedSVD_eq_bestRankFrobSq` are all general.

Taken over from α's deleted `FiniteIndexTransport`: `exists_isBestRankApprox` (no `DecidableEq`
arguments; it uses `classical`) and `IsBestRankApprox.frobSq_sub_eq_bestRankFrobSq`. Dropped:
`IsBestRankApprox.reindex`, `bestRankFrobSq_reindex` and `bestRankFrobSq_eq_singularValueTailSq_reindex`
(they had no users).

Deleted: `ComplexEckartYoung`, `ComplexBestRankApproximation`, `ComplexGramTruncation`,
`ComplexVolumeSpectrum`.

* ComplexVolumeSpectrum (`complexGramEigenvalues`, `complexGramElementary`, `complexGramTail`, and
  their lemmas) is volume-sampling material, not an Eckart–Young twin. It moved verbatim, names and
  tags kept, into its only direct consumer `LowRank/Sampling/ComplexVolumeSamplingLaw.lean`
  (section `ComplexGramSpectrum`).
* `LowRank/Sampling/ComplexVolumeSampling.lean` now states its two endpoints with the general
  `bestRankFrobSq k A` and `truncatedSVD A k`. A private bridge `singularValueTailSq_eq_complexGramTail`
  lives in that file.
* `Subspaces/ComplexFrameTransport` imported ComplexBestRankApproximation only transitively. It now
  imports `ComplexVolumeProjectorTrace` and `ComplexVolumeProjection`.
* The `volume-sampling (partial)` tags on the three deleted ℂ helper theorems were not moved. Their
  general replacements are Eckart–Young statements tagged `eckart-young(-frobenius)`, and
  `volume-sampling` keeps its endpoint formalizations.

## 4. Mirsky: remains real (not done)

* The Frobenius Mirsky inequality `sum_sq_singularValues_add_sub_le_frobSq` (in Weyl) is now on
  `Fintype` with no `_fin` lemma: it uses `abs_frobInner_le_sum_singularValues_mul` from
  `Norms/SchattenTrace` (new import; no cycle). It stays ℝ because the library's von Neumann trace
  inequality (`Inequalities/VonNeumann`, a leaf) is real. A 𝕜 version needs `VonNeumann` over 𝕜
  (about 100 lines: `diagonalSequence`/Ky Fan with `re` and `‖·‖²`).
* `Inequalities/Mirsky.lean` (weak majorization) and `MirskyPadded.lean` are unchanged and ℝ. They go
  through `RealDilation`/`RealDilationSpectrum` (`Fin`-indexed real Hermitian dilation) and `Lidskii`
  (ℝ). Their private `weaklyMajorized_abs_singularValues_add_sub_fin` and
  `sum_abs_singularValues_add_sub_le_sum_range_fin` still match the brief's `_fin\b` grep. Removing
  them needs the dilation on `Fintype`, and a 𝕜 statement needs a Hermitian dilation `[0 A; Aᴴ 0]`
  and Lidskii over 𝕜. MirskyPadded is a padding corollary, not an ℝ/ℂ twin.

## 5. Call-site repairs (minimal; all build)

| file | repair |
|---|---|
| OstrowskiCongruence (4 blocks) | `simp only [RCLike.re_to_real, star_trivial] at *` after `intro x hx` |
| EigenvalueOrder, EigenvaluePerturbation | `simp only [quadForm_def, RCLike.re_to_real, star_trivial] at h ⊢` |
| LowRankInterlacing | `quadForm_def` added to a `simpa`; `Matrix.le_iff.mpr (by simpa … )` for the Loewner hypothesis |
| Krylov/Quadrature/Jacobi | `Matrix.conjTranspose_eq_transpose_of_trivial` before `← restrict_T_eq`, and after `convert` |
| Factorizations/RankRevealingTrailing | `simp only [RCLike.re_to_real, star_trivial]` before a `rw` |
| LowRank/RangeFinding/ExpectedPower | `rw [singularValueTailSq, Fintype.card_fin, ← Fin.sum_univ_eq_sum_range …]` |
| Perturbation/OptimalErrorContinuity | import `FiniteIndexTransport` → `EckartYoung` + `Norms.RankNorm` |
| ComplexRandomPivotedCholesky | general core call; `RCLike.re_to_complex` in one `simpa` |
| TraceTail, RelativeSpectrum, KyFan, CompressionDeterminant, SingularInterlacing, the files above | old unqualified names → `Matrix.IsHermitian.*` (textual) |

Recipe for real callers of the new CF forms: the goals read
`RCLike.re (quadForm A x) ≤ c * RCLike.re (star x ⬝ᵥ x)`. Run
`simp only [quadForm_def, RCLike.re_to_real, star_trivial]` on the goal and on the hypotheses, or pass
a real `⬝ᵥ` term directly in term mode (it is definitionally equal).

## Remaining / for the coordinator

* Mirsky over 𝕜 and the two Mirsky `_fin` lemmas (§4).
* `grep "Matrix (Fin"` still hits `EckartYoung.lean`, at the Σ factor `Matrix (Fin p) (Fin q) 𝕜` of the
  E′ `IsSVD`/`rectDiag`, which is inherent to that decision (SVD.lean has 28 hits). The brief's grep
  has to exclude it or be restated.
* `ComplexQZ.lean` has a `RealQZ.lean` sibling (generalized Schur, outside F1's core list).
* `scripts/AuditNewProofs.lean` l.350 still lists `NLAlib.Matrix.Inequalities.ComplexTraceTail`
  (a selection list; not edited, as γ1 did for ComplexFrobenius).
* I did not run Audit/ExtractDecls/sync_atlas. The `courant-fischer`, `cauchy-interlacing` and
  `weyl-mirsky` tags now sit on `Matrix.IsHermitian.*` declarations (ExtractDecls accepts `_root_`
  names in library modules).
