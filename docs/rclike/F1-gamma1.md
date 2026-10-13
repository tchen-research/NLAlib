# F1, agent γ1: norms and spectral core (`Norms/Frobenius`, `Norms/Core`, `Spectral/Core`)

Date: 2026-10-13. Files edited: `NLAlib/Matrix/Norms/Frobenius.lean`, `NLAlib/Matrix/Norms/Core.lean`,
`NLAlib/Matrix/Spectral/Core.lean`. Deleted: `NLAlib/Matrix/Norms/ComplexFrobenius.lean`. Repointed
(import line or moved lemma only): `Matrix/Norms.lean` (aggregator line removed),
`Matrix/Norms/ComplexFrobeniusTrace.lean`, `Matrix/Spectral/ComplexVolumeSpectrum.lean`,
`Sketching/Sampling/SamplingMultiplication.lean`. Rename map: `docs/renames/2026-10-F1.json`
(shared with γ2; 25 γ1 entries).

`lake build NLAlib.Matrix.Norms.Core NLAlib.Matrix.Spectral.Core` succeeds. None of the three files
has a warning. The leaf `Norms/SpectralNormBounds`, which `Spectral/Core` imports, builds, but now
shows four `unusedSectionVars` warnings (`[DecidableEq m]` at l.30, 43, 59, 98), because `specNorm`
no longer needs it (item 3). I did not touch it.

## 1. Transpose twins removed

Rule applied. If the `ᵀ` name does not mention `transpose` (`_of_orthonormal`, `frobInner_mul_mul`,
`frobInner_eq_trace`), the general `ᴴ` lemma takes that plain name. If it does mention `transpose`,
the general lemma keeps its `conjTranspose` name and the `ᵀ` name is removed.
`@[deprecated (since := "2026-10-13")] alias` was kept only for names that are used outside the
core files and whose general statement has the same shape up to `ᴴ`/`ᵀ`.

### ℝ names that now carry the `ᴴ` statement (same name; no alias possible)

| name | new statement |
|---|---|
| `frobInner_eq_trace` | `frobInner A B = RCLike.re (Aᴴ * B).trace` (was `(Aᵀ * B).trace` over ℝ) |
| `frobInner_mul_mul` | `frobInner (P*X) (Q*Y) = frobInner X (Pᴴ * Q * Y)` |
| `frobInner_mul_mul_eq_zero` | hypothesis `Pᴴ * Q = 0` |
| `frobInner_mul_left_of_orthonormal` | hypothesis `Qᴴ * Q = 1` |
| `frobSq_mul_left_of_orthonormal` | hypothesis `Qᴴ * Q = 1` |
| `frobSq_mul_right_of_orthonormal` | `frobSq (X * Vᴴ) = frobSq X`, hypothesis `Vᴴ * V = 1` |
| `specNorm_le_one_of_orthonormal` | hypothesis `Pᴴ * P = 1` |

### Removed or renamed names

| old name | replacement | alias? |
|---|---|---|
| `frobInner_eq_re_trace` | `frobInner_eq_trace` | yes (7 uses) |
| `frobInner_eq_trace_mul_transpose` (ℝ) | `frobInner_eq_re_trace_mul_conjTranspose` | no (the `RCLike.re` wrapper changes the shape; 1 use, ProcrustesRotations l.68) |
| `frobSq_eq_sum_dotProduct_self` (ℝ) | `frobSq_eq_sum_re_star_dotProduct_self` | no (`re`/`star` shape; 1 use, Kaczmarz/Core l.87) |
| `mulVec_dotProduct_mulVec_self` (ℝ) | `star_mulVec_dotProduct_mulVec_self` | no (`star` shape; 18 uses, listed in §5) |
| `frobInner_mul_mul_conjTranspose` | `frobInner_mul_mul` | no (0 uses) |
| `frobInner_mul_mul_eq_zero_of_conjTranspose_mul_eq_zero` | `frobInner_mul_mul_eq_zero` | no (0 uses) |
| `frobInner_mul_left_of_conjTranspose_mul_self` | `frobInner_mul_left_of_orthonormal` | no (0 uses) |
| `frobSq_mul_left_of_conjTranspose_mul_self` | `frobSq_mul_left_of_orthonormal` | yes (Projections) |
| `frobSq_mul_right_of_conjTranspose_mul_self` | `frobSq_mul_right_of_orthonormal` | no (0 uses) |
| `specNorm_le_one_of_conjTranspose_mul_self` | `specNorm_le_one_of_orthonormal` | yes (Projections) |
| `specNorm_transpose_mul_of_eq_mul` (ℝ) | `specNorm_conjTranspose_mul_of_eq_mul` | yes |
| `specNorm_mul_transpose_self` (ℝ) | `specNorm_mul_conjTranspose_self` | yes |
| `specNorm_le_one_of_isHermitian_of_isIdempotentElem` | `Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem` (item 4) | no (no Lean users) |
| `specNorm_le_one_of_isSymm_of_isIdempotentElem` (ℝ) | `Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem` | yes (an `IsSymm` argument elaborates in the `IsHermitian` slot; tested) |
| `specNorm_sub_mul_transpose_mul_le` (ℝ) | `specNorm_sub_mul_conjTranspose_mul_le` | yes |
| `specNorm_add_sq_le_of_mul_transpose_eq_zero` (ℝ) | `specNorm_add_sq_le_of_mul_conjTranspose_eq_zero` | yes |
| `specNorm_add_sq_le_of_transpose_mul_eq_zero` (ℝ) | `specNorm_add_sq_le_of_conjTranspose_mul_eq_zero` | no (0 uses) |
| `frobenius_norm_sq_eq_frobSq` (ℝ, ComplexFrobenius) | `frobNorm_eq_norm` | no (0 uses) |
| `lamMin` (def) | `hM.eigenvalues₀ ⟨card n - 1, _⟩` via `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf` | no |
| `lamMin_le`, `lamMin_eq_iInf_rayleigh` | `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`; `ciInf_le (bddBelow_range_rayleigh M) ⟨x, hx⟩` for `lamMin_le` | no |
| `sigmaMinSq` (def), `sigmaMinSq_nonneg`, `sigmaMin_eq_sqrt_sigmaMinSq`, `sigmaMinSq_eq_sigmaMin_sq` | `sigmaMin`, `sigmaMin_nonneg`, `sigmaMin_transpose_sq` | no (0 uses outside the file) |

**How the aliases behave.** Term-mode uses (`exact`, `have := …`, passing `hV : Vᵀ * V = 1` into a
`Vᴴ * V = 1` slot) elaborate. `rw [alias …]` on a goal that contains `ᵀ` in the rewritten pattern
does **not** match. For example, `rw [specNorm_mul_transpose_self]` on `specNorm (A * Aᵀ)` fails,
and so does `rw [frobSq_mul_right_of_orthonormal hV]` on `frobSq (X * Vᵀ)` (tested in a scratch
file). The same holds for the same-name `ᴴ` statements above. Such call sites need
`simp only [Matrix.conjTranspose_eq_transpose_of_trivial]` on the lemma, or `rw` on the goal first.

### Real specialisations kept (not `ᵀ`-shaped)

`frobSq_eq_sum_sq`, `sum_diag_sq_le_frobSq`, `sum_diag_sq_le_frobNorm_sq`, `sum_sq_mulVec_le_frobSq`,
`sum_sq_mulVec_le_specNorm_sq`, `mulVec_dotProduct_mulVec_le_frobSq_mul`, `dotProduct_self_nonneg`,
`mulVec_dotProduct_mulVec_eq_sum_sq`, `abs_dotProduct_mulVec_le_specNorm`, and the Euclidean-length
lemmas. These replace `‖x‖²` by `x²` or are real dot-product facts, and they have no `ᴴ`
counterpart in these files. `frobSq_eq_sum_sq` alone has 35 uses. Folding them into the `‖·‖`
forms belongs to the port. `frobInner_transpose`, `frobSq_transpose`, `frobNorm_transpose` and
`specNorm_transpose` are general over `𝕜`, since `ᵀ` is a separate operation over ℂ. They stay.

## 2. One spelling

* **Frobenius.** New in `Norms/Frobenius.lean`: `frobNorm_eq_norm (A : Matrix m n 𝕜) : frobNorm A = ‖A‖`,
  stated under `open scoped Matrix.Norms.Frobenius`. Mathlib's
  `frobenius_norm_sq_eq_sum_norm_sq` (over any `NormedAddCommGroup`) moved here from
  `ComplexFrobenius`, keeping its name; the bridge is proved from it. Its 4 user files needed no edit.
* **Smallest eigenvalue.** `lamMin` is deleted. New in `Spectral/Core.lean`:
  `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf (hM : M.IsHermitian) (hn : 0 < card n) :
  hM.eigenvalues₀ ⟨card n - 1, _⟩ = ⨅ x : {x : n → ℝ // x ⬝ᵥ x = 1}, x ⬝ᵥ M *ᵥ x`. This is the real
  Rayleigh characterisation, with a self-contained proof from Mathlib's
  `conjStarAlgAut_star_eigenvectorUnitary` (it adds the import `Mathlib.Analysis.Matrix.Spectrum`).
  `sigmaMin_transpose_sq` keeps its name, and its right side is now the infimum, i.e. what `lamMin`
  unfolded to: `sigmaMin Gᵀ ^ 2 = ⨅ x : {x : m → ℝ // x ⬝ᵥ x = 1}, x ⬝ᵥ (G * Gᵀ) *ᵥ x`. Combined
  with the bridge it gives `eigenvalues₀`. `bddBelow_range_rayleigh` stays.
* **Loewner order.** None of the three files contains a `PosSemidef` or `(B - A).PosSemidef`
  hypothesis. Nothing to do.

## 3. `specNorm` and `DecidableEq`

`specNorm [DecidableEq n] (A : Matrix m n 𝕜)`: `[DecidableEq m]` is dropped, `[DecidableEq n]`
stays. The brief's premise is wrong for the column index. `Matrix.instL2OpNormedAddCommGroup` has
signature `[RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]`, because the norm is induced through
`Matrix.toEuclideanLin`/`Matrix.toLin'`, whose inverse uses `Pi.single`. In `Norms/Core` the
section variable is now `[DecidableEq n]`. `[DecidableEq m]` was added only where a statement needs
it: `specNorm_conjTranspose`, `specNorm_transpose`, `specNorm_mul_conjTranspose_self`. Four proofs
that need it only internally use `classical`. The two `omit [DecidableEq m] in` lines are gone.
Downstream signatures that still carry `[DecidableEq m]` keep working (it is simply unused).
`specNorm_eq_norm` and `specNorm_nonneg` now take only `[DecidableEq n]`.

## 4. Dot-notation namespaces

`Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem` (`hs.specNorm_le_one_of_isIdempotentElem hp`)
and `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf` are declared with `_root_.` inside
`namespace NLAlib`. Tested: a name `NLAlib.Matrix.IsHermitian.foo` is **not** found by `hA.foo`
inside `namespace NLAlib`; it works only with `open NLAlib`. So the `_root_` prefix is required.

**Coordinator action needed.** `scripts/ExtractDecls.lean` keeps only declarations under the
`NLAlib` root (l.61/89). These two theorems are therefore missing from `atlas/declarations.json`.
The `atlas: projection-facts` tag now sits on `Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem`,
so after the next sync `projection-facts` loses both of its formalizations
(`NLAlib.specNorm_le_one_of_isHermitian_of_isIdempotentElem` and `…isSymm…` in `atlas.json`
l.1362/1368). Suggested fix: also accept names whose module starts with `NLAlib.`. `check_names.py`
and `sync_atlas.py` read `declarations.json`, so they then need nothing else.

## Deleted files

* `Matrix/Norms/ComplexFrobenius.lean` (46 lines, deleted). Its contents were the generic
  `frobenius_norm_sq_eq_sum_norm_sq` (moved to `Norms/Frobenius`, name kept), the ℝ twin
  `frobenius_norm_sq_eq_frobSq` (deleted, superseded by `frobNorm_eq_norm`), and two ℂ facts used
  only by the sampled-multiplication files: `frobenius_norm_sq_vecMulVec` and
  `frobenius_norm_sq_map_ofReal_eq_frobSq`. Those two moved verbatim, names kept, into
  `Sketching/Sampling/SamplingMultiplication.lean`, their only consumer (`…Bounds` imports it). The
  three importers now import `NLAlib.Matrix.Norms.Core`.
* `Matrix/Spectral/RealComplexNorm.lean` does not exist. The file is
  `Matrix/Norms/RealComplexNorm.lean`. **Not deleted**: it is not a ℂ twin of core content. It
  holds the real-to-complex transport `specNorm_le_norm_map_ofReal` (`‖A‖₂ ≤ ‖A.map ofReal‖`) and
  `norm_toLp_ofReal_eq`. These have no general counterpart in the core, and 5 files use them
  (MatrixPowerBounded, MatrixPowerReal ×2, SRHT, SRHTWithReplacement). DESIGN §3.3 pitfall 6 keeps
  real↔complex transports as bridges. Deleting it would need a new core lemma
  (`specNorm (A.map (algebraMap ℝ 𝕜)) = specNorm A`), so I left it for the coordinator or the port.
* `scripts/AuditNewProofs.lean` l.344 still lists the module `NLAlib.Matrix.Norms.ComplexFrobenius`
  (not edited; it is a name in a selection list).

## Other generalised statements

* `inner_toEuclideanLin_eq_sum` and `one_sub_two_mul_mul_specNorm_le_iSup`: `Matrix (Fin N) (Fin n) ℝ`
  becomes `Matrix m n ℝ` over `[Fintype m] [Fintype n] [DecidableEq n]`, with nets in
  `EuclideanSpace ℝ n × EuclideanSpace ℝ m`. Their users (Gaussian `Gordon`, `SpectralSecondMoment`)
  build unchanged.
* `specNorm_pinvR_sq`: the proof now unfolds `pinvR` and uses
  `simp only [Matrix.conjTranspose_eq_transpose_of_trivial]` instead of
  `pinvR_eq_transpose_mul_inv`. That bridge is a γ2 `ᵀ` twin, so this keeps `Spectral/Core`
  independent of it. The statement is unchanged.
* The module docstrings of the three files now describe the F1 convention (`ᴴ` statements, no
  `ᵀ` corollaries, `frobNorm_eq_norm`, smallest eigenvalue = `eigenvalues₀` at `card - 1`).

## 5. Probe (direct importers; not fixed)

Built on 2026-10-13 with γ2's in-progress edits to `Basic/*` and `Subspaces/Projections` in the
tree. Targets: the 33 direct importers of the three files, the users of the moved
ComplexFrobenius lemmas, and the alias users. "γ2" means the first error is a name or shape that γ2
removed (`pinvL_eq_inv_transpose_mul_mul_transpose`, `pinvR_eq_transpose_mul_inv`,
`residual_eq_sub_mul_transpose_mul`, `HasOrthonormalCols.transpose_mul_self`,
`hasOrthonormalCols_iff_transpose_mul_self`, `quadForm_eq_sum`).

**Build** (✔): MoorePenroseProjector, Pseudoinverse, Projections, SVD, SingularValueSpectrum,
MaximumVolumeBudget, TracePowers, ColumnNorms, ComplexFrobeniusTrace, EntryBounds, RayleighNorm,
RealComplexNorm, SpectralNormBounds (4 new unused-variable warnings), SpectralContinuity,
QuadraticProbe, SchurFrobenius, HoffmanWielandtNormal, GaussianMatrix, Lipschitz, FourthMoment,
SecondMoment, Gordon, SmallBall, SpectralSecondMoment, ApproxMultiplication, SamplingMultiplication,
SamplingMultiplicationBounds, NormalizedBands, DirectionalSquaredNorm.

**Fail, caused by γ1:**

| module | first error |
|---|---|
| Matrix.Calculus.GramTrace | l.54 (and l.135): after `rw [frobInner_eq_trace]` the goal is `RCLike.re ((X * G)ᴴ * (X * G)).trace = …`, so the next `rw` pattern `(?M * ?N)ᵀ` is not found (`frobInner_eq_trace` now has the `ᴴ` statement) |
| Matrix.Spectral.SpectralBounds | l.185/205/219: unknown identifier `mulVec_dotProduct_mulVec_self`. **This one blocks most of the spectral tree** (see below) |
| Matrix.Perturbation.GramSingularBounds | l.34: unknown identifier `mulVec_dotProduct_mulVec_self`; l.55: `simpa only [transpose_transpose, specNorm_transpose] using (specNorm_mul_transpose_self Aᵀ).symm` type mismatch (the alias produces `Aᵀᴴ`) |
| Solvers.Kaczmarz.Core | l.87: unknown identifier `frobSq_eq_sum_dotProduct_self` |

**Fail, caused by γ2:** Structured.Measurable (l.92 `pinvL_eq_inv_transpose_mul_mul_transpose`),
Factorizations.QR (l.332, same), Subspaces.OrthogonalProducts (l.30 `hP.transpose_mul_self`),
Subspaces.Stiefel (l.77, same), LowRank.Structural.RangeFinder (l.96, same),
LowRank.Nystrom.SketchedRegression (l.90, `pinvL` rewrite; l.148 `residual_eq_sub_mul_transpose_mul`),
Spectral.SingularValueInvariance (l.70 `hasOrthonormalCols_iff_transpose_mul_self`),
Probability…QuadraticMoments (l.114 `quadForm_eq_sum` pattern now has `star`).

**Not built (blocked):**

| module | blocked by |
|---|---|
| PolynomialFilter, PowerIteration, EigenvalueTrace, Sylvester, EckartYoung, ComplexVolumeSpectrum | SpectralBounds (γ1) only |
| VonNeumann, SchattenSingularCoefficients, InversePerturbation, PseudoinverseProjectors, ProjectionFrobeniusGaps, ProjectionGaps, ProjectorBlocks | SpectralBounds (γ1) and OrthogonalProducts / SingularValueInvariance (γ2) |
| Conditioning, LeastSquaresGeometry | SpectralBounds, QR, OrthogonalProducts |
| SpectralRangeFinder | SpectralBounds, GramTrace, RangeFinder, SketchedRegression, Measurable, OrthogonalProducts |
| CanonicalQR | OrthogonalProducts, Stiefel (γ2) |
| KaczmarzExtensions | Kaczmarz.Core (γ1) |

**Predicted further breakage** (grep, beyond the modules built above):

* `mulVec_dotProduct_mulVec_self` (no alias): PowerIteration l.136, PolynomialCalculus l.132/173,
  ProductSingularValues l.30, CourantFischer l.335/355/370/387, SpectralMinimum l.70,
  ProjectionGaps l.24, GramIsometry l.27, SubGaussianRows l.54, SubspaceEmbedding/Gram l.39,
  SubspaceEmbedding l.103.
* `frobInner_eq_trace` (now `ᴴ` + `re`): 32 `rw` sites in 22 files, e.g. EckartYoung l.153/175/248,
  Procrustes l.30/40/99/101, KyFan l.117, NuclearNorm l.163, InversePowerGrowth l.30/319,
  GramSoftMin l.91/115, EigenvalueTrace l.136, ProjectionGaps l.202, PrincipalAngles l.250 (γ2's
  Pseudoinverse/Projections/MoorePenrose already use the new form).
  `frobInner_eq_trace_mul_transpose`: ProcrustesRotations l.68.
* `rw` with a renamed general or alias lemma on a `ᵀ` goal: `frobSq_mul_right_of_orthonormal`
  (PolynomialFilter l.160/161, SpectralRangeFinder l.377, RangeFinder l.98/99, EckartYoung l.246,
  EigenvalueTrace l.50, ProjectionFrobeniusGaps l.52/53); `frobInner_mul_mul` followed by
  `rw [hs.eq]` with `hs : IsSymm` (VonNeumann l.39/40, ProjectorBlocks l.43/45);
  `specNorm_mul_transpose_self` in `rw` (PowerIteration l.115/117, RelativeSpectrum l.179,
  BlockNormBounds l.22/23).
* `lamMin`, `lamMin_le`, `sigmaMin_transpose_sq`: SpectralMinimum l.24–110 (the whole file is about
  `lamMin`). Repair: replace `lamMin A` by its infimum, `lamMin_le A hv` by
  `ciInf_le (bddBelow_range_rayleigh A) ⟨v, hv⟩`, and `unfold lamMin` by nothing.
  `sigmaMin_transpose_sq` already returns the infimum.

## Acceptance greps (my files)

```
$ F="NLAlib/Matrix/Norms/Frobenius.lean NLAlib/Matrix/Norms/Core.lean NLAlib/Matrix/Spectral/Core.lean"
$ grep -n "_fin\b" $F            # 0
$ grep -n "Matrix (Fin" $F       # 0
$ grep -n "ℂ" $F                 # 0
$ grep -n "PosSemidef" $F        # 0
$ ls NLAlib/Matrix/Norms/ComplexFrobenius.lean   # No such file
$ grep -rnw lamMin NLAlib --include=*.lean | grep -v Spectral/Core.lean | wc -l   # 3 (SpectralMinimum, leaf)
```

The one remaining `Fin` in `Spectral/Core` is the index type of Mathlib's `eigenvalues₀` in the
bridge. Note for the brief's grep `grep -rn "_fin\b" NLAlib/Matrix`: it currently returns 173 lines,
111 of them Mathlib names (`Fintype.card_fin`, `Finset.sum_fin…`). The remaining 62 are the SVD
agents' `private …_fin` lemmas. The acceptance line should exclude `card_fin`.

## Atlas impact (for the coordinator's sync)

`lamMin` (tags `norm-lipschitz`, `svd-def`; atlas.json l.3321, l.13296) and `sigmaMinSq`
(`svd-def`, l.13310, which has a hand-written `usage`) disappear. The bridge carries no `atlas:` tag
line, only a docstring mention of `norm-lipschitz`. `projection-facts`: see §4.
