# Stage A-1 (agent β): `NLAlib/Matrix/Basic/QuadForm.lean`

Date: 2026-10-13. Status: the module compiles (`lake build NLAlib.Matrix.Basic.QuadForm`, no
warnings, `scripts/check_names.py` OK). No other file was edited.

## Definitions (decision D3)

| def | new body over `[RCLike 𝕜]` | ℝ bridge (`rfl`) |
|---|---|---|
| `quadForm A z : 𝕜` | `star z ⬝ᵥ (A *ᵥ z)` (Mathlib's `PosSemidef` form) | `quadForm_eq_dotProduct : quadForm A z = z ⬝ᵥ (A *ᵥ z)` |
| `rayleighQuotient A x : ℝ` | `RCLike.re (quadForm A x) / RCLike.re (star x ⬝ᵥ x)` | `rayleighQuotient_eq_div : rayleighQuotient A x = quadForm A x / (x ⬝ᵥ x)` |

There are also general unfolding lemmas `quadForm_def` and `rayleighQuotient_def`, both `rfl`.
The `atlas: quadform-def` tag stays on `quadForm`. The docstring no longer says ℝ. The atlas text
is D13 and the coordinator rewords it.

Imports: `Mathlib.Data.Real.Star` was replaced by `Mathlib.Analysis.RCLike.Basic`, and
`Mathlib.LinearAlgebra.Matrix.PosDef` was added for `quadForm_nonneg`/`quadForm_pos`. The file does
not import `Mathlib.Analysis.Matrix.*`.

## Generalised in place (same name, statement has no `ᵀ`/`⬝ᵥ`)

- `quadForm_zero_right` (`@[simp]`)
- `quadForm_reindex`

## New general lemmas (𝕜)

| lemma | statement |
|---|---|
| `quadForm_zero_left` (`@[simp]`) | `quadForm 0 z = 0` |
| `quadForm_eq_sum_star` | `= ∑ i, ∑ j, A i j * (star (z i) * z j)` |
| `quadForm_eq_sum_star_mul_mul` | `= ∑ i, ∑ j, star (z i) * A i j * z j` |
| `quadForm_sq_eq_sum_star` | quartic expansion with `star (z i)`, `star (z k)` |
| `quadForm_add` | `quadForm A (x+y) = Q x + star x ⬝ᵥ A *ᵥ y + star y ⬝ᵥ A *ᵥ x + Q y` |
| `quadForm_smul` | `quadForm A (c • z) = star c * c * quadForm A z` |
| `star_quadForm` | `star (quadForm A z) = quadForm Aᴴ z` |
| `ofReal_re_quadForm` | `hA : A.IsHermitian → ((re (quadForm A z) : ℝ) : 𝕜) = quadForm A z` |
| `star_dotProduct_mulVec_comm_of_isHermitian` | `star y ⬝ᵥ A *ᵥ x = star (star x ⬝ᵥ A *ᵥ y)` |
| `re_quadForm_smul_add_smul` | Hermitian, `r s : ℝ`: `re Q(r x + s y) = r² re Q x + 2 r s re (star x ⬝ᵥ A *ᵥ y) + s² re Q y` |
| `quadForm_vecMulVec_star_self` | `quadForm (vecMulVec b (star b)) x = (‖star x ⬝ᵥ b‖ : 𝕜) ^ 2` |
| `quadForm_conjTranspose_mul_mul` | `quadForm (Wᴴ * A * W) v = quadForm A (W *ᵥ v)` |
| `quadForm_conjTranspose_mul_self` | `quadForm (Aᴴ * A) y = star (A *ᵥ y) ⬝ᵥ (A *ᵥ y)` |
| `quadForm_nonneg` (`ComplexOrder`) | `A.PosSemidef → 0 ≤ quadForm A z` |
| `quadForm_pos` (`ComplexOrder`) | `A.PosDef → z ≠ 0 → 0 < quadForm A z` |
| `re_quadForm_nonneg` | `A.PosSemidef → 0 ≤ re (quadForm A z)` (no scope needed in the statement) |

`quadForm_nonneg`, `quadForm_pos` and `re_quadForm_nonneg` sit in a `section Order` with
`open scoped ComplexOrder`. At ℝ, the order in their statements is the usual one.

## Kept real under the current names (decision D1)

Each is a one-line corollary of the general lemma: `simpa only [star_trivial]`,
`simpa only [conjTranspose_eq_transpose_of_trivial, …]` or `simpa`.

`quadForm_eq_sum`, `quadForm_eq_sum_mul_mul`, `quadForm_sq_eq_sum`, `quadForm_smul_add_smul`
(cross term `x ⬝ᵥ A *ᵥ y`), `quadForm_vecMulVec_self` (`(x ⬝ᵥ b) ^ 2`),
`quadForm_transpose_mul_mul`, `quadForm_transpose_mul_self`.

All seven are used downstream (2–5 files each), and each statement contains either a
`star`-free double sum, `ᵀ` or a bare `⬝ᵥ`. Generalising them in place would leave `star (z i)` in
real goals after `rw`, so the general versions take the `_star`/`conjTranspose` names instead.

## `rayleighQuotient_toEuclideanCLM_eq` (in `Matrix/Spectral/PowerRayleigh`)

Its proof ends with `rfl`, and that `rfl` still closes the goal at ℝ. I copied the proof verbatim
into a scratch file importing the new module and it compiled. PowerRayleigh itself was not
rebuilt, because its ancestor PolynomialCalculus breaks (below). That file's other sites,
`rw [rayleighQuotient_toEuclideanCLM_eq, rayleighQuotient, quadForm]`, need the recipe
`rayleighQuotient` ↦ `rayleighQuotient_eq_div` and `quadForm` ↦ `quadForm_eq_dotProduct`.

## Probe results (no downstream file was edited)

Run 1 built ten dependants, run 2 built four more. Norms/Core and PenroseIdentities built
without errors in the state they were in at that time.

| module | result | first error |
|---|---|---|
| Matrix/Functions/PolynomialCalculus | **fails** (2 errors) | l.184: after `rw [quadForm, …]` the goal is `star (aeval A p *ᵥ v) ⬝ᵥ … = (aeval A p *ᵥ v) ⬝ᵥ …` (`star` left behind); same at l.233 |
| Matrix/Norms/Net | **fails** (2 errors) | l.106: `rw [quadForm, hBv, dotProduct_smul, hv]` cannot find `v ⬝ᵥ v` (goal has `star v ⬝ᵥ v`); l.217: `simp only [quadForm, …]; ring` leaves `star y ⬝ᵥ …` |
| Sketching/Sparse/Bands/Light/SynthesisBounds | **fails** (2 errors) | l.85: unfolding leaves `star z ⟨k, x⟩` in a triple sum; l.218: `simp only [quadForm, dotProduct]` leaves `star x i` |
| Probability/Concentration/QuadraticForms/QuadraticMoments | builds | — |
| Probability/Concentration/QuadraticForms/HansonWright | builds | — |
| Probability/Concentration/QuadraticForms/Geometry | builds | — |
| Sketching/Sparse/Bands/Heavy/PreservingBound | builds (predicted broken: false positive) | — |
| Estimation/Diagonal/DiagonalEstimator | builds (predicted broken: false positive) | — |
| Matrix/Spectral/CourantFischer | not built: blocked by PolynomialCalculus | — |
| Matrix/Inequalities/Wielandt | not built: blocked by PolynomialCalculus | — |
| Krylov/Solvers/CG | not built: blocked by PolynomialCalculus | — |
| Matrix/Spectral/PowerRayleigh | not built: blocked by PolynomialCalculus | — |
| Matrix/Inequalities/FiniteExponentialGram | not built: blocked by PolynomialCalculus | — |
| Sketching/Sparse/Bands/Light/ZeroBlock | not built: blocked by SynthesisBounds | — |

Matrix/Spectral/Core does not import QuadForm, even transitively, so it was not probed.

Every observed failure is the predicted "quadForm unfold" pattern. The mechanical fix is to
replace `quadForm` by `quadForm_eq_dotProduct` in the `rw`/`simp only` list, and `rayleighQuotient`
by `rayleighQuotient_eq_div`. No failure came from a renamed or changed lemma statement.

PolynomialCalculus blocks 22 of the 28 files predicted to break on quadForm/rayleighQuotient
(Spectral, Perturbation, Inequalities, Krylov and Estimation/Spectral). It is the first file to
repair in stage B.

## For the coordinator

- No new files, so the aggregators are unchanged. There is no rename map: nothing was renamed.
  The new names are additive.
- Atlas D13: the `quadform-def` entry text should say `zᴴ A z` over RCLike.
