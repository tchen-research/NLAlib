# Sketch interface: what the moment method needs, what Sparse contains, and the conclusion shape

This is the F3 write-up from `docs/FOUNDATIONS_BRIEF.md` §3. It was written on 2026-10-13 by reading
the source only: no Lean file was edited and no Lean or lake process was run. File references are
`path:line`, where the line is that of the `theorem`/`def` keyword in today's source. Unless a path
starts otherwise, `Sparse/` means `NLAlib/Sketching/Sparse/` and `Properties/` means
`NLAlib/Sketching/Properties/`. The machine-readable companion for §3 is
`docs/port/sparse_files.json`.

Inputs:
- the sources under `NLAlib/Sketching/`;
- `atlas/declarations.json` (10:39 snapshot; it already has the S2 module names);
- `docs/SPARSE_INTEGRATION.md`, `docs/dedup/S1.md` and `docs/dedup/S2.md`;
- a file-level import closure and an approximate declaration-level closure of the two headline
  theorems. The second was computed by matching names textually in declaration bodies, so it errs
  towards inclusion.

The two headline theorems still have their names and are in `Sparse/SparseEmbedding.lean`:

- `measure_sparseStack_embedding_success_ge` (`Sparse/SparseEmbedding.lean:35`);
- `measure_uniformSparse_embedding_success_ge` (`Sparse/SparseEmbedding.lean:86`).

## 0. How the headline theorems are proved today

The two theorems run the same chain with different sketch laws. SparseStack uses a uniform signed
hash per (block, column). Uniform exact-s, i.e. OSNAP, uses a uniform signed support of size `s`
per column. Below, `G = (S U)ᵀ (S U) − I_d`.

1. **Markov on a trace moment.** `P(¬ embedding) ≤ P(‖G‖ ≥ ε) ≤ E tr G^{2q} / ε^{2q}`.
   - `Sparse/MomentMethod/GramTail.lean:38` (`FiniteLaw.prob_le_norm_le_expect_trace_pow_div`) and
     its instance at `:82`;
   - exact-s copies at `Sparse/MomentMethod/UniformSparseTail.lean:33,51`;
   - deterministic core at `NLAlib/Matrix/Spectral/TracePowerBounds.lean:44`
     (`specNorm_pow_two_mul_le_trace_pow`).
2. **Comparison of the sparse sketch with an iid model.** The iid model has entries
   `η ∈ {0, ±√b}`. The statement is `E tr G_sparse^{2q} ≤ c^{4q} E tr G_iid^{2q}` with `c ≤ c*`.
   - SparseStack: `Sparse/IIDComparison/MomentTransfer.lean:135`.
   - Exact-s: `Sparse/IIDComparison/ExactMomentTransfer.lean:216`.
   - The proof is convex order through a martingale coupling: `Sparse/IIDComparison/ConvexOrder.lean:166`
     and `Sparse/IIDComparison/ExactMomentTransfer.lean:95`.
   - Convexity of `tr A^{2q}` is `NLAlib/Matrix/Functions/TracePowerConvexity.lean:356`.
3. **The iid moment as a vacuum moment.**
   `E tr G_iid^k = Σ_a ⟨(a,0)| M^k |(a,0)⟩`, where `M` is multiplication by `G_iid` in an
   orthonormal product polynomial basis (`Sparse/FockModel/VacuumMoment.lean:62`).
4. **Ladder iteration.** If the band bounds `‖B_δ P_ν‖ ≤ β` hold for `ν ≤ 2q`, then
   `E tr G_iid^{2q} ≤ d (3β)^{2q}` (`Sparse/Bands/LadderIteration.lean:392`).
5. **The band envelope.** `β = (3+√2)(√(D_q/m) + D_q/m + (2q+1)/s)` with `D_q = d+2q+1`
   (`Sparse/Bands/BandEnvelope.lean:32,96`).
6. **Rounding.** With `q = max 1 ⌈log₂(d/δ)⌉`, `s = ⌈L(2q+1)/ε⌉`, `L = 90 c*²` and
   `c* = (1−e^{−1})^{−1}`, the moment bound gives failure probability at most `δ`.
   - SparseStack: `Sparse/MomentMethod/Endgame.lean:115`.
   - Exact-s: `Sparse/MomentMethod/UniformSparseRoundedBounds.lean:31`.
   - The displayed sizes `s < 1356 q/ε` and `m < 306456 (d+q)/ε²` are at
     `Sparse/SparseEmbedding.lean:137`.

No ε-net or union bound appears anywhere in this chain. The trace moment controls every direction
at once.

## 1. What the OSE moment method needs from a sketch distribution

### 1.1 Named hypotheses

The setting is a probability measure `μ` on `Ω`, a random sketch `S : Ω → Matrix k m ℝ`, a fixed
`U : Matrix m d ℝ` with `HasOrthonormalCols U`, and `G ω = (S ω * U)ᵀ * (S ω * U) − 1`. A
`structure` carrying the interface would hold the fields below. Only **H1** is needed for the
conclusion. **H2–H6** are what the sparse proof uses to *establish* H1, and **H7** is the
quantifier form.

**H1 `traceMoment` (oblivious trace-moment bound).** For every `U` with orthonormal columns,
`tr (G^{2q})` is integrable and `∫ tr (G ω ^ (2q)) ∂μ ≤ B(d, q)`.

The Markov step consumes this hypothesis:
- `Sparse/MomentMethod/GramTail.lean:82` (`sparseStack_ose_failure_tail`), used at
  `Sparse/MomentMethod/Endgame.lean:93`;
- `Sparse/MomentMethod/UniformSparseTail.lean:51` (`ose_failure_tail`), used at
  `UniformSparseTail.lean:131`.

The SparseStack value is `B = d (3 c_b² β)^{2q}` (`Sparse/MomentMethod/Endgame.lean:35`). The
exact-s value is `B = d (3 ŝ² β)^{2q}` with `ŝ = exactScale ≤ c_b`
(`Sparse/MomentMethod/UniformSparseTail.lean:82`, `Sparse/IIDComparison/FillThinCoupling.lean:259`).

The `q = 1` case can be stated with `frobSq G = tr G²` (G is symmetric), as CountSketch does. The
library has no `frobSq A = tr (Aᵀ A)` lemma for real matrices; the only trace forms of `frobSq` are
pseudoinverse-specific (`NLAlib/Matrix/Basic/Pseudoinverse.lean:277–332`). The interface would need
that bridge.

**H2 `unitColumns` (hollowness).** Surely `diag (S ωᵀ S ω) = 1`, i.e. every column has norm
exactly 1. Then `G = Σ_{i≠j} (SᵀS)_{ij} u_i u_jᵀ` has no diagonal term. That makes `G` multilinear
in *distinct* columns, which the barycenter step H5 needs.

| where it is used | file:line |
|---|---|
| SparseStack | `Sparse/SparseStack.lean:373` (`gramError_eq_hollow`) |
| exact-s | `Sparse/UniformSparse.lean:278` |
| entry to the coupling | `Sparse/IIDComparison/DistributionBridges.lean:56` (`sparseVectorError_eq_gramError`, needs `0 < s`) |
| CountSketch | `Sparse/CountSketch.lean:81` (needs `σ_i² = 1`) and `:104` |

**H3 `isotropy`.** `E[SᵀS] = I`, equivalently `E G = 0` for every `U`.
- The sparse proof never uses it directly; it is implied by H2 + H5.
- CountSketch has it conditionally on the hash: `Sparse/CountSketchMoments.lean:87`.
- SRHT has it as the population mean:
  `NLAlib/Sketching/Structured/SRHTCore.lean:99` (`mean_srhtPopulationAtom`).
- For leverage sampling it is proved inside `NLAlib/Sketching/Sampling/LeverageSampling.lean:60`.

H3 is the hypothesis of the matrix-Chernoff route (SRHT, leverage), not of the moment route.

**H4 `independence`.** The primitive randomness is independent across columns:
- SparseStack: across (block, column) sites. The law is `sparseStackSelectorLaw`
  (`Sparse/SparseStackLaw.lean:68`) and its product form is `selectorArrayLaw`
  (`Sparse/IIDComparison/ConvexOrder.lean:28`).
- Exact-s: across whole columns (`uniformSparseSampleLaw`, `Sparse/UniformSparse.lean:80`).

It is used twice:
- in the off-diagonal conditional expectation at two distinct sites,
  `Sparse/IIDComparison/IndependentCopyLift.lean:134` (`conditional_cross_inner`, hypothesis
  `z ≠ z'`);
- in "mixture of product kernels = product law", `Sparse/IIDComparison/ConvexOrder.lean:102` and
  `Sparse/IIDComparison/ExactConditionalMatrixTransfer.lean:76`.

**H4′ `limitedIndependence` (weakening of H4).** It suffices that the law matches the fully
independent law in all `4q`-wise marginals. The reason is that `tr G^{2q}` has local degree `4q`
in the primitive coordinates.
- Degree bound: `Sparse/MomentMethod/SparseStackLimitedIndependence.lean:160`.
- Transfer: `Sparse/MomentMethod/SparseStackLimitedIndependence.lean:183`.
- Whole-column OSNAP: `Sparse/MomentMethod/UniformSparseLimitedIndependence.lean:139,161`.
- The predicate is `MatchesUpTo`, defined at `Sparse/FiniteLaw/LocalMoments.lean:51`.

This is off the headline path, but it is the natural field for a "k-wise independent hash" sketch.

**H5 `signSymmetricCoupling` (conditional barycenter / martingale coupling).** There is a kernel
`κ` from the sparse column law to an iid ternary model with two properties:
(a) the mixture `μ ⊗ κ` has exactly the iid law;
(b) `E[c·Y | X] = X` columnwise.

It is proved from sign symmetry by coordinate flips:
- `Sparse/IIDComparison/ConditionalBarycenter.lean:159` (`kernelWeight_flipAt_of_ne`);
- `:177` (`fiberMoment_off`);
- `:347` (`conditional_barycenter`).

For exact-s it is the fill/thin coupling: `Sparse/IIDComparison/FillThinCoupling.lean:432`
(`jointColumnLaw`) and `Sparse/IIDComparison/ExactConditionalBarycenter.lean:181`.

The constants are as follows.
- `c = c_b = (1 − (1−1/b)^b)^{−1}`: `Sparse/IIDComparison/TernaryCoordinateLaws.lean:201`.
- `c_b ≤ c* = (1−e^{−1})^{−1} < 1.582`: `TernaryCoordinateLaws.lean:219` and
  `Sparse/MomentMethod/ParameterConstants.lean:28,134`.
- The exact-s scale is `exactScale ≤ c_b`: `FillThinCoupling.lean:253,259`.

H2 + H4 + H5 imply the matrix barycenter identity. The SparseStack version is
`Sparse/IIDComparison/IndependentCopyLift.lean:229` and the exact-s version is
`Sparse/IIDComparison/ExactConditionalMatrixTransfer.lean:197`. Together with convexity (R2) they
give the comparison R3.

**H6 `iidModelMoment`.** The iid comparison model satisfies H1 with `B = d (3β)^{2q}`
(`Sparse/Bands/LadderIteration.lean:392`, `Sparse/Bands/BandEnvelope.lean:96`).

Its own inputs are the ternary law `η ∈ {0, ±√b}` with masses `1 − 1/b` and `1/(2b)` each, which
has mean 0 and variance 1 (`Sparse/FockModel/TernaryJacobi.lean:160,168`), and the product
orthonormal basis (`Sparse/FockModel/ProductBasis.lean:35`). All 62 rebuilt band and Fock-model files (63 counting the dead `Bands/Light/ZeroBlock`) serve
this one hypothesis, and only for this one law.

**H7 `oblivious`.** The bound holds for each fixed `U` with `HasOrthonormalCols U`. The Gram
equivalence `Properties/SubspaceEmbedding/Gram.lean:46` needs orthonormality.

There is a random-`U`-independent-of-`S` corollary at `Sparse/MomentMethod/IndependentFrame.lean:33`.
In the Measure world it is Fubini.

Gaussian satisfies a stronger form: the law of `S U` depends only on `d`
(`NLAlib/RandomMatrix/Gaussian/Invariance/LinearImage.lean:68`, `gaussianMatrix_map_mul_right`).

### 1.2 Which sketch satisfies what (constants; "—" = not proved here)

| sketch | H1 trace moment | H2 unit cols | H3 isotropy | H4 independence | H5 coupling / sign symmetry | endpoint route and parameters |
|---|---|---|---|---|---|---|
| **Gaussian** `S = k^{-1/2} G` | `q=1`: `E‖G_U‖_F² = (d²+d)/k`. This follows from `NLAlib/RandomMatrix/Gaussian/Moments/ApproxMultiplication.lean:152` with `M = N = Uᵀ`, `t = k`; it is not stated in sketch vocabulary. `q>1`: — | no (column norms are random) | entry covariance `NLAlib/RandomMatrix/Gaussian/Moments/FourthMoment.lean:267`; `E SᵀS = I` not stated | iid entries (product measure `gaussianMatrix`) | not needed: rotation invariance `LinearImage.lean:68` replaces it | singular-value deviation (Gordon), not moments: `NLAlib/Sketching/Gaussian/GaussianEmbedding.lean:72`, `k ≥ 18(d + 2 log(2/δ))/ε²`, via `NLAlib/RandomMatrix/Gaussian/Spectral/Deviation.lean:41,74` |
| **CountSketch** (one hash and sign per column) | `q=1`: `E‖G‖_F² = (d²+d−2Σℓᵢ²)/m ≤ (d²+d)/m`, at `Sparse/CountSketchExpectation.lean:94` and `Sparse/CountSketchTail.lean:24`. `q>1`: — (CountSketch is SparseStack with `s=1`, which the SparseStack parameters exclude) | yes, `Sparse/CountSketch.lean:81,104` | yes, conditional on the hash, `Sparse/CountSketchMoments.lean:87` | independent hash and sign per column, `Sparse/CountSketch.lean:52` | Rademacher sign symmetry for the second moment, `NLAlib/Probability/Concentration/QuadraticForms/RademacherQuadraticMoments.lean:73,89` | Markov at `q=1`: `Sparse/CountSketchTail.lean:38` gives failure `≤ (d²+d)/(m ε²)`, so `m ≥ (d²+d)/(δε²)` (`:66,:83`) |
| **SRHT** `√(n/k) R H D` | — | true for flat `H` (`H_ij² = 1/n` gives column norm² `(n/k)·k·(1/n) = 1`), not stated | yes, population mean `NLAlib/Sketching/Structured/SRHTCore.lean:99` | **no**: one shared `D`, rows sampled without replacement; independence is used only through the sampling-without-replacement Chernoff bound conditional on `D` | sign symmetry of `D` gives subgaussian rows for flattening: `NLAlib/Sketching/Structured/SRHTFlattening.lean:53,139` | matrix Chernoff on the Gram matrix: `NLAlib/Sketching/Structured/SRHT.lean:104`, `k ≥ 3L ε⁻² log(4d/δ)`, `L = (√d + √(8 log(2n/δ)))²` |
| **OSNAP** (uniform exact-s) | `B = d(3 ŝ² β)^{2q}`, `Sparse/MomentMethod/UniformSparseTail.lean:82` | yes, `Sparse/UniformSparse.lean:278` | implied by H2 + H5, not stated | independent columns, `Sparse/UniformSparse.lean:80`; H4′ whole-column `4q`-wise, `Sparse/MomentMethod/UniformSparseLimitedIndependence.lean:161` | fill/thin coupling, `ŝ ≤ c_b ≤ c*` (`FillThinCoupling.lean:259`) | moment method: `Sparse/SparseEmbedding.lean:86`, `q = max 1 ⌈log₂(d/δ)⌉`, `s < 1356q/ε`, `m < 306456(d+q)/ε²` (`:137`) |
| **SparseStack** (one signed hash per block and column) | `B = d(3 c_b² β)^{2q}`, `Sparse/MomentMethod/Endgame.lean:35` | yes, `Sparse/SparseStack.lean:373` | implied, not stated | independent per (block, column), `Sparse/SparseStackLaw.lean:68`; H4′ `4q`-wise, `Sparse/MomentMethod/SparseStackLimitedIndependence.lean:183` | `E[c_b Y \| X] = X`, `Sparse/IIDComparison/ConditionalBarycenter.lean:347` | moment method: `Sparse/SparseEmbedding.lean:35`, same parameters |
| **Leverage sampling** (ℂ) | — | no | yes, proved inside `NLAlib/Sketching/Sampling/LeverageSampling.lean:60` | iid rows (`Measure.pi`) | n/a | matrix Chernoff: `LeverageSampling.lean:222`, `k ≥ 3d/(βε²) log(2d/δ)`; out of F3 scope (ℂ) |

In the table, `β = (3+√2)(√(D_q/m) + D_q/m + (2q+1)/s)` (`Sparse/MomentMethod/ParameterConstants.lean:87`)
and `c_b ≤ c* < 1.582`.

Reading of the table:
- The *moment* interface (H1, optionally established through H2 + H4 + H5 + H6) is satisfied today by
  SparseStack and OSNAP at every order `q`, and by CountSketch and Gaussian at `q = 1` only.
- SRHT and leverage sampling go through matrix Chernoff, which needs H3 and a uniform bound on the
  rank-one atoms, not H1. A second interface field `chernoffAtoms` (isotropic PSD atoms with
  `λ_max ≤ L`) would cover them. The shared lemma there is
  `NLAlib/Probability/Concentration/Matrix/SamplingWithoutReplacementTails.lean:153`.

## 2. The reusable lemmas inside Sparse, in library vocabulary

There are four, plus one small identity. R2 is already outside Sparse
(`NLAlib/Matrix/Functions/`), as is the deterministic half of R1 (`NLAlib/Matrix/Spectral/`).

**R1. Markov step from a trace moment to `IsSubspaceEmbedding`.**

```lean
theorem measureReal_not_isSubspaceEmbedding_le_integral_trace_pow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k m d : Type*} [Fintype k] [Fintype m] [Fintype d] [DecidableEq d]
    (S : Ω → Matrix k m ℝ) {U : Matrix m d ℝ} (hU : HasOrthonormalCols U)
    {q : ℕ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε)
    (hint : Integrable (fun ω => (((S ω * U)ᵀ * (S ω * U) - 1) ^ (2 * q)).trace) μ) :
    μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U ε} ≤
      (∫ ω, (((S ω * U)ᵀ * (S ω * U) - 1) ^ (2 * q)).trace ∂μ) / ε ^ (2 * q)
```

The proof has three steps:
1. `{¬ IsSubspaceEmbedding} ⊆ {ε < specNorm G}`, the contrapositive of
   `isSubspaceEmbedding_of_specNorm_transpose_mul_self_sub_one_le`
   (`Properties/SubspaceEmbedding/SubspaceEmbedding.lean:95`).
2. `specNorm G ^ (2q) ≤ tr G^{2q}` (`NLAlib/Matrix/Spectral/TracePowerBounds.lean:44`), with
   nonnegativity from `:34`.
3. Mathlib's `mul_meas_ge_le_integral_of_nonneg`.

Current versions:
- `SparseSketch.FiniteLaw.prob_le_norm_le_expect_trace_pow_div` at
  `Sparse/MomentMethod/GramTail.lean:38`, in FiniteLaw form for a Hermitian `A`;
- its embedding form at `GramTail.lean:82` (`sparseStack_ose_failure_tail`) and success form at
  `:109`;
- exact-s duplicates at `Sparse/MomentMethod/UniformSparseTail.lean:33,51`;
- a `4q`-wise copy at `Sparse/MomentMethod/SparseStackLimitedIndependence.lean:200,220`;
- the `q = 1` Frobenius special case inline in `Sparse/CountSketchTail.lean:38`, through
  `specNorm_sq_le_frobSq` (`NLAlib/Matrix/Norms/Core.lean:275`).

The Gram ↔ embedding step is `Sparse/MomentMethod/GramError.lean:98`
(`norm_gramError_le_iff_isSubspaceEmbedding`). It is a wrapper around the library's
`isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le`
(`Properties/SubspaceEmbedding/Gram.lean:46`).

**R2. Trace-power convexity (and Jensen).**
`convexOn_traceEvenPower (d q : ℕ) : ConvexOn ℝ Set.univ (traceEvenPower (d := d) q)` is at
`NLAlib/Matrix/Functions/TracePowerConvexity.lean:356`. Related declarations:
- the line form `convexOn_tracePowerAlong` is at `:325`;
- the domain is `symmetricMatrices d : Submodule ℝ (Matrix (Fin d) (Fin d) ℝ)` (`:41`);
- `traceEvenPower q A = tr (A^(2q))` (`:348`).

The library form wanted is `ConvexOn ℝ {A | A.IsHermitian} (fun A => RCLike.re (A ^ (2*q)).trace)`
over a `Fintype` index, or on `selfAdjoint`. That generalisation is F1 territory, done at port time.

The Jensen step `SparseSketch.FiniteLaw.map_barycenter_le_expect`
(`Sparse/IIDComparison/IndependentCopyLift.lean:323`) is Mathlib's `ConvexOn.map_sum_le` for finite
laws and `ConvexOn.map_integral_le` in general. Drop it.

**R3. iid versus sparse comparison (convex order through a conditional barycenter).**

```lean
theorem integral_convexOn_le_of_barycenter {X Y E : Type*} [Fintype X] [Fintype Y]
    [AddCommGroup E] [Module ℝ E] [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : PMF X) (κ : X → PMF Y) (Φ : X → E) (Ψ : Y → E)
    (hbar : ∀ x, ∑ y, (κ x y).toReal • Ψ y = Φ x)
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ∫ x, f (Φ x) ∂p.toMeasure ≤ ∫ y, f (Ψ y) ∂(p.bind κ).toMeasure
```

The matrix instance takes `E = symmetricMatrices d`, `f = traceEvenPower q` (R2),
`Φ = G_sparse` and `Ψ = c·G_iid`. It gives `E tr G_sparse^{2q} ≤ c^{4q} E tr G_iid^{2q}` once the
model proves two obligations:
- `p.bind κ = iid law`: `Sparse/IIDComparison/ConvexOrder.lean:102,131` and
  `Sparse/IIDComparison/ExactConditionalMatrixTransfer.lean:76,124`;
- `hbar`: `Sparse/IIDComparison/IndependentCopyLift.lean:229` and
  `Sparse/IIDComparison/ExactConditionalMatrixTransfer.lean:197`, both resting on H2 + H4 + H5.

Current versions, each specialised to its model:
- `SparseSketch.unconditional_convex_order` (`Sparse/IIDComparison/ConvexOrder.lean:166`), with its
  pointwise half `conditional_convex_order` (`Sparse/IIDComparison/IndependentCopyLift.lean:362`);
- `SparseSketch.UniformSparse.unconditional_convex_order`
  (`Sparse/IIDComparison/ExactMomentTransfer.lean:95`, pointwise half at `:79`);
- the trace-moment instances `raw_trace_moment_le_scaled_product`
  (`Sparse/IIDComparison/MomentTransfer.lean:135`) and `UniformSparse.trace_moment_le_scaled_product`
  (`Sparse/IIDComparison/ExactMomentTransfer.lean:216`).

The generic lemma was proposed as item 2k (`FiniteLaw.expect_convex_le_of_barycenter`,
`docs/SPARSE_INTEGRATION.md` §3). It was never done (`docs/dedup/S2.md`, open follow-ups).

**R4. Ladder bound for graded operators (the moment method's substitute for a net).** Let the
operator `T = Σ_{δ ∈ {−,0,+}} B_δ` act on a graded finite-dimensional space with grade projections
`P_ν`, where each `B_δ` shifts grade by `δ`. If `‖B_δ P_ν‖ ≤ β` for `ν ≤ 2q`, then
`‖P_0 T^{2q} P_0‖ ≤ (3β)^{2q}`. Summing the `d` vacuum diagonal entries then gives at most
`d (3β)^{2q}`.

Current names:
- `projected_power_norm_le` (`Sparse/Bands/LadderIteration.lean:310`);
- `vacuum_diagonal_sum_le` (`:343`);
- `iid_trace_moment_le_of_band_bounds` (`:392`), which uses the vacuum identity
  `Sparse/FockModel/VacuumMoment.lean:62`.

Today it is typed to the sparse Fock space (`FullOp d m n`, `IsFullGradeShift`), but the argument
is general: words in three letters, walk-to-zero counting. It is the reusable core for any iid
model with an orthogonal-polynomial basis.

**Net/union argument: none in Sparse.** The trace moment bounds `‖G‖` in every direction at once.
- The only case split is `d = 0` (`Sparse/SparseEmbedding.lean:22`, `isSubspaceEmbedding_of_isEmpty`).
- The library's nets live elsewhere, for sketches that do not use moments:
  - `NLAlib/Matrix/Norms/Net.lean:206` (`specNorm_le_div_of_net_quadForm`) and `:361`
    (`exists_finset_net_specNorm_le`);
  - `NLAlib/Probability/Concentration/Basic/Net.lean:32`.
- Union bounds appear only outside Sparse:
  - SRHT row flattening (`NLAlib/Sketching/Structured/SRHTFlattening.lean:139`);
  - the two-stage bad-event split `measureReal_prod_le_bad_add`
    (`NLAlib/ForMathlib/Probability/FiniteProductEvents.lean:33`);
  - JL (`Properties/JL/JL.lean`).

**R5 (small). Hollow Gram identity.** If every column of `S` has unit norm and `UᵀU = I`, then
`(S U)ᵀ(S U) − I = Σ_{i≠j} (SᵀS)_{ij} u_i u_jᵀ`. The `u_i` are the rows of `U`.

It exists three times:
- `Sparse/SparseStack.lean:373`;
- `Sparse/UniformSparse.lean:278`;
- CountSketch, entrywise as a hollow quadratic form, `Sparse/CountSketch.lean:81,104`.

It should become one lemma about `IsSubspaceEmbedding`-free Gram matrices with unit columns.

## 3. Every other file in `Sparse/`: rebuild or drop

The definitions used here:
- `rebuild`: the file's mathematics is needed for the two headline theorems.
- `drop`: either the file is off the headline path, or it is on the path only as port
  representation. Port representation means the FiniteLaw machinery, the `Frame` ↔ matrix bridges,
  Gram wrappers, conclusion bundles and transports. The new repository replaces these with Mathlib
  `PMF`/`Measure`, `HasOrthonormalCols` and the library Gram lemma.
- `keep`: the four CountSketch files. They are not part of the sparse-stack proof but a separate
  endpoint (`countsketch-ose`), already written in `Measure` and library vocabulary. Labelling
  them `drop` would lose the endpoint that the F3 conversion step targets, so I used a third label.

Aggregators (`Bands`, `Bands/{Directional,Heavy,Light,Mixed}`, `FiniteLaw`, `FockModel`,
`IIDComparison`, `MomentMethod`) are excluded. `lines` is today's `wc -l`. The JSON companion also
carries `on_headline_path` and an approximate count of declarations reached from the headline
theorems.

**Totals.**

| action | files | lines |
|---|---|---|
| rebuild | 95 | 24459 |
| drop | 16 | 2729 |
| keep | 4 | 427 |
| total | 115 | 27615 |

Two checks:
- The headline theorems' import closure contains every content file except 9: the two
  limited-independence files, `FiniteLaw/LocalMoments` and the two transport/finite-index wrappers
  (these five are marked "off the headline path" below), and the four CountSketch files.
- Three more files are imported but no declaration in them is used:
  - `Bands/Light/ZeroBlock`, which is dead code;
  - `MomentMethod/IndependentFrame` together with its `FiniteLaw/BinaryProduct`, which is reached
    only from an unused corollary in `SparseStackTheorem`.

**Sparse/ (top level)**

| file | lines | action | reason |
|---|---|---|---|
| `CountSketch` | 112 | keep | not part of the sparse-stack proof: separate countsketch-ose endpoint, already Measure + library vocabulary; port as Sketching/CountSketch |
| `CountSketchExpectation` | 106 | keep | exact CountSketch second moment (d^2+d-2 sum lev^2)/m; separate endpoint |
| `CountSketchMoments` | 113 | keep | CountSketch conditional second moment (Rademacher quadratic forms); separate endpoint, already library vocabulary |
| `CountSketchTail` | 96 | keep | CountSketch endpoint, already in the target failure shape (:83); q=1 instance of the Markov step |
| `SparseEmbedding` | 147 | rebuild | hosts the two headline theorems (:35, :86); restate in the failure shape mu.real {not IsSubspaceEmbedding} <= delta |
| `SparseEmbeddingTransport` | 79 | drop | _of_map_eq transport to arbitrary probability spaces; superseded by the HasLaw corollary convention of F2 (re-home its 2 sparse-ose tags) (off the headline path) |
| `SparseFiniteIndex` | 114 | drop | Fintype-index restatement via reindexing; the rebuild states the headline over arbitrary Fintype indices directly (re-home its 2 sparse-ose tags) (off the headline path) |
| `SparseLaws` | 64 | rebuild | sparseStackMeasure/uniformSparseMeasure are the measures in the headline statements; becomes the PMF.toMeasure definitions |
| `SparseStack` | 424 | rebuild | SparseStack model (sparseStackMatrix, signed basis, hollow Gram identity gramError_eq_hollow :373); appears in the headline statement |
| `SparseStackLaw` | 159 | rebuild | selector law of the headline; restate as PMF.uniformOfFintype product / Measure.pi instead of FiniteLaw |
| `UniformSparse` | 319 | rebuild | OSNAP/exact-s model (uniformSparseMatrix, hollow Gram :278); appears in the headline statement; law becomes a PMF |

**Sparse/FiniteLaw/**

| file | lines | action | reason |
|---|---|---|---|
| `FiniteLaw/BinaryProduct` | 112 | drop | binary product law, only used by the independent-frame corollary (off the headline path): Measure.prod |
| `FiniteLaw/Expectation` | 282 | drop | D1 real-weighted finite law (expect, prob, markov, prob_compl): replaced by Mathlib PMF/Measure, integral, measureReal |
| `FiniteLaw/IndependentProduct` | 189 | drop | finite independent product law: replaced by Measure.pi / PMF product |
| `FiniteLaw/LocalMoments` | 262 | drop | MatchesUpTo/HasLocalDegree k-wise matching; only used by the limited-independence side results (off the headline path). Idea survives as interface hypothesis H4 |
| `FiniteLaw/ToMeasure` | 78 | drop | FiniteLaw -> PMF/Measure bridge; disappears when laws are PMFs from the start |
| `FiniteLaw/Uniform` | 126 | drop | uniform/map finite laws: replaced by PMF.uniformOfFintype and PMF.map |

**Sparse/MomentMethod/**

| file | lines | action | reason |
|---|---|---|---|
| `MomentMethod/Assembly` | 130 | drop | MainConclusions bundle (bundles are deleted at port time); canonicalS_pos/canonicalB_pos fold into MomentParameters |
| `MomentMethod/Endgame` | 286 | rebuild | moment chain sparse <= c_b^{4q} iid <= d(3c_b^2 beta)^{2q}, Markov and rounding (:35, :83, :115); on the headline path |
| `MomentMethod/Frame` | 284 | rebuild | Parseval-frame analysis/synthesis identities used throughout the band proofs; rebuild as lemmas on the rows of U with HasOrthonormalCols U, dropping the Frame structure (D2) |
| `MomentMethod/FrameOfMatrix` | 101 | drop | Frame <-> matrix representation bridge; disappears once Frame is replaced by HasOrthonormalCols |
| `MomentMethod/GramError` | 106 | drop | sketchGram/embeddedGram/gramError wrappers; replaced by (S*U)^T*(S*U)-1 and isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le (Properties/SubspaceEmbedding/Gram.lean:46) |
| `MomentMethod/GramTail` | 140 | rebuild | hosts reusable lemma R1 (Markov step, :38/:82); rebuild once, generically, in Sketching/Properties; the SparseStack instances drop |
| `MomentMethod/IndependentFrame` | 89 | drop | random-frame-independent-of-sketch corollary, off the headline path; Fubini in the Measure world |
| `MomentMethod/MomentOrder` | 108 | rebuild | q = max 1 ceil(log2(d/delta)) facts used by the final rounding |
| `MomentMethod/MomentParameters` | 225 | rebuild | rounded envelope and moment base < 1/2; rounded_scalar_failure_le_delta (:170), main_parameter_package (:205) |
| `MomentMethod/ParameterConstants` | 204 | rebuild | explicit constants q, s, b, m, c*, 3+sqrt2, L=90c*^2 of the headline statements |
| `MomentMethod/RoundedScales` | 315 | rebuild | ceiling estimates for s, b, m; s<1356q/eps, m<306456(d+q)/eps^2 |
| `MomentMethod/SparseStackLimitedIndependence` | 423 | drop | 4q-wise SparseStack side result, off the headline path; candidate atlas sparse-limited-independence, re-derive from interface hypothesis H4 (trace moment has local degree 4q, :160/:183) |
| `MomentMethod/SparseStackTheorem` | 159 | rebuild | only rounded_band_bound (:33) is needed (band envelope at rounded parameters); the MainConclusions/MatrixMainConclusions bundles and frame transport drop |
| `MomentMethod/UniformSparseLimitedIndependence` | 383 | drop | whole-column 4q-wise OSNAP side result, off the headline path; same remark as SparseStackLimitedIndependence (:139/:161) |
| `MomentMethod/UniformSparseRoundedBounds` | 223 | rebuild | exact-s rounding to <= delta (:31, :206); merges with Endgame rounding once the moment bound is the interface hypothesis |
| `MomentMethod/UniformSparseTail` | 167 | rebuild | exact-s moment bound trace_moment_le_of_band_bounds (:82) is needed; its Markov instances (:33, :51) are duplicates of R1 and drop |
| `MomentMethod/UniformSparseTheorem` | 145 | drop | UniformExactSMainConclusions bundle and Frame-to-matrix transport; the content is UniformSparseRoundedBounds + the endpoint in SparseEmbedding |

**Sparse/IIDComparison/**

| file | lines | action | reason |
|---|---|---|---|
| `IIDComparison/ConditionalBarycenter` | 354 | rebuild | one-column conditional barycenter E[c_b Y \| X] = X (:347), from sign flips (:159, :177): hypothesis H5 |
| `IIDComparison/ConvexOrder` | 193 | rebuild | unconditional convex order sparse <= iid (:166) via mixture = iid law (:102, :131); hosts R3 |
| `IIDComparison/DistributionBridges` | 273 | rebuild | needed identities sparseVectorError_eq_gramError (:56) and iidVectorError_eq_flattened_iidGramError (:210); the law/flatten bridges (:33, :78-:159) disappear if the iid model is indexed by Fin s x Fin b |
| `IIDComparison/ExactColumnMarginals` | 168 | rebuild | uniform exact-s column marginal of the coupling |
| `IIDComparison/ExactConditionalBarycenter` | 194 | rebuild | exact-s conditional barycenter (:181): H5 for OSNAP |
| `IIDComparison/ExactConditionalMatrixTransfer` | 239 | rebuild | exact-s mixture = iid column law (:76) and matrix barycenter transfer (:197, :227) |
| `IIDComparison/ExactConditionalSupport` | 323 | rebuild | conditional support moments of the exact-s coupling |
| `IIDComparison/ExactCoordinateSymmetry` | 269 | rebuild | coordinate-flip identities for exact-s conditional moments |
| `IIDComparison/ExactIIDMatrixError` | 329 | rebuild | exact-s iid matrix error and its flattening to the product-Fock model |
| `IIDComparison/ExactMomentTransfer` | 234 | rebuild | exact-s convex order (:95) and trace-moment comparison (:216); instance of R3 with R2 |
| `IIDComparison/ExactSelectionSymmetry` | 270 | rebuild | signed-permutation invariance of the exact-s selection kernel |
| `IIDComparison/ExactSignActions` | 291 | rebuild | signed coordinate actions on exact-s columns used by the exact-s symmetry arguments |
| `IIDComparison/FillThinCoupling` | 445 | rebuild | exact-s fill/thin coupling (jointColumnLaw :432), exactScale <= c_b (:259): H5 for OSNAP |
| `IIDComparison/IndependentCopyLift` | 374 | rebuild | lifts the coupling to all sites; off-diagonal matrix barycenter (:229) via independence at distinct sites (:134); Jensen (:323, :362); hosts part of R3 |
| `IIDComparison/MomentTransfer` | 171 | rebuild | trace-moment comparison E tr G_sparse^{2q} <= c_b^{4q} E tr G_iid^{2q} (:135); instance of R3 with R2 |
| `IIDComparison/SelectionKernel` | 116 | rebuild | support-selection kernel of the SparseStack martingale coupling |
| `IIDComparison/SelectorMarginals` | 269 | rebuild | identifies the selector marginal of the joint coupling law (sign/swap symmetry) |
| `IIDComparison/TernaryCoordinateLaws` | 226 | rebuild | iid ternary vector law, p0 = (1-1/b)^b, c_b = (1-p0)^{-1} <= c* (:201, :219) |

**Sparse/FockModel/**

| file | lines | action | reason |
|---|---|---|---|
| `FockModel/FockSpace` | 366 | rebuild | iid-model trace moment (H6): Euclidean realization and exact-grade projections |
| `FockModel/LadderMatrices` | 207 | rebuild | iid-model trace moment (H6): three-level creation/annihilation matrices of the ternary Jacobi operator |
| `FockModel/LadderWords` | 343 | rebuild | iid-model trace moment (H6): typed ladder-word inventory (shift x heaviness cells) |
| `FockModel/OccupationPattern` | 241 | rebuild | iid-model trace moment (H6): Level/Site/Pattern and total occupation grade of the product basis |
| `FockModel/ProductBasis` | 385 | rebuild | iid-model trace moment (H6): iid product law iidLaw (:35) and its orthonormal product basis |
| `FockModel/SiteKernels` | 252 | rebuild | iid-model trace moment (H6): one-site and pair kernels on the pattern basis |
| `FockModel/TensorOperators` | 102 | rebuild | iid-model trace moment (H6): external rank-one (vecMulVec) factors tensored with pattern kernels |
| `FockModel/TernaryJacobi` | 336 | rebuild | iid-model trace moment (H6): ternary law eta in {0, +-sqrt b}, mean 0 (:160), variance 1 (:168), orthonormal polynomial basis |
| `FockModel/VacuumMoment` | 185 | rebuild | iid-model trace moment (H6): E tr G_iid^k = vacuum diagonal of the multiplication operator^k (:62) |
| `FockModel/WeightedBasis` | 258 | rebuild | iid-model trace moment (H6): weighted orthonormal basis and multiplication operators (vacuum moment identity behind VacuumMoment) |

**Sparse/Bands/ (top level)**

| file | lines | action | reason |
|---|---|---|---|
| `Bands/BandAssembly` | 191 | rebuild | iid-model band bound (H6): assembly of the three band estimates from sector components |
| `Bands/BandEnvelope` | 108 | rebuild | iid-model band bound (H6): band envelope 3+sqrt2 (concrete_band_envelope :32, concrete_band_bound_le_beta :96) |
| `Bands/CoefficientBounds` | 200 | rebuild | iid-model band bound (H6): scalar coefficient bounds for normalized bands (m = s*b) |
| `Bands/EnvelopeArithmetic` | 184 | rebuild | iid-model band bound (H6): scalar assembly of the uniform band envelope |
| `Bands/GlobalBands` | 323 | rebuild | iid-model band bound (H6): global bands as sums over rows and ordered distinct column pairs, nine-cell partition |
| `Bands/Ladder` | 255 | rebuild | iid-model band bound (H6): multiplication operator = sum of the three grade bands |
| `Bands/LadderIteration` | 407 | rebuild | iid-model band bound (H6): ladder iteration: E tr G_iid^{2q} <= d(3 beta)^{2q} from band bounds (:392) |
| `Bands/NamedBands` | 227 | rebuild | iid-model band bound (H6): named band families L/X/Y/H |
| `Bands/ScalarBounds` | 158 | rebuild | iid-model band bound (H6): square-root/scalar envelope inequalities |

**Sparse/Bands/Directional/**

| file | lines | action | reason |
|---|---|---|---|
| `Bands/Directional/MarkedCoefficients` | 414 | rebuild | iid-model band bound (H6), Directional sector: Directional marked coefficient formulas |
| `Bands/Directional/MarkedReindexing` | 407 | rebuild | iid-model band bound (H6), Directional sector: Directional marked-pair reindexing |
| `Bands/Directional/NormalizedBands` | 343 | rebuild | iid-model band bound (H6), Directional sector: Normalized directional mixed-band estimates |
| `Bands/Directional/OccupationEnergy` | 315 | rebuild | iid-model band bound (H6), Directional sector: Directional supported occupation energy |
| `Bands/Directional/OccupationProfiles` | 281 | rebuild | iid-model band bound (H6), Directional sector: Directional occupation profiles |
| `Bands/Directional/OutputEnergy` | 441 | rebuild | iid-model band bound (H6), Directional sector: Directional output synthesis energy |
| `Bands/Directional/RestrictedBounds` | 195 | rebuild | iid-model band bound (H6), Directional sector: Directional exact-grade operator bounds |
| `Bands/Directional/SiteTransitions` | 310 | rebuild | iid-model band bound (H6), Directional sector: Directional two-site transitions |

**Sparse/Bands/Heavy/**

| file | lines | action | reason |
|---|---|---|---|
| `Bands/Heavy/AnalysisOperators` | 194 | rebuild | iid-model band bound (H6), Heavy sector: Concrete heavy analysis operators |
| `Bands/Heavy/CreationEnergy` | 116 | rebuild | iid-model band bound (H6), Heavy sector: Heavy creation occupation-energy estimate |
| `Bands/Heavy/DemotionEnergy` | 156 | rebuild | iid-model band bound (H6), Heavy sector: Heavy demotion occupation-energy estimate |
| `Bands/Heavy/DiagonalEnergy` | 234 | rebuild | iid-model band bound (H6), Heavy sector: Heavy same-site diagonal energy |
| `Bands/Heavy/GradeProjections` | 183 | rebuild | iid-model band bound (H6), Heavy sector: Heavy middle-grade projections |
| `Bands/Heavy/LoweringBound` | 171 | rebuild | iid-model band bound (H6), Heavy sector: Restricted heavy lowering operator bound |
| `Bands/Heavy/MarkedSites` | 341 | rebuild | iid-model band bound (H6), Heavy sector: Marked heavy-site transitions |
| `Bands/Heavy/NormalizedBands` | 132 | rebuild | iid-model band bound (H6), Heavy sector: Normalized heavy-band estimates |
| `Bands/Heavy/OccupationIdentity` | 185 | rebuild | iid-model band bound (H6), Heavy sector: Exact heavy diagonal occupation identities |
| `Bands/Heavy/PreservingBound` | 243 | rebuild | iid-model band bound (H6), Heavy sector: Restricted heavy preserving operator bound |
| `Bands/Heavy/PreservingGram` | 254 | rebuild | iid-model band bound (H6), Heavy sector: Heavy preserving Gram factorization |
| `Bands/Heavy/RaisingBound` | 179 | rebuild | iid-model band bound (H6), Heavy sector: Restricted heavy raising operator bound |
| `Bands/Heavy/RowFactorization` | 243 | rebuild | iid-model band bound (H6), Heavy sector: Heavy raising row factorization |

**Sparse/Bands/Light/**

| file | lines | action | reason |
|---|---|---|---|
| `Bands/Light/AbstractContraction` | 154 | rebuild | iid-model band bound (H6), Light sector: Light-sector contraction estimate |
| `Bands/Light/AnalysisGram` | 387 | rebuild | iid-model band bound (H6), Light sector: Light creation analysis Gram estimates |
| `Bands/Light/BlockDecomposition` | 240 | rebuild | iid-model band bound (H6), Light sector: The finite direct sum of exact heavy/light pattern blocks |
| `Bands/Light/CrossContraction` | 307 | rebuild | iid-model band bound (H6), Light sector: Concrete cross-map contractions on common spectator fibers |
| `Bands/Light/CrossCoordinates` | 176 | rebuild | iid-model band bound (H6), Light sector: Common spectator coordinates for two particle slots |
| `Bands/Light/GradeNorm` | 289 | rebuild | iid-model band bound (H6), Light sector: The shared-leg norm bound on a fixed grade |
| `Bands/Light/GramQuadratic` | 140 | rebuild | iid-model band bound (H6), Light sector: The dimension-plus-particle-count shared-leg quadratic estimate |
| `Bands/Light/HardCoreEmbedding` | 247 | rebuild | iid-model band bound (H6), Light sector: Normalized hard-core symmetrization and compression bounds |
| `Bands/Light/LabelledSlots` | 282 | rebuild | iid-model band bound (H6), Light sector: Labelled particle slots and their individual synthesis matrices |
| `Bands/Light/LegalTransitions` | 247 | rebuild | iid-model band bound (H6), Light sector: Legal physical light moves and fixed-block preservation |
| `Bands/Light/MixedFactorization` | 159 | rebuild | iid-model band bound (H6), Light sector: Light synthesis and mixed row factors |
| `Bands/Light/MoveOrbits` | 242 | rebuild | iid-model band bound (H6), Light sector: Correspondence between labelled spectators and legal physical moves |
| `Bands/Light/NormalizedBands` | 326 | rebuild | iid-model band bound (H6), Light sector: Normalized light-band estimates |
| `Bands/Light/OrbitCompression` | 340 | rebuild | iid-model band bound (H6), Light sector: The exact orbit-sum and physical compression identity |
| `Bands/Light/PatternWords` | 362 | rebuild | iid-model band bound (H6), Light sector: Canonical pattern words and permutation orbits |
| `Bands/Light/PreservingDiagonal` | 418 | rebuild | iid-model band bound (H6), Light sector: Light preserving diagonal energy |
| `Bands/Light/RowFactorization` | 359 | rebuild | iid-model band bound (H6), Light sector: Light raising row factorization |
| `Bands/Light/SharedLegOperators` | 364 | rebuild | iid-model band bound (H6), Light sector: Creation, annihilation, and one-particle shared-leg operators |
| `Bands/Light/SynthesisBounds` | 382 | rebuild | iid-model band bound (H6), Light sector: The combined synthesis matrix and its two Gram bounds |
| `Bands/Light/ZeroBlock` | 110 | drop | dead code: none of its 6 declarations is used anywhere (imported by Light/RowFactorization only) |

**Sparse/Bands/Mixed/**

| file | lines | action | reason |
|---|---|---|---|
| `Bands/Mixed/NormalizedBands` | 373 | rebuild | iid-model band bound (H6), Mixed sector: Normalized mixed-band estimates |
| `Bands/Mixed/RestrictedBounds` | 199 | rebuild | iid-model band bound (H6), Mixed sector: Mixed exact-grade operator bounds |
| `Bands/Mixed/RowFactorization` | 439 | rebuild | iid-model band bound (H6), Mixed sector: Mixed light-heavy row factorizations |

What survives as *new-repository* material once the rebuild targets the interface:
- R1–R5;
- the model files (`SparseStack`, `SparseStackLaw`, `UniformSparse`, `SparseLaws`);
- the coupling (H5: the IIDComparison files);
- the iid-model moment bound (H6: FockModel + Bands, 62 files);
- the parameter files.

Two consolidations are possible once H1 is the interface field. The two rounding chains collapse
into one (`MomentMethod/Endgame` and `MomentMethod/UniformSparseRoundedBounds`), and the two Markov
copies collapse into R1.

## 4. The single conclusion shape: which endpoints have it

The target is `μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U ε} ≤ δ` for `U` with
`HasOrthonormalCols U`.

The conversion step can write it inline in each endpoint, which needs no new definition and fits
the freeze rules best. Alternatively it can name it once in `Sketching/Properties/` (e.g.
`Properties/SubspaceEmbedding/Basic.lean`):

```lean
/-- `S` is an `(ε, δ)` oblivious subspace embedding for `d`-dimensional subspaces under `μ`. -/
def IsObliviousSubspaceEmbedding {Ω k m : Type*} [MeasurableSpace Ω] [Fintype k] [Fintype m]
    (μ : Measure Ω) (S : Ω → Matrix k m ℝ) (d : Type*) [Fintype d] [DecidableEq d] (ε δ : ℝ) : Prop :=
  ∀ U : Matrix m d ℝ, HasOrthonormalCols U → μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U ε} ≤ δ
```

| endpoint | today's conclusion | file:line | gap to the target shape |
|---|---|---|---|
| **CountSketch** | `(countSketchLaw).real {z \| ¬ IsSubspaceEmbedding (countSketchMatrix z.1 z.2) U ε} ≤ δ` | `Sparse/CountSketchTail.lean:83` (`measure_countSketch_embedding_failure_le_of_rows`) | **none: already the target shape.** `:38` and `:66` are the Gram-form steps before it. The law lives on `(ι → ρ) × (ι → ℝ)` with real Rademacher signs, so `S ω = countSketchMatrix ω.1 ω.2` |
| **Gaussian** | `1 − ENNReal.ofReal δ ≤ gaussianMatrix k m {G \| IsSubspaceEmbedding ((1/√k) • Matrix.of G) U ε}` (success form, ENNReal) | `NLAlib/Sketching/Gaussian/GaussianEmbedding.lean:72` | **stops one line short.** The proof establishes `μ Eᶜ ≤ ENNReal.ofReal δ` at `:81` (`suffices hc`); then `ENNReal.toReal_le_of_le_ofReal hδ0.le hc` gives `μ.real Eᶜ ≤ δ`. The event is never proved measurable, which `μ.real` does not need. F2 rewrites this file (`Matrix.of.symm` at `:134`, `gaussianMatrix` moves to `Matrix`), so the conversion should land with or after F2's `gaussianMatrix` PR |
| **SRHT** (distinct rows) | `(srhtLaw hk {ω \| ε < specNorm ((srhtSketch H ω.1 ω.2 * U)ᵀ * (srhtSketch H ω.1 ω.2 * U) − 1)}).toReal ≤ δ` (**Gram bound**, `.toReal`) | `NLAlib/Sketching/Structured/SRHT.lean:104` (sharp), `:141` (manuscript), `:209` (capped), `:251` (Walsh), `:267`, `:281` (capped width); zero-failure cases `:173`, `:190`; conditional step `:38` | **never reaches `IsSubspaceEmbedding`.** Conversion: `{¬ IsSubspaceEmbedding (S ω) U ε} ⊆ {ε < specNorm G}` by the contrapositive of `Properties/SubspaceEmbedding/SubspaceEmbedding.lean:95`, then `measureReal_mono`; `(μ s).toReal` is `μ.real s` by `measureReal_def`. Carry the side conditions: `[NeZero d]` (`d = 0` comes from `:190`), `ε < 1` strict, `δ < 1` strict |
| **SRHT with replacement** | same Gram form | `NLAlib/Sketching/Structured/SRHTWithReplacement.lean:128`, `:167`, `:191`; zero rank `:206`; conditional `:87` | same conversion as SRHT. The brief does not name it, but it is the same file family |
| **Leverage sampling** | `(Measure.pi …) {ω \| ∃ x, ‖S(Ax)‖² < (1−ε)‖Ax‖² ∨ (1+ε)‖Ax‖² < ‖S(Ax)‖²}).toReal ≤ δ` over ℂ, on `range A ⊆ range U`; the Gram step is `‖(SU)ᴴ(SU) − 1‖ ≥ ε` | `NLAlib/Sketching/Sampling/LeverageSampling.lean:222`; Gram step `:60` | morally the failure shape, but over ℂ with an inline predicate. `IsSubspaceEmbedding` is ℝ-only (`Properties/SubspaceEmbedding/Basic.lean:27`). Out of F3 scope per the brief; it becomes convertible once `IsSubspaceEmbedding` is `RCLike` (F1 / port) |
| **SparseStack, OSNAP** (Sparse, untouched) | success form `1 − δ ≤ μ.real {IsSubspaceEmbedding …}`; Gram failure form `μ.real {ε < specNorm …} ≤ δ` | `Sparse/SparseEmbedding.lean:35`, `:86` (success); `:65`, `:117` (Gram); the internal failure form is `Sparse/MomentMethod/Endgame.lean:115` (FiniteLaw) | not converted here (Sparse is frozen). The rebuild should state the failure shape directly; from today's success form it is `measureReal_compl` |

**Scope of the conversion step:**
- CountSketch is done.
- Gaussian: about 5 lines, after F2.
- SRHT: about 10 lines per endpoint, or one bridging lemma
  `measureReal_not_isSubspaceEmbedding_le_of_gram` in `Properties/` that every Gram-form endpoint
  calls. That lemma is the deterministic half of R1 and is worth stating once.
- Leverage sampling and Sparse are out of scope.

**Collision with F2's acceptance grep.** `grep -rn "_of_map_eq" NLAlib` will find
`Sparse/SparseEmbeddingTransport.lean:22,54` and `Sparse/FiniteLaw/ToMeasure.lean:68`. They carry
two `sparse-ose` tags. Either F2 excludes `Sketching/Sparse` from that check, or it touches Sparse,
which F3 forbids. The coordinator should decide.

## 5. Summary

- **The interface.** The moment method needs one hypothesis of a sketch law: H1, an oblivious bound
  `∫ tr G^{2q} ≤ B(d,q)` for every orthonormal `U`. R1 turns it into
  `μ.real {¬ IsSubspaceEmbedding} ≤ B/ε^{2q}`. Everything else in the sparse proof establishes H1
  for two specific laws:
  - H2: unit columns;
  - H4: column independence, or `4q`-wise (H4′);
  - H5: a sign-symmetric martingale coupling to an iid ternary model, with constant `c ≤ 1.582`;
  - H6: the iid model's own bound `d(3β)^{2q}`, which accounts for 62 files of Fock and band
    machinery.
- **Coverage.** H1 is proved at all orders for SparseStack and OSNAP, and at `q = 1` for CountSketch
  and (implicitly) Gaussian, both with `(d²+d)/m`. SRHT and leverage sampling use matrix Chernoff
  (H3 plus bounded atoms) and would need a second interface field.
- **Reusable lemmas.** R1 (Markov to `IsSubspaceEmbedding`), R2 (`convexOn_traceEvenPower`, already
  outside Sparse), R3 (convex order through a conditional barycenter, to be stated over `PMF`), and
  R4 (ladder bound for graded operators). R5, the hollow Gram identity, is a small extra. There is
  no net or union bound in Sparse.
- **Files.** Of the 115 content files (27,615 lines): 95 are `rebuild` (24,459), 16 are `drop`
  (2,729) and the 4 CountSketch files are `keep` (427). The drops are:
  - the FiniteLaw layer (6 files);
  - the Frame/Gram wrappers and bundles (4);
  - the off-path side results (limited independence ×2, independent frame);
  - the transport and finite-index wrappers (2);
  - one dead file (`Bands/Light/ZeroBlock`).
- **Conclusion shape.** CountSketch already has it (`Sparse/CountSketchTail.lean:83`). Gaussian is
  one line short (`GaussianEmbedding.lean:81`, ENNReal success form; convert after F2). SRHT stops
  at the Gram bound in `.toReal` form (`SRHT.lean:104,141,209,251,267,281`, plus the
  with-replacement twins) and needs the Gram ⇒ embedding step `SubspaceEmbedding.lean:95`.
  Leverage sampling (ℂ) and Sparse are out of scope.
