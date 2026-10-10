# Round 6: fill the tree (audit follow-up)

Read `docs/STANDARDS.md`, `docs/ROUND1_BRIEF.md` (working rules: `lake env lean <file>` for
single-file checks, `lake build NLAlib.<Module>` for an olean you or another group needs, wait and
retry on a Lake lock, never a full `lake build`, no atlas edits, every file warning-free) and
`CONTRIBUTING.md` § "Assuming is encouraged". Then read the audit report(s) your group cites: the
item ids below (`G0 C5`, `G2 A2`, …) refer to `docs/audit/G0.md` … `G3.md`, which hold the
precise statements, proof sketches, Mathlib names and files. Use those statements; deviate only
when Lean forces it, and say so.

Policy for this round. Prove what you can. When a *well-known* fact will not close, state it as a
named scaffold (`SCAFFOLD: <atlas id>` docstring, `sorry` body, statement checked against the
source with theorem number) and keep building on it; a scaffold with a correct statement is a
success, an abandoned target is not. Never scaffold something you are not sure is true as
written. Constants explicit, `[Fintype ι]` unless a Gaussian law is involved, no `Fin`-only
statements where a general index type works.

Layering facts for this round: `quadForm` is now `NLAlib.Matrix.QuadForm` (layer 0) and the
public Hanson–Wright theorems are `NLAlib.Concentration.HansonWright` (layer 1). Krylov is
layer 1 (imports Matrix, Polynomial, ForMathlib only). Polynomial facts: `NLAlib/Polynomial/*`
(`inv_eval_T_real_le_of_forall_abs_eval_le`, `abs_eval_chebyshevResidual_le_two_mul_pow`,
`exists_degree_lt_abs_eval_sub_inv_le`, `chebyshevAmplifier`, Markov, interpolation).

## Groups (exclusive file ownership; create the new files named)

**R6-A — matrix spectral theory** (`NLAlib/Matrix/Norms.lean`, `NLAlib/Matrix/EckartYoung.lean`,
new `Matrix/PolynomialCalculus.lean`, `Matrix/CourantFischer.lean`, `Matrix/Weyl.lean`,
`Matrix/VonNeumann.lean`, and `NLAlib/Matrix.lean` for imports). Do in this order and build the
olean after each of the first two steps, because groups C and D poll for them:
1. G0 C1 (spectral-norm helpers, into `Norms.lean`) and G0 C5 / G3 C1 (`specNorm_aeval_le` and
   the vector / energy forms `‖p(A)v‖ ≤ max|p(λᵢ)| ‖v‖`, into `PolynomialCalculus.lean`).
   `lake build NLAlib.Matrix.Norms NLAlib.Matrix.PolynomialCalculus`.
2. G0 C4 (the von Neumann rank corollary `⟨X,E⟩ ≤ √r ‖X‖_F ‖E‖` for `rank X ≤ r`, into
   `VonNeumann.lean`) and G0 C3 (`specNorm (A − truncatedSVD A k) = σ_k`, into `EckartYoung.lean`).
   `lake build NLAlib.Matrix.VonNeumann NLAlib.Matrix.EckartYoung`.
3. G0 A1 Courant–Fischer (prove it; scaffold the two halves if it does not close), then
   G0 B1 (singular-value form), B2 (Weyl `σ_{i+j}(A+B) ≤ σ_i(A)+σ_j(B)`), B3 (`|σ_k(A+E)−σ_k(A)| ≤ ‖E‖`),
   B5 (Eckart–Young spectral lower bound), B8 (Cauchy interlacing), B6, B7.
4. G0 A2 full von Neumann trace inequality (prove via Ky Fan if feasible, else scaffold) and
   B4 Mirsky.

**R6-B — chi-square, the law of Gx, and the JL scaffold**
(`NLAlib/Gaussian/Extreme/ChiSquare.lean`, new `NLAlib/Gaussian/LinearImage.lean`,
`NLAlib/ForMathlib/Analysis/Real.lean`, `NLAlib/Sketching/JL.lean`, aggregators `Gaussian.lean`
for the new import). Goal: `jl_distributional` proved, the four `jl_lemma*` declarations sorry-free.
1. G1 C1 chi-square upper tail (Chernoff and Laurent–Massart forms) and G1 C2 sharp lower tail
   (make `measureReal_sum_sq_le_le_exp_mul` public under a STANDARDS name, add the Laurent–Massart
   lower form). Build `NLAlib.Gaussian.Extreme.ChiSquare`.
2. G1 C3 / G2 C10: law of `G x` for a unit vector, `gaussianMatrix_map_transpose`,
   `gaussianMatrix_map_mul_right` (into `LinearImage.lean`). Build it; group C polls for it.
3. The two log inequalities (G2 C1(d)) into `ForMathlib/Analysis/Real.lean`.
4. Discharge `jl_distributional` (G2 C1); remove the SCAFFOLD docstring; re-check `JL.lean`.
5. If time remains: G1 C9 (`HasSubgaussianMGF` of the Gaussian).

**R6-C — sketching and low-rank** (new `NLAlib/LowRank/SpectralRangeFinder.lean`,
`LowRank/PowerIteration.lean`, `LowRank/Nystrom.lean`, `Sketching/Leverage.lean`,
`Sketching/GaussianEmbedding.lean`, `Sketching/ApproxMultiplication.lean`; aggregators
`LowRank.lean`, `Sketching.lean`). Poll `lake build NLAlib.Matrix.Norms` (R6-A step 1) before
starting item 1, and `NLAlib.Gaussian.LinearImage` (R6-B step 2) before item 5.
1. G2 C4 / G0 C2: `hmt-9-1-spectral` with exactly the hypotheses of `frobSq_residual_le_of_range_subset`.
2. G2 C2 `nystrom-structural` (exact identity, no square root) and C7 `nystrom-randomized`.
3. G2 C3 `leverage-scores`.
4. G2 A2 HMT Prop 8.6 (`‖PA‖^{2q+1} ≤ ‖P(AAᵀ)^qA‖`, prove if feasible, else scaffold) and
   B1 `power-iteration-deterministic` (HMT Thm 9.2).
5. G2 C8 `gaussian-ose` with the explicit `k ≥ 18(d + 2 log(2/δ))/ε²`, and C6 `amm-ose` (constant 1).
6. If time remains: G2 B2 `rsvd-spectral-expected` (HMT Thm 10.6).

**R6-D — Krylov, estimation, solvers** (`NLAlib/Krylov/**` new files `SpectralMeasure.lean`,
`CG.lean`, `GaussQuadrature.lean`, `Lanczos.lean`; `NLAlib/Estimation/**` new files
`HutchinsonTail.lean`, `Diagonal.lean`, `Unbiased.lean`, and `HutchinsonLaws.lean` for item 7;
`NLAlib/Solvers/**`; aggregators). Poll `lake build NLAlib.Matrix.PolynomialCalculus` (R6-A
step 1) before item 2.
1. G3 C2 `spectral-measure` (definition and `uᵀf(A)u = ∫ f dμ_u`), in `Krylov/SpectralMeasure.lean`.
2. G3 C3 `cg-convergence`: CG iterate defined as the A-norm minimiser over `krylovSpace`, existence,
   the polynomial form, and the κ-bound from `abs_eval_chebyshevResidual_le_two_mul_pow`.
3. G3 C5 `lanczos-gauss-quadrature` exactness (any orthonormal basis containing the Krylov space)
   and its error bound; G3 C13 SLQ for `1/x`.
4. G3 C6 `hutchinson-tail` from `NLAlib.Concentration.HansonWright` with the explicit constant.
5. G3 C8 diagonal estimator, C11 Hutch++ / XTrace unbiasedness.
6. G3 C12 Kaczmarz extensions (inconsistent, rank-deficient, sketch-and-project).
7. Last: when `NLAlib.Concentration.Scalar.Rademacher` exists (R6-E step 1), delete the
   `rademacherMeasure` definition from `Estimation/HutchinsonLaws.lean` and import R6-E's file.
8. If time remains: G3 C15 `lanczos-recurrence`, C14 Ritz-value bounds.

**R6-E — concentration API and nets** (`NLAlib/Concentration/HansonWright.lean`, new
`Concentration/Scalar/Rademacher.lean`, `Concentration/Scalar/SubGaussian.lean`,
`Concentration/Scalar/Net.lean`, `Concentration/Matrix/Sampling.lean`; aggregators
`Concentration.lean`, `Concentration/Scalar.lean`, `Concentration/Matrix.lean`).
1. `Rademacher.lean`: the `rademacherMeasure` definition (copy from `Estimation/HutchinsonLaws.lean`,
   same name and statement; R6-D deletes the original later) with G1 C5 (1-sub-Gaussian). Build it first.
2. Generalise `hanson_wright_mgf` and `hanson_wright_of_lintegral_exp_sq_le_two` from `Fin n` to
   `[Fintype ι]` (G3 flag 1); keep the names.
3. G1 C6, C7 (sub-Gaussian moments, explicit Khintchine, maximal inequality) into `SubGaussian.lean`,
   promoting the buried `HansonWrightProof` lemmas you need to public STANDARDS names (re-export
   with `alias`, do not move the proofs).
4. G1 C4 `matrix-chernoff-sampling` with explicit constants, real corollary of `matrix_chernoff`.
5. G1 C8 deterministic net lemmas, then G1 A1 (sphere ε-net cardinality: prove if feasible, else
   scaffold) and B1 `epsilon-net-norm`, B2 sub-Gaussian spectral norm.

## Report
Per the Round 1 brief: every public declaration with status proved / scaffold / uses-scaffold and
atlas id, the exact check commands and output, and which audit items you did not reach.
