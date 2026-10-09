# Round 3: port the Prove2me Gaussian series into NLAlib

Read `docs/STANDARDS.md` and `docs/ROUND1_BRIEF.md` first (working rules: single-file checks with
`lake env lean`, no full `lake build`, no atlas edits; `sorry` only in a named scaffold).

## Source
The Prove2me workspace `/home/tyler/prove2me_workspace`: statements in
`Theorems/Thm_GaussianMatrix_<name>.lean`, proofs in `Solutions/Sol_GaussianMatrix_<name>.lean`
(each exposes `theorem solution`; it may import other `Theorems.Thm_GaussianMatrix_*`, which
are the dependencies), shared definitions in `Definitions/Def_GaussianMatrix_basic.lean`
(namespace `GaussianMatrix`). Same Mathlib pin as NLAlib, so proofs port with renames only.
Exactly one theorem has no solution: `wishart_lambda_min_cdf_density_bound`; port it as a
scaffold (`sorry`, docstring `SCAFFOLD: wishart-lambda-min-tail`) so everything above it is
proved modulo that one lemma.

## Target
Namespace `NLAlib`. Definitions come from NLAlib, never from the workspace bundle:
`gaussianMatrix` (`Gaussian/Basic.lean`, identical product measure), `frobSq`/`frobNorm`/
`specNorm` (`Matrix/Norms.lean`), `pinvL`/`pinvR` (`Matrix/Pseudoinverse.lean`),
`singularValues` (`Matrix/SVD.lean`), rotation invariance, block law/independence
(`Gaussian/Invariance.lean`), full rank a.s. and moments (`Gaussian/Moments.lean`), inverse
chi-square moment, Schur diagonal inverse, residual law, inverse-Wishart mean, pseudoinverse
Frobenius moment (`Gaussian/InverseMoments.lean`), conditioning (`Gaussian/Conditioning.lean`).
Read those files for the CURRENT names before you start (a rename pass just finished). The
workspace's `sigmaMin`, `lamMin`, `sigmaMinSq` do not exist in NLAlib yet: the Comparison agent
defines them in `NLAlib/Matrix/Spectral.lean` (see its task); everyone else imports that file
(poll for it with `lake build NLAlib.Matrix.Spectral`).

Rules for every ported declaration:
- Statement identical in content to the source (generalise only when free; never weaken);
  name per STANDARDS §1 (no `tw_`, `ou_` style prefixes: `gammaRatio_le`, `ornsteinUhlenbeck…`);
  docstring with the mathematics, the source (HMT 2011, Vershynin 2012, Davidson–Szarek 2001,
  Tropp–Webber 2023, Ledoux, …), the atlas id, and `ported from Prove2me solution
  GaussianMatrix.<name>`.
- Helpers from the solution files that are of general use become public lemmas in the right
  file; proof-local ones may stay `private`.
- One concept per file, under ~500 lines where possible (the 1000+-line solutions may stay one
  file each, split only if natural). Module docstrings per STANDARDS §2.
- Every file: `lake env lean <file>` with no errors and no warnings; build oleans with
  `lake build NLAlib.<Module>` so dependents can import (wait and retry on a lock).

## Groups (one agent each; files are owned exclusively by the group)
- **L — Gaussian concentration** (`NLAlib/Gaussian/Concentration/`): gaussian_ibp_one_dim,
  gaussian_integration_by_parts, ou_semigroup_commutation, ou_semigroup_invariant,
  ou_entropy_hasDerivAt, gaussian_logsobolev_bounded_below,
  gaussian_logsobolev_one_dim_compact_support, gaussian_logsobolev_one_dim,
  entropy_tensorization, gaussian_logsobolev, lipschitz_smooth_approx,
  gaussian_lipschitz_entropy_bound, herbst_argument, gaussian_concentration_vector,
  gaussian_concentration. Atlas ids: gaussian-integration-by-parts, ornstein-uhlenbeck,
  gaussian-log-sobolev, entropy-tensorization, herbst, gaussian-concentration.
- **C — Gaussian comparison and extreme singular values** (`NLAlib/Matrix/Spectral.lean`,
  `NLAlib/Gaussian/Comparison/`, `NLAlib/Gaussian/Extreme/Lipschitz.lean`,
  `NLAlib/Gaussian/Extreme/Gordon.lean`, `Chevet.lean`, `SpectralSecondMoment.lean`):
  sMin_lipschitz, specNorm_lipschitz, slepian_tail_comparison, sudakov_fernique, gordon_minimax,
  expectation_norm_gaussian_diff, gordon_lower, gordon_upper, gordon, chevet_expectation_bound,
  chevet, spectral_second_moment_bound, spectral_second_moment. Atlas ids: norm-lipschitz,
  slepian, sudakov-fernique, gordon-minimax, gordon, chevet, spectral-second-moment.
- **E — chi-square tails, small ball, higher moments** (`NLAlib/Gaussian/Extreme/ChiSquare.lean`,
  `SmallBall.lean`, `Deviation.lean`, `NLAlib/Gaussian/Moments/FourthMoment.lean`,
  `ApproxMultiplication.lean`, `NLAlib/Concentration/Scalar/TailIntegral.lean`):
  chi_square_lower_tail, chi_square_neg_moment, inv_chi_square_Lq_bound, inv_sq_chi_square_moment,
  integral_le_of_tail_bound, integral_power_exp_le, sMin_le_imp_dist_le,
  gaussian_dist_colspace_small_ball, dist_col_span_small_ball, sMin_small_ball,
  frobenius_fourth_moment, approx_multiplication, and LAST (they need C and L): sMin_lower_tail,
  extreme_singular_values_deviation. Atlas ids: chi-square-lower-tail, chi-square-neg-moment,
  inverse-chi-square-moment, tail-integral, smin-small-ball, gaussian-frob-fourth-moment,
  gaussian-amm, smin-lower-tail, extreme-singular-values-deviation.
- **W — inverse Wishart and pseudoinverse moments** (`NLAlib/Gaussian/InverseMoments/`):
  schur_offdiag_inv, regression_residual_indep, inverse_wishart_diag_law,
  inverse_wishart_diag_sq_moment, inverse_wishart_offdiag_sq_moment,
  inverse_wishart_rotation_relation, inverse_wishart_diag_prod_moment,
  inverse_wishart_frobenius_moment, pinv_frobenius_fourth_moment, pinv_frobenius_tail,
  specNorm_inv_gram_eq, specNorm_pinvR_sq, wishart_lambda_min_cdf_rank_one,
  wishart_lambda_min_cdf_density_bound (SCAFFOLD), wishart_lambda_min_tail,
  tw_gamma_ratio_bound, tw_inverse_moment_numeric, pinv_spectral_tail,
  pinv_spectral_expectation, inverse_wishart_spectral_moment. Atlas ids:
  inverse-wishart-mean (helpers), inverse-wishart-frob-moment, pinv-frob-fourth-moment,
  pinv-frob-tail, wishart-lambda-min-tail, pinv-spectral-tail, pinv-spectral-expectation,
  inverse-wishart-spectral-moment.

## Report
Per the Round 1 brief: every public declaration with status (`proved` / `scaffold` /
`uses-scaffold`), the atlas id it realises, the atlas ids its proof invokes, the exact check
commands and outputs, and a rename map `docs/renames/2026-10-09-port-<group>.json` mapping
`GaussianMatrix.<source name>` → `NLAlib.<new name>`.
