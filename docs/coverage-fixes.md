# Completed Gaussian proofs and catalogue coverage fixes

This change completes the four Prove2Me Gaussian inverse results and integrates
the independently checked coverage proofs into the normal `NLAlib` module tree.
Import `NLAlib`, or the individual topic module. The exact public signatures are
in the generated [`atlas/declarations.json`](../atlas/declarations.json).

## Four Gaussian inverse results

The existing theorem statements retain their hypotheses and constants.
The moment theorems prove integrability as well as their expectation bounds.
The Gaussian full-row-rank theorem justifies the full-rank inverse formulas
almost surely, including the square-matrix case of the tail bound.

| Prove2Me target | Canonical declaration |
| --- | --- |
| [Inverse-Wishart spectral moment](https://prove2.me/theorems/b8bbfa46-4e40-44b1-acd8-87ddb9ac6bb3) | `integrable_and_integral_specNorm_inv_self_mul_transpose_pow_gaussianMatrix_le` |
| [Expected Gaussian pseudoinverse norm](https://prove2.me/theorems/d4d3ca6e-eb6f-496c-b9cd-975119336270) | `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le` |
| [Gaussian pseudoinverse spectral tail](https://prove2.me/theorems/c927004d-b093-4f9b-8a2c-b6cc07ccb941) | `gaussianMatrix_lt_specNorm_pinvR_le` |
| [Integrated Edelman bound](https://prove2.me/theorems/86a4ed0c-832c-4bb5-a8d7-efc12b3a4f57) | `gaussianMatrix_sigmaMin_transpose_sq_le_le_lintegral` |

All names above are in namespace `NLAlib`. The integrated CDF bound is in
[`LambdaMinTail`](../NLAlib/Gaussian/InverseMoments/LambdaMinTail.lean);
the other three are in
[`SpectralTail`](../NLAlib/Gaussian/InverseMoments/SpectralTail.lean).

The tail proof uses finite unshifted operator calculus, a scalar weak-density
argument, and a Mellin endpoint. The moment and expectation proofs use Gaussian
quadratic probes and Schur residual laws. The separate results in
[`SpectralProbe`](../NLAlib/Gaussian/InverseMoments/SpectralProbe.lean) improve the
inverse-moment numerator to `k+r−1`, permit positive real powers up to half the
oversampling gap, remove the original `p≤18` restriction in that stronger result,
and give the sharper expected pseudoinverse bound
`e/(k−r) * sqrt((k+r−1)/2)`. The original statements remain available unchanged.

## Coverage fixes

| Original gap | Completed coverage |
| --- | --- |
| Missing Gram converse and singular-value OSE form | Both Gram directions and the singular-value equivalence, including empty dimensions |
| Full-rank formulas advertised as a general pseudoinverse | General real Moore–Penrose inverse, uniqueness, four identities, projectors and norm formulas at every rank |
| Missing rank factor and operator-norm perturbation bound | Rank-based Frobenius comparison, norm invariance and the stronger minimum-singular-value perturbation bound |
| Hutchinson moment assumptions instead of distributional corollaries | Actual Gaussian and Rademacher laws discharge the moment and integrability premises |
| Generic Hutchinson entry advertised isotropy but its theorem required independence | Coordinate second-moment identity alone now derives integrability and unbiasedness |
| MGF certificates substituted for Orlicz hypotheses | Genuine exponential-moment bridges and complete Bernstein/Hanson–Wright tails with explicit constants |
| Slepian tail convention and omitted variance condition | Nonstrict comparison with equal coordinate variances; degenerate Gaussian laws included |
| Entropy tensorization restricted to positive functions | Nonnegative functions, including zeros, with conditional integrability derived |
| Gaussian LSI assumed finite entropy | Finite square and gradient energy imply finite entropy; exact LSI constant 2 |
| Herbst assumed an entropy or exponential-moment certificate | A genuine Dirichlet-form LSI implies concentration for every Lipschitz observable, with moments derived |
| Gaussian integration by parts restricted derivatives | Polynomial-growth scalar/product identities and the integrable differential-operator domain |
| OU assumed section integrability | Commutation and full entropy dissipation on the positive C1 polynomial-growth domain |
| Low-rank bounds used an unidentified tail or supplied Gaussian facts | Actual best-rank Frobenius optimum, proved minimizers, constructed Gaussian range frames, and the raw generalized Nyström formula at every rank |
| Ordinary and early projected-truncation claims were combined | Ordinary truncation has a separate proved variant, with the stronger one-residual error bound |
| Kaczmarz used a supplied singular lower bound and weighted recurrence | The actual pseudoinverse condition number and probability expectation of iid row paths |

The catalogue also makes the positive-width condition for Gaussian AMM explicit
and uses adjoints in the complex Hermitian-dilation and matrix-series formulas.
The Slepian and Kaczmarz catalogue statements now include the required equal-variance
and full-column-rank hypotheses.

## Precise scope

Frobenius Eckart–Young is proved with an attained infimum over all rank-at-most-`k`
matrices. The broader entry's spectral-norm component remains open and is not
marked proved by this result. Deterministic endpoints accept arbitrary finite
index types. The parent's singular-value list uses explicit `Fin(card)` normalization.

OU entropy dissipation is proved for C1 functions bounded below by a positive
constant, with polynomial growth of their values and derivatives, at positive
times. Smoothness and an unspecified lower bound alone do not ensure finite
Gaussian moments or entropy. These conditions are recorded in the atlas.

The standard constructed-frame RSVD output has rank at most `k` and integrable
squared error bounded by `(1+k/(t−k−1)) OPT²`. The raw generalized Nyström output
is `AΩ(ΨᵀAΩ)†ΨᵀA`, with the exact factor
`(1+q/(s−q−1))(1+k/(t−k−1))`, where `q=min(rank A,t)`.
It assumes the actual independent Gaussian laws, `t≥k+2` and `s≥q+2`;
frame, rank, moment, completion and best-approximation certificates are derived.

`etrsvd`, `etgn` and the early-truncation-specific identity await the CP25/LRA
source. Their unverified historical external references remain available with
candidate/stated status. The conditional tGN entry is marked assumed. These
labels distinguish unavailable or conditional references from the checked local
statements. Truncated-Nyström and RSVD spectral-tail algorithm extensions are outside
this change. Existing JL scaffolds remain catalogued and do not occur in the new proofs.

## Provenance and verification

Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` are unchanged.
The Hanson–Wright port preserves Apache-2.0 notices from HighDimProb commit
`c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae`; that repository is a proof source,
and this package continues to depend on Mathlib only.

Run:

```text
lake build
lake env lean scripts/Audit.lean
lake env lean -DautoImplicit=false scripts/AuditGaussianInverse.lean
lake env lean -DautoImplicit=false scripts/AuditNewProofs.lean
lake env lean scripts/ExtractDecls.lean
python3 scripts/check_layers.py
python3 scripts/check_names.py
python3 scripts/check_atlas.py
```

The additional audits cover the original four statements, sharper corollaries,
the unshifted tail dependencies, and public/private theorem helpers in the new
and completed modules. Their permitted axioms are `propext`, `Classical.choice`
and `Quot.sound`. No new scaffolds or nonstandard axioms are introduced.
