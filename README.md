# NLAlib: randomized numerical linear algebra in Lean 4

A Lean 4 / Mathlib library of the **foundations of randomized numerical linear algebra**: the
matrix analysis, Gaussian and random-matrix facts, concentration inequalities, sketching
primitives and structural low-rank lemmas that randomized algorithms are analysed with. The aim is
reusable statements that other people's proofs can cite, not one-off verifications of particular
algorithms.

Progress map: **https://research.chen.pw/NLAlib/** (built from `atlas/atlas.json` on every merge).

## Layout

```
NLAlib/
  ForMathlib/     general facts headed upstream                                        (layer −1)
  Matrix/         norms, projections, pseudoinverse, SVD, spectral, measurability      (layer 0)
  Polynomial/     Chebyshev growth and minimax, Markov, interpolation                  (layer 0)
  Probability/    Gaussian/ (scalar and vector facts), Concentration/ (Scalar, Matrix = Tropp
                  2015 Ch. 3–8, QuadraticForms, Entropy, Martingales), SubGaussian/, Rademacher/,
                  ChiSquare/, Sampling/                                                (layer 1)
  RandomMatrix/   Gaussian/ (Basic, Invariance, Moments, Spectral, Wishart, InverseMoments),
                  SubGaussian/, Haar/                                                     (layer 2)
  Sketching/      subspace embeddings, JL                                              (layer 3)
  LowRank/ Estimation/   range finder, RSVD, generalized Nyström; Hutchinson, randomized
                         Krylov estimators                                              (layer 4)
  Solvers/        randomized Kaczmarz                                                   (layer 5)
atlas/                      the catalogue of results, sources, libraries and dependencies
scripts/                    Audit.lean (axioms), check_layers.py, check_atlas.py, build_site.py
```

A module may import only its own layer and lower; `scripts/check_layers.py` enforces it. Each
area's `Basic.lean` holds definitions only and is the area's public interface.

## Building

```
lake exe cache get   # Mathlib oleans
lake build
lake env lean scripts/Audit.lean   # every theorem uses only propext, Classical.choice, Quot.sound
python3 scripts/check_layers.py
python3 scripts/check_atlas.py
```

Pinned: Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (`lake-manifest.json`).

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for conventions and the pull-request process, and
[atlas/TARGETING.md](atlas/TARGETING.md) for how targets are chosen. Agents driving the build
should read [AGENTS.md](AGENTS.md).

## License

Apache License 2.0, see [LICENSE](LICENSE).

## Completed proof coverage

The [coverage guide](docs/coverage-fixes.md) records the completed Gaussian inverse
proofs, Gram converse, general Moore–Penrose inverse, distributional concentration
and estimator results, and actual-optimum low-rank bounds. It includes the precise
domains, source provenance, catalogue corrections and verification commands.
