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
scripts/                    trust audits, declaration lint, import/layer/name/atlas checks, site builders
```

A module may import only its own layer and lower; `scripts/check_layers.py` enforces it.
Definitions and foundational theorems live together in each topic's API.

## Using the library

Use the same Lean toolchain and Mathlib revision as this package. For a local checkout, add a
path dependency to your project's `lakefile.lean` (adjust the path):

```lean
require NLAlib from "../NLAlib"
```

Then start with the checked default import:

```lean
import NLAlib

open NLAlib

example {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    specNorm (A * B) ≤ specNorm A * specNorm B :=
  specNorm_mul_le A B
```

`import NLAlib` excludes modules with unfinished proofs and their import dependants. CI checks
the transitive axioms of every reachable library declaration, including definitions and private
helpers, and rejects `sorryAx`. The complete development is available through
`import NLAlib.Experimental`; its unfinished declarations and their descendants are marked by
`sorry: true` in [the declaration index](atlas/declarations.json).

For smaller imports, use individual topic modules. Check
[the import inventory](atlas/import_surface.json): it lists the modules in the default surface
and explains which experimental roots exclude the others. Topic aggregators import their entire
topic and can include experimental work. Exclusion is conservative at module level: an
independent proved theorem can share a file with an unfinished one.

[Downstream examples](Examples/Downstream.lean) illustrate generic and complex matrices and
subspace embeddings; [probability examples](Examples/Probability.lean) show Gaussian laws on an
arbitrary probability space. Public probability bounds should be applied through their
law/integral statements; weighted sums and recurrences provide computational identities. Algorithm
specifications and compression theorems are distinct from correctness or cost guarantees for a
particular recurrence.

## Building

```
lake exe cache get   # Mathlib oleans
lake build NLAlib NLAlib.Experimental
python3 scripts/import_surface.py --check
lake env lean scripts/AuditTrusted.lean   # default import: no sorry or nonstandard axioms
lake env lean scripts/Lint.lean           # standard declaration and instance linters
lake env lean scripts/Audit.lean          # complete development: experimental sorry inventory
lake env lean Examples/Downstream.lean
lake env lean Examples/Probability.lean
python3 scripts/check_layers.py
python3 scripts/check_names.py
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
