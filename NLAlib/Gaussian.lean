import NLAlib.Gaussian.Basic
import NLAlib.Gaussian.Moments
import NLAlib.Gaussian.InverseMoments
import NLAlib.Gaussian.Conditioning
import NLAlib.Gaussian.Concentration
import NLAlib.Gaussian.Moments.ApproxMultiplication
import NLAlib.Gaussian.Moments.FourthMoment
import NLAlib.Gaussian.Comparison
import NLAlib.Gaussian.Extreme
import NLAlib.Gaussian.Invariance

/-!
# Gaussian and random matrix facts

Layer 2: imports `NLAlib.Matrix` and `NLAlib.Concentration`.

Files (atlas ids): `Basic` (`gaussian-matrix-def`), `Invariance` (`rotation-invariance`,
`block-law-indep`), `Moments` (`gaussian-frob-second-moment`, `gaussian-full-rank-ae`),
`InverseMoments` (aggregator of `InverseMoments/`: `inverse-wishart-mean`, `pinv-frob-moment`,
the inverse-Wishart second moments and the pseudoinverse tails), `Conditioning`
(`gaussian-conditioning`), `Extreme` (aggregator of `Extreme/`, including `ChiSquare`:
`chi-square-lower-tail`, `chi-square-neg-moment`, `inverse-chi-square-moment`).

`Moments/` (`gaussian-frob-fourth-moment`, `gaussian-amm`), `Comparison` (Slepian,
Sudakov–Fernique, Gordon's minimax comparison), `Concentration` (`gaussian-concentration`).
-/
