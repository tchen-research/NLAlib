import NLAlib.Gaussian.Basic
import NLAlib.Gaussian.Moments
import NLAlib.Gaussian.InverseMoments
import NLAlib.Gaussian.Conditioning
import NLAlib.Gaussian.Invariance

/-!
# Gaussian and random matrix facts

Layer 2: imports `NLAlib.Matrix` and `NLAlib.Concentration`.

Files (atlas ids): `Basic` (`gaussian-matrix-def`), `Invariance` (`rotation-invariance`,
`block-law-indep`), `Moments` (`gaussian-frob-second-moment`, `gaussian-full-rank-ae`),
`InverseMoments` (`inverse-chi-square-moment`, `inverse-wishart-mean`, `pinv-frob-moment`),
`Conditioning` (`gaussian-conditioning`).

Planned: `Moments` (`gaussian-frob-fourth-moment`, `gaussian-amm`), `Extreme` (`gordon`,
`smin-lower-tail`, `smin-small-ball`), `Concentration` (`gaussian-concentration`).
-/
