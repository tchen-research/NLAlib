import NLAlib.Gaussian.Concentration.Stein
import NLAlib.Gaussian.InverseMoments.CutoffDerivativeIntegrability
import NLAlib.Gaussian.InverseMoments.CutoffIntegrability
import NLAlib.Gaussian.InverseMoments.GammaBounds
import NLAlib.Gaussian.InverseMoments.GaussianWeakInequality
import NLAlib.Gaussian.InverseMoments.HardEdgeEndpoint
import NLAlib.Gaussian.InverseMoments.OperatorHardEdge
import NLAlib.Gaussian.InverseMoments.Probe
import NLAlib.Gaussian.InverseMoments.RegularizedApproximation
import NLAlib.Gaussian.InverseMoments.RegularizedIntegrability
import NLAlib.Gaussian.InverseMoments.ResolventLimit
import NLAlib.Gaussian.InverseMoments.SpectralProbe
import NLAlib.Gaussian.InverseMoments.UnshiftedWeakInequality
import NLAlib.Gaussian.InverseMoments.WeakInequality
import NLAlib.Gaussian.LogSobolevCoverage
import NLAlib.Gaussian.LogSobolevHerbst
import NLAlib.Gaussian.OrnsteinUhlenbeckEntropyGrowth
import NLAlib.Gaussian.OrnsteinUhlenbeckGrowth
import NLAlib.Gaussian.PolynomialGrowth
import NLAlib.Gaussian.PolynomialGrowthIntegrationByParts
import NLAlib.Gaussian.PositiveMoments
import NLAlib.Gaussian.ProductIntegrationByParts
import NLAlib.Gaussian.SimpleSpectrum
import NLAlib.Gaussian.SketchRank
import NLAlib.Gaussian.SlepianTails
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
import NLAlib.Gaussian.LinearImage

/-!
# Gaussian and random matrix facts

Layer 2: imports `NLAlib.Matrix` and `NLAlib.Concentration`.

Files (atlas ids): `Basic` (`gaussian-matrix-def`), `Invariance` (`rotation-invariance`,
`block-law-indep`), `LinearImage` (laws of `Gᵀ`, `G U`, `G x`: `gaussian-matrix-mulVec-law`),
`Moments` (`gaussian-frob-second-moment`, `gaussian-full-rank-ae`),
`InverseMoments` (aggregator of `InverseMoments/`: `inverse-wishart-mean`, `pinv-frob-moment`,
the inverse-Wishart second moments and the pseudoinverse tails), `Conditioning`
(`gaussian-conditioning`), `Extreme` (aggregator of `Extreme/`, including `ChiSquare`:
`chi-square-lower-tail`, `chi-square-upper-tail`, `chi-square-neg-moment`,
`inverse-chi-square-moment`).

`Moments/` (`gaussian-frob-fourth-moment`, `gaussian-amm`), `Comparison` (Slepian,
Sudakov–Fernique, Gordon's minimax comparison), `Concentration` (`gaussian-concentration`).
-/
