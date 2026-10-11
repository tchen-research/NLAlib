import NLAlib.Polynomial.AnalyticApproximation
import NLAlib.Polynomial.AnalyticCoefficients
import NLAlib.Polynomial.AnalyticFourier
import NLAlib.Polynomial.AnalyticInterpolation
import NLAlib.Polynomial.BernsteinEllipse
import NLAlib.Polynomial.ChebyshevAliasing
import NLAlib.Polynomial.CosineBasis
import NLAlib.Polynomial.EvenChebyshevFilter
import NLAlib.Polynomial.Exponential
import NLAlib.Polynomial.Jackson
import NLAlib.Polynomial.JacksonPeriodic
import NLAlib.Polynomial.JacksonPolynomial
import NLAlib.Polynomial.LanczosFilterMean
import NLAlib.Polynomial.Monomial
import NLAlib.Polynomial.SawtoothDerivative
import NLAlib.Polynomial.SawtoothInterpolation
import NLAlib.Polynomial.SawtoothNorm
import NLAlib.Polynomial.SawtoothSign
import NLAlib.Polynomial.SawtoothSquareWave
import NLAlib.Polynomial.SawtoothZeros
import NLAlib.Polynomial.SineBasis
import NLAlib.Polynomial.SquareWave
import NLAlib.Polynomial.Basic
import NLAlib.Polynomial.Chebyshev
import NLAlib.Polynomial.Minimax
import NLAlib.Polynomial.Approximation
import NLAlib.Polynomial.Markov
import NLAlib.Polynomial.Interpolation

/-!
# Polynomial approximation

Layer 0: real polynomials only, no matrices. Files (atlas ids): `Basic` (`chebyshevResidual`,
`chebyshevAmplifier`), `Chebyshev` (`chebyshev-growth`, `chebyshev-second-kind`), `Minimax`
(`chebyshev-extremal`, `chebyshev-minimax`, `chebyshev-monic-minimal`), `Approximation`
(`chebyshev-amplifier`, `inverse-polynomial-approx`), `Markov` (`markov-brothers`,
`bernstein-polynomial-inequality`), `Interpolation` (`interpolation-remainder`,
`chebyshev-interpolation-error`).
-/
