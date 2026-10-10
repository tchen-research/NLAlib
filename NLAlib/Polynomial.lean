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
