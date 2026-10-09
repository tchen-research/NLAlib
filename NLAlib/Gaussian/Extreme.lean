import NLAlib.Gaussian.Extreme.Lipschitz
import NLAlib.Gaussian.Extreme.LinearForms
import NLAlib.Gaussian.Extreme.Gordon
import NLAlib.Gaussian.Extreme.SpectralSecondMoment
import NLAlib.Gaussian.Extreme.Chevet
import NLAlib.Gaussian.Extreme.ChiSquare
import NLAlib.Gaussian.Extreme.SmallBall
import NLAlib.Gaussian.Extreme.Deviation

/-!
# Extreme singular values of Gaussian matrices

Aggregator for `NLAlib/Gaussian/Extreme/`: integrability of Frobenius-Lipschitz functionals
(`Lipschitz`, atlas `norm-lipschitz`), linear forms of a Gaussian matrix (`LinearForms`),
Gordon's bounds `√N − √n ≤ 𝔼 σ_min ≤ 𝔼 σ_max ≤ √N + √n` (`Gordon`, atlas `gordon`), the second
moment of a Gaussian sandwich `(𝔼‖SΓT‖²)^{1/2} ≤ ‖S‖‖T‖_F + ‖S‖_F‖T‖` (`SpectralSecondMoment`,
atlas `spectral-second-moment`), Chevet's inequality (`Chevet`, atlas `chevet`); chi-square
tails and negative moments (`ChiSquare`, atlas `chi-square-lower-tail`, `chi-square-neg-moment`),
the small-ball estimate
for `σ_min` (`SmallBall`, atlas `smin-small-ball`), and the deviation inequalities for
`σ_min` and `‖·‖₂` (`Deviation`, atlas `smin-lower-tail`,
`extreme-singular-values-deviation`).
-/
