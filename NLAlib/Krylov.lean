import NLAlib.Krylov.Basic
import NLAlib.Krylov.Polynomial
import NLAlib.Krylov.SpectralMeasure
import NLAlib.Krylov.CG
import NLAlib.Krylov.GaussQuadrature
import NLAlib.Krylov.Lanczos
import NLAlib.Krylov.Ritz

/-!
# Krylov and polynomial methods

Layer 1: deterministic, imports `NLAlib.Matrix`, `NLAlib.Polynomial` and `NLAlib.ForMathlib`
only; randomized Krylov guarantees live with their consumers in `LowRank` and `Estimation`.
Files (atlas ids): `Basic` (`krylovSpace`), `Polynomial` (`krylov-subspace`), `SpectralMeasure`
(`spectral-measure`), `CG` (`cg-convergence`), `GaussQuadrature` (`lanczos-gauss-quadrature`),
`Lanczos` (`lanczos-recurrence`), `Ritz` (`ritz-value-bounds`).
-/
