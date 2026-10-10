import NLAlib.Krylov.Basic
import NLAlib.Krylov.Polynomial
import NLAlib.Krylov.Grade
import NLAlib.Krylov.Minimiser
import NLAlib.Krylov.SpectralMeasure
import NLAlib.Krylov.CG
import NLAlib.Krylov.PolynomialMethods
import NLAlib.Krylov.GaussQuadrature
import NLAlib.Krylov.Arnoldi
import NLAlib.Krylov.ArnoldiProcess
import NLAlib.Krylov.Lanczos
import NLAlib.Krylov.Jacobi
import NLAlib.Krylov.JacobiFraction
import NLAlib.Krylov.FunctionApprox
import NLAlib.Krylov.GMRES
import NLAlib.Krylov.Ritz
import NLAlib.Krylov.Block
import NLAlib.Krylov.Preconditioned

/-!
# Krylov and polynomial methods

Layer 1: deterministic, imports `NLAlib.Matrix`, `NLAlib.Polynomial` and `NLAlib.ForMathlib`
only; randomized Krylov guarantees live with their consumers in `LowRank` and `Estimation`.
Conventions: `docs/KRYLOV_DEFINITIONS.md` (methods are predicates or compressions; approximant
theorems take any orthonormal `Q ⊇ K_q`, structure theorems take a `LanczosDecomp`).

Files (atlas ids): `Basic` (`krylovSpace`), `Polynomial` (`krylov-subspace`), `Grade`
(`krylov-grade`), `Minimiser` (`affine-krylov-minimiser`, `residual-polynomial`), `SpectralMeasure`
(`spectral-measure`), `CG` (`cg-convergence`, `cg-finite-termination`), `PolynomialMethods`
(`polynomial-method-def`, `richardson-iteration`, `chebyshev-iteration`), `GaussQuadrature`
(`lanczos-gauss-quadrature`), `Arnoldi` (`graded-krylov-basis-def`, `arnoldi-def`),
`ArnoldiProcess` (the canonical witness), `Lanczos` (`arnoldi-relation`, `lanczos-recurrence`),
`Jacobi` (`lanczos-orthogonal-polynomials`, `jacobi-matrix-identities`), `JacobiFraction`
(continued fraction), `FunctionApprox` (`krylov-polynomial-exactness`, `lanczos-fa-error`,
`lanczos-fa-interpolation`), `GMRES` (`gmres-def`, `minres-bound`), `Ritz` (`ritz-value-bounds`,
`krylov-eigenvector-angle`, `kaniel-paige-saad`), `Block` (`block-krylov-subspace`,
`subspace-iteration-def`), `Preconditioned` (`preconditioned-cg`, `cgls-lsqr-bound`).
-/
