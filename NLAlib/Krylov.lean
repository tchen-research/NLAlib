import NLAlib.Krylov.Basic
import NLAlib.Krylov.Polynomial

/-!
# Krylov and polynomial methods

Layer 1: deterministic, imports `NLAlib.Matrix` and `NLAlib.Polynomial` only; randomized Krylov
guarantees live with their consumers in `LowRank` and `Estimation`. Files (atlas ids): `Basic` (`krylovSpace`),
`Polynomial` (`krylov-subspace`). Planned: `lanczos-recurrence`, `lanczos-gauss-quadrature`.
-/
