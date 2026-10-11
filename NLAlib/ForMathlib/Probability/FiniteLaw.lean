/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.ForMathlib.Probability.FiniteLawIndependent

/-!
# Explicit normalized finite laws

Compatibility import for finite expectations/events and independent products.
All declarations retain namespace `NLAlib.SparseFock.FiniteLaw`; the native
PMF/measure bridge is in `FiniteLawMeasure`. Source: pinned sparse-Fock commit
`b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`; supports `sparse-ose`.
-/
