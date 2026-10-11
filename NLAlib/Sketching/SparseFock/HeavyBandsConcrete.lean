/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.HeavyNormalizedBands

/-!
# Concrete heavy-heavy band estimates

This compatibility import exposes the marked-site transitions, occupation
energies, row factorizations, and all three normalized heavy-band estimates.
Every existing declaration remains in `NLAlib.SparseFock.HeavyBandsConcrete`.
Ported from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/
