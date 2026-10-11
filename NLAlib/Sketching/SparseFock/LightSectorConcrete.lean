/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.SparseFock.LightZeroBlock

/-!
# Concrete shared-leg light operator

Compatibility import for the shared-leg proof, partitioned into operators,
labelled coordinates, cross contractions, hard-core compression, and grade bounds.
All declarations retain namespace `NLAlib.SparseFock.LightSectorConcrete`.
Source: pinned sparse-Fock commit `b9da2b5d96e5fd70252e9c6551aefc92643e7d0b`;
supports `sparse-ose`.
-/
