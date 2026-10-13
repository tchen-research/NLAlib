# F2a: the measurable space on `Matrix` (first F2 PR)

Agent F2a, 2026-10-13. Brief: `docs/FOUNDATIONS_BRIEF.md` §2, first bullet and the deletion bullet.

## Added

New file `NLAlib/ForMathlib/MeasureTheory/Matrix.lean` (imports Mathlib only; layer -1), added to
the aggregator `NLAlib/ForMathlib/MeasureTheory.lean`:

| declaration | statement |
|---|---|
| `Matrix.instMeasurableSpace` | `[MeasurableSpace α] : MeasurableSpace (Matrix m n α) := MeasurableSpace.pi` (global) |
| `Matrix.instBorelSpace` | `[Fintype m] [Fintype n] [TopologicalSpace α] [MeasurableSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) := Pi.borelSpace` (global) |
| `Matrix.measurable_entry` | `Measurable fun A : Matrix m n α => A i j` |
| `Matrix.measurable_of` | `Measurable (Matrix.of : (m → n → α) → Matrix m n α)` (`fun_prop`) |
| `Matrix.measurable_iff_entries` | `Measurable f ↔ ∀ i j, Measurable fun x => f x i j` (via `measurable_pi_iff`) |
| `Matrix.ofMeasurableEquiv` | `(m → n → α) ≃ᵐ Matrix m n α`, with simp lemmas `coe_ofMeasurableEquiv`, `coe_ofMeasurableEquiv_symm` |
| `Matrix.measurable_transpose` | `Measurable (transpose : Matrix m n α → Matrix n m α)` (`fun_prop`) |
| `Matrix.measurable_conjTranspose` | same for `conjTranspose`, under `[Star α] [TopologicalSpace α] [ContinuousStar α] [BorelSpace α]` (Mathlib has no `MeasurableStar` class) (`fun_prop`) |
| `Measurable.matrix_mul` | `Measurable f → Measurable g → Measurable fun x => f x * g x` over `[NonUnitalNonAssocSemiring α] [MeasurableMul₂ α] [MeasurableAdd₂ α]` (`fun_prop`) |

`measurable_entry` is not tagged `fun_prop` (the attribute rejects it: "Not a valid `fun_prop`
theorem").

## Deleted (recorded in `docs/renames/2026-10-F2.json`)

- `NLAlib.matrixMeasurableSpace` (`borel (Matrix m n ℂ)`) and `NLAlib.matrixBorelSpace`, in
  `Probability/Concentration/Basic/MatrixStatistics.lean`; replaced by the new instances (the file
  now imports the ForMathlib module; header sentence "Borel structure on complex matrices" dropped).
- `NLAlib.orthogonalGroupMeasurableSpace` (`borel _`) and `NLAlib.orthogonalGroupBorelSpace` in
  `Matrix/Subspaces/Stiefel.lean`; the orthogonal group now gets Mathlib's
  `Subtype.instMeasurableSpace` / `Subtype.borelSpace` over the new matrix instances.

## `Matrix/Structured/Measurable.lean`

Names and signatures unchanged (all still take entrywise hypotheses, so no caller changed).
Proofs now go through the instance: `measurable_mul_entry_of` is a one-liner from
`Measurable.matrix_mul` and `measurable_iff_entries`; `measurable_inv_entry_of` composes
`det`/`adjugate` continuity with `Measurable A` instead of the array view; the two `specNorm`
lemmas (`measurable_specNorm_inv_self_mul_transpose`, `measurable_specNorm_pinvR`) use
`continuous_norm.measurable` on `Matrix` directly, which removes their two `Matrix.of.symm` uses.
Module docstring updated (it said Mathlib has no `MeasurableSpace (Matrix m n ℝ)`).

## Topology check (scratch files, not committed)

`Matrix.instBorelSpace` is stated for the topology found by instance search. Checked with
`lake env lean` on a scratch file importing the new module, `Mathlib.Analysis.CStarAlgebra.Matrix`,
`Mathlib.Analysis.Matrix.Normed`, `Mathlib.MeasureTheory.Constructions.BorelSpace.Complex`:

- Default: `(inferInstance : TopologicalSpace (Matrix m n ℂ)) = Pi.topologicalSpace` by `rfl`,
  and `= instTopologicalSpaceMatrix` by `with_reducible_and_instances rfl`; `BorelSpace` found for
  `Matrix m n ℂ` and `Matrix m n ℝ`; `BorelSpace.measurable_eq : instMeasurableSpace = borel _`.
- `open scoped Matrix.Norms.L2Operator`: the norm-induced topology
  (`PseudoMetricSpace.toUniformSpace.toTopologicalSpace`) equals `instTopologicalSpaceMatrix` by
  `with_reducible_and_instances rfl` (Mathlib's `instL2OpMetricSpace` replaces topology and
  uniformity and is `@[instance_reducible]`). `BorelSpace` is found, and
  `continuous_norm.measurable : Measurable fun A : Matrix m n ℂ => ‖A‖` (also over ℝ) and
  `(continuous_id.mul continuous_id).measurable` elaborate. **Correct and usable.** This is the
  scope of the whole concentration layer (103 files open it).
- `open scoped Matrix.Norms.Frobenius`, `Matrix.Norms.Elementwise`, and the local
  `Matrix.linftyOpNormedAddCommGroup`: the norm-induced topology equals
  `instTopologicalSpaceMatrix` by `rfl` at default transparency (so the instance is the right
  σ-algebra), but **not** at instance transparency, so `continuous_norm.measurable` fails to
  synthesize `OpensMeasurableSpace (Matrix m n ℂ)` for the norm-path topology term. (On the bare
  pi type `m → n → ℂ` it works.) The cause is Mathlib's: these normed structures are built by
  `fast_instance%` from `Pi.*`/`PiLp.*` without a `replaceTopology` to `Matrix`'s instance, and
  `instTopologicalSpaceMatrix` is an `inferInstanceAs`. No file in NLAlib needs it today: of the 19
  files opening the Frobenius scope only `Sketching/Sampling/SamplingMultiplication{,Bounds}.lean`
  mention measurability, and they build. Workaround if needed (not tested): prove
  measurability entrywise via `measurable_iff_entries`, or state continuity for
  `instTopologicalSpaceMatrix` explicitly.

## Files repaired downstream

None. `lake build NLAlib.ForMathlib.MeasureTheory.Matrix`, then
`lake build NLAlib.Matrix.Structured NLAlib.Probability NLAlib.RandomMatrix NLAlib.LowRank
NLAlib.Sketching NLAlib.Estimation` (4542 jobs) succeeded with no edits outside the four files
above: the concentration layer (`Measurable`, `iIndepFun`, `Integrable` of `Ω → Matrix d d ℂ`
under the L2 scope) and the Haar files (`RandomMatrix/Haar/*`, over the orthogonal group) build
unchanged on the new instance; no `Measurable.of_comap_le` arguments were needed.

`lake build NLAlib` (root) additionally fails in `Matrix/Spectral/{SvdPowers,SpectralBounds,
RealDilation}.lean` and `Matrix/Subspaces/ObliqueProjectionCanonical.lean`; these are caused by the
uncommitted, concurrent F1 edits to `Matrix/Spectral/SVD.lean` and `EckartYoung.lean` (e.g. missing
`NLAlib.IsSVD.mul_transpose_self`), not by F2a. `scripts/Audit.lean` / `ExtractDecls.lean` were
not run because they import the whole library. `python3 scripts/check_layers.py`: import layers OK.

## Acceptance grep

```
$ grep -rn "instance.*MeasurableSpace\|instance.*BorelSpace" NLAlib
NLAlib/ForMathlib/MeasureTheory/Matrix.lean:37:instance instMeasurableSpace [MeasurableSpace α] : MeasurableSpace (Matrix m n α) :=
NLAlib/ForMathlib/MeasureTheory/Matrix.lean:42:instance instBorelSpace [Fintype m] [Fintype n] [TopologicalSpace α] [MeasurableSpace α]
NLAlib/Sketching/Sparse/SparseLaws.lean:19:instance SparseSketch.Sign.instMeasurableSpace :
NLAlib/Sketching/Sparse/SparseLaws.lean:29:instance UniformSparseSupport.instMeasurableSpace (m s : ℕ) :
NLAlib/Sketching/Sparse/FiniteLaw/ToMeasure.lean:42:instance toMeasure_isProbabilityMeasure [MeasurableSpace α]
```

The three remaining hits are in `Sketching/Sparse/`, frozen except for F3 (brief §0): two
instances on finite non-matrix types (`SparseSketch.Sign`, `UniformSparseSupport`) and one false
positive (an `IsProbabilityMeasure` instance with a `[MeasurableSpace α]` binder). None is a matrix
instance; left for F3 / the port, or the acceptance line should be read as "no matrix instance
outside the new file".
