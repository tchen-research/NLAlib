# Matrix foundations: Mathlib compatibility and usability audit

Date: 2026-10-13. Scope: Matrix definitions, norms, singular values, condition numbers,
Moore–Penrose inverse, subspace geometry, and selected mathematical `ForMathlib` extensions.
Read-only source review; this report is the only repository edit. Comparison is against the
checked-out Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474` in `lake-manifest.json:10`,
with Lean `v4.33.1` (`lean-toolchain:1`). This is not an exhaustive mathematical audit.

## Assessment

The central foundation is substantially compatible with Mathlib. I found no contradictory
SVD, Moore–Penrose inverse, or square condition-number definition. The strongest issues are
misleading geometric names outside their valid domains, remaining parallel interfaces, and
an F4 rule that would remove useful Mathlib-style bundled adapters. Compiled theorems with
appropriate hypotheses are not invalidated by the totalization issues below.

## Ranked findings

### 1. Unequal-width `sinThetaMax` is a directed gap, not a symmetric principal-angle API

**Priority: high for public API clarity; concrete semantic naming problem, not a false theorem.**

`Matrix/Subspaces/PrincipalAngles.lean:49` describes the sine of the largest principal angle
“between” two ranges, but the definition at line 54 is the directional residual
`specNorm (projResidual Q X)`. `PrincipalAngleDefinitions.lean:22` tells users that the largest
angle for unequal widths is reached through this function without specifying a direction
or a padding convention.

For `Q = I₂` and `X = [1,0]ᵀ`, the two values are:

- `sinThetaMax Q X = 0`;
- `sinThetaMax X Q = 1`.

Both inputs have orthonormal columns. The ordinary list of `min(dim S, dim T)` principal
angles for this nested pair contains just zero, independently of argument order. A convention
that pads by extra right angles is also legitimate, but this function changes with argument
order. The equal-width API is unaffected.

**Direction:** name or document this as the directed subspace gap, explicitly specify the
source and target ranges, and retain an equal-width principal-angle bridge. If a full
unequal-dimensional principal-angle list is wanted, give it its own symmetric indexing and
padding convention. Do not “fix” the residual formula: it is useful for range approximation.
The two displayed values were checked in Lean (validation below).

### 2. Tangent diagnostics collapse orthogonality/unboundedness to zero

**Priority: medium; documented partial-domain convention in some places, underdocumented in others.**

`PrincipalAngles.lean:64` defines `tanThetaMax` using the ordinary inverse of `QᵀX`.
Its docstring at lines 57–60 correctly limits its geometric meaning to invertible overlap
and explicitly admits a zero junk value on singular overlap. Therefore this alone is not a
mathematical bug. However, its name and unconditional nonnegativity API can make zero look
like successful alignment to users who have not established transversality.

`GraphTangent.lean:73` defines `vectorTangentToFrame` as a real quotient. Its docstring calls
this the tangent without mentioning the zero-denominator convention. Whenever `Qᵀu = 0`,
the value is zero, even for nonzero `u` orthogonal to the frame. At line 23,
`subspaceTangent` uses real `sSup`; when the defining set is unbounded above, Mathlib's
`Real.sSup_of_not_bddAbove` makes the result zero. The docstring mentions transverse graphs,
but does not state this value outside that domain. These are distinct from an extended
nonnegative tangent, which should diverge at a right angle.

Lean checked `tanThetaMax e₁ e₂ = 0` for orthonormal one-column frames in `ℝ²`, the generic
zero-overlap/zero-projection implications, and the unbounded-supremum implication.
`PrincipalAngleTangent.lean:45` already protects its norm/inverse bridge with `IsUnit (PᵀQ)`;
`GraphTangent.lean:80` uses a competitor hypothesis from which nonzero projection is proved.
I have not found a false use of those theorems.

**Direction:** keep total algebraic helpers if useful, but expose a domain-safe geometric
interface (an explicit transversality argument or an `ℝ≥0∞` variant) and add discoverable
validity/degeneracy lemmas. At minimum, bring the vector and supremum docstrings up to the
standard already met by `tanThetaMax`. Merely replacing inverse by pseudoinverse would still
hide right-angle components and would not solve the geometric problem.

### 3. F4 N3 would remove useful bundled norm interfaces

**Priority: medium, policy correction before further refactoring.**

`docs/F4_CONSISTENCY_BRIEF.md:57` demands deletion of `schattenSeminorm` and
`schattenInvariantNorm` as definitions. This conflates multiple scalar spellings with
multiple interfaces to one quantity.

`Matrix/Norms/SchattenNorms.lean:129` constructs an actual Mathlib
`Seminorm ℝ (Matrix m n ℝ)` via `Seminorm.of`; its application bridge at line 136 is `rfl`.
`SchattenInvariant.lean:89` packages that quantity with separation and unitary invariance;
its application bridge at line 99 is also `rfl`. `InvariantNorm.lean:27` sensibly extends
Mathlib's `Seminorm` with the extra invariant-norm facts. Such bundles let clients use
Mathlib seminorm composition/scaling/inequality APIs and abstract invariant-norm theorems.
Replacing them with only scalar lemmas forces each client to reconstruct the bundle.

**Direction:** retain the bundled constructors and their simp application bridges while
consolidating the scalar exponent interface. These definitions are good adapters, not
competing mathematical notions. Generalize their current real-matrix instances to `RCLike`
when the supporting inequalities are available; do not introduce a competing global norm
instance on matrices. Mathlib itself deliberately keeps multiple matrix norm structures
scoped (`Mathlib/Analysis/Matrix/Normed.lean:15`, `:23`, `:496`).

### 4. Equivalent projector and principal-angle objects still have separate public APIs

**Priority: medium, concrete composition cost.**

`Subspaces/RangeProjector.lean:31` defines generic `columnSpace`; line 37 defines the generic
Moore–Penrose range projector. Its bridge at line 124 identifies it with Mathlib's
`Submodule.starProjection`.

`Subspaces/ComplexVolumeProjection.lean:20` separately defines `complexColumnSpace` by the
same range formula, and line 25 defines `complexColumnProjector` by transporting
`starProjection` back to a matrix. These are mathematically the same objects, but their
projectors are not definitionally the same construction. A source search found no public
`complexColumnProjector = rangeProjector` bridge. Complex volume consumers consequently use
a parallel family of projector theorems.

Similarly, `PrincipalAngleDefinitions.lean:26` is real-only and reindexes to `Fin`, while
`ComplexObliqueSecant.lean:19` separately defines the complex angles directly through
`QᴴW`. Generic singular values are already available (`Spectral/SVD.lean:79`).

**Direction:** use the existing generic projector/column-space API, first adding an explicit
compatibility theorem for consumers if migration is incremental. Unify the real and complex
angle definition over `RCLike` with conjugate transpose and no unnecessary reindexing.
This recommendation is based on the actual definitions and bridges, not just F4's backlog.

### 5. The orthonormal-column predicate lacks a basic public Mathlib equivalence

**Priority: medium-low, missing interoperability lemma rather than a bad definition.**

`Basic/Orthonormal.lean:25` uses the natural equation `QᴴQ = 1`. Keeping this convenient
matrix predicate is reasonable. `Subspaces/OrthogonalProducts.lean:111` already converts it
to a Mathlib `LinearIsometry`.

However, the direct conversion from this predicate to Mathlib's `Orthonormal` family is
private (`Subspaces/Projections.lean:305`, `:308`), and a source search found no public iff
with `Orthonormal 𝕜 (fun j => WithLp.toLp 2 (Q.col j))`. This is the common boundary when
using Mathlib Gram–Schmidt or orthonormal-basis results. Clients currently unpack Gram
entries or reconstruct this correspondence.

**Direction:** publish an iff for the actual Euclidean columns and provide the corresponding
matrix/linear-isometry round-trip lemmas. Keep `HasOrthonormalCols`; do not require every
matrix theorem to expand the Gram equation or switch to a newly invented frame structure.

### 6. Scalar Schatten APIs are fragmented, while their invalid-exponent behavior is unsurprising totalization

**Priority: medium-low.**

`Norms/Schatten.lean:33` takes `p : ℝ`; `:42` introduces a second scalar definition taking
`p : ℝ≥0∞`. The latter handles infinity, but nearly parallel theorem families and differing
parameter types make usage harder. `schattenNorm A 0 = 1` for every `A`, including zero,
was checked in Lean. This follows from real `rpow`/division conventions; the docstring
correctly restricts norm results to `1 ≤ p`, so this is not a failed norm theorem.

**Direction:** one main extended-exponent scalar interface, a clearly named finite power-sum
helper if positive exponents below one are needed, and bundled norm constructors requiring
`1 ≤ p`. Preserve the useful bundles in finding 3. General complex matrices should not lose
those constructors merely because the current proofs are real-only.

### 7. Coordinate-subspace and Hilbert-subspace entry points require manual transport

**Priority: low-medium for extension work.**

`orthonormalBasisMatrix` takes `Submodule 𝕜 (m → 𝕜)`
(`Subspaces/OrthonormalBasisMatrix.lean:43`), whereas `columnSpace` produces
`Submodule 𝕜 (EuclideanSpace 𝕜 m)` (`RangeProjector.lean:31`). The basis implementation
already transports through `WithLp.linearEquiv`, but that transport and its dimension lemma
are private (`OrthonormalBasisMatrix.lean:24`, `:29`). Thus the natural composition
“take an orthonormal basis of this columnSpace” does not type-check directly.

**Direction:** expose a Hilbert-subspace basis-matrix entry point or named public transport
bridges, retaining the algebraic coordinate version where it is convenient. This is ordinary
Mathlib `WithLp` transport; no new custom vector type is needed.

## Foundations worth retaining

- `specNorm` is Mathlib's L2 operator norm with an `rfl` bridge
  (`Norms/Core.lean:53`, `:57`). `frobNorm` has an explicit bridge to Mathlib's scoped
  Frobenius norm (`Norms/Frobenius.lean:486`). Named norms avoid ambiguity when scopes change;
  this is useful, not accidental duplication of norm semantics.
- `singularValues` delegates to `Matrix.toEuclideanLin A` and Mathlib's
  `LinearMap.singularValues` (`Spectral/SVD.lean:79`, `:83`). The zero-based, zero-padded
  convention is already Mathlib's convention
  (`Mathlib/Analysis/InnerProductSpace/SingularValues.lean:91`). NLAlib forgets the upstream
  `Finsupp` packaging and returns a function; exposing a support/Finsupp bridge would be a
  convenience, not a prerequisite for correctness. `IsSVD` at `SVD.lean:334` is a reasonable
  matrix-factorization certificate. No competing Mathlib matrix SVD predicate was found.
- `moorePenroseInverse` is defined by existence plus uniqueness of the four Penrose identities
  (`Basic/MoorePenrose.lean:107`, `:116`), over generic finite rectangular shapes. The pinned
  Mathlib matrix inverse explicitly does not handle pseudoinverses
  (`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:22`). This is genuine added theory.
  `pinvL`/`pinvR` remain separate full-rank formula helpers (`Basic/Pseudoinverse.lean:44`, `:50`)
  with documented zero junk outside their rank domain; make the general function the primary
  user entry point rather than advertising these helpers as unrestricted pseudoinverses.
- Square `conditionNumber` now has the conventional singular value `⊤`
  (`Perturbation/ConditionNumber.lean:39`, `:55`), while the finite pseudoinverse quantity has
  a distinct name (`:161`) and an invertibility-guarded bridge (`:166`). This resolves the
  earlier conceptual collision. `.toReal` lemmas explicitly require invertibility.
- `IsDiagonalizable` has bridges to Mathlib eigenspaces and, with the correct algebraic-closure
  hypothesis, semisimplicity (`Spectral/Diagonalizable.lean:109`, `:177`). It should not be
  blindly replaced by `IsSemisimple` over arbitrary fields.
- `ForMathlib/MeasureTheory/Matrix.lean:37` and `:42` install the actual product measurable
  and Borel structures. No equivalent Matrix measurable-space instance was found in the
  pinned Mathlib source search. This is a defensible upstream candidate, not an incompatible
  replacement. Likewise the sampled Gram–Schmidt transport and matrix quadratic-form CLM
  helpers build on Mathlib objects. I did not establish a serious Mathlib theorem duplication
  in those sampled files; this does not certify every `ForMathlib` file.

## Other documented totalizations

`ForMathlib/Analysis/Calculus/Conditioning.lean:25` gives zero at nondifferentiable points
because Mathlib's `fderiv` does; its relative quantity at line 29 gives zero when the output
vanishes. Both are documented. `Functions/ExpLog.lean:35` is the self-adjoint real CFC log,
not a general complex principal matrix logarithm. Its bridge to `CFC.log` is explicit at
line 40. These are acceptable theorem-level helpers with their intended hypotheses, but
entry-point documentation should distinguish them from unrestricted numerical diagnostics.
In particular, the log docstring's “non-positive spectrum” description is imprecise: applying
`Real.log` through a Hermitian spectral calculus retains Real.log's negative-input convention;
only failure of the CFC's self-adjoint domain forces the CFC junk value. None of this warrants
inventing an alternative calculus implementation.

## Validation and limits

Scratch checks used only `/tmp/MatrixAuditChecks.lean`, under
`flock /tmp/nlalib-f4-build.lock lake env lean /tmp/MatrixAuditChecks.lean`.
The final successful check is `/tmp/matrix-audit-checks6.log`; it proves the orthogonal-frame
tangent counterexample, both directed-gap values, invalid-exponent Schatten value, the
unbounded-supremum tangent implication, and the singular square condition-number behavior.
Earlier scratch attempts failed on matrix literal/type elaboration; no source proofs were
changed or admitted. No full build was run for this audit. The checked files are snapshots
of the current working tree, not claims about all uninspected downstream uses.
