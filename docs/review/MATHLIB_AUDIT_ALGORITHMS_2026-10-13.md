# Algorithm and approximation API audit — 2026-10-13

Scope: `Krylov/**`, `Polynomial/**`, `Estimation/**`. Read-only Lean review after compilation recovery. This assesses whether another author can safely build on the mathematics, not merely whether the tree compiles. No Lean definitions, theorem statements, or atlas statuses were changed.

Inspected the actual implementation, the regenerated declaration index, and pinned Mathlib sources. The pin is `0df444a360eaa60ab8c11dca51a86af692955474`, Lean `v4.33.1`. A scratch Lean check ran successfully under `/tmp/nlalib-f4-build.lock`: `/tmp/f4_algorithms_audit.lean`, output `/tmp/f4_algorithms_audit.log`. No full build was run for this audit.

## Assessment

The underlying choice of Mathlib objects is mostly sound: ordinary matrices, submodules, `Polynomial`, `aeval`, `cfc`, measures, and Euclidean `WithLp` spaces. The custom algorithm definitions generally encode recognizable mathematical objects rather than certificates invented to make a desired theorem trivial. Keep that foundation.

There is, however, a concrete mismatch between the advertised largest Ritz value and its actual definition. There is also a material gap between proved variational/compression results and proved correctness of short recurrences or an actual bounded-cost stochastic algorithm. These should be resolved or clearly separated before advertising this as a trusted starting point for others.

## Findings, in priority order

### 1. High: the public largest Ritz value is clipped at zero

Location: `NLAlib/Krylov/Spectral/MeasurableRitz.lean:43–49`, and the unconditional nonnegativity theorem at line 89. The module introduction also identifies the value with the largest eigenvalue of the compression without a positivity restriction.

`lanczosRitzValue` takes the supremum of Rayleigh quotients over **all** vectors in the Krylov space. The zero vector contributes the totalized quotient `0/0 = 0`. For a nontrivial space and a negative-definite matrix, the result is zero rather than the largest Ritz value. More generally, it clips a negative largest Ritz value to zero.

Reproduced with `A = [-1]`, `b = [1]`, `q = 1`. This Krylov space is the entire one-dimensional space; the unique compression eigenvalue and every nonzero-vector Rayleigh quotient are `-1`. The scratch Lean file proves:

```lean
import NLAlib.Krylov.Spectral.MeasurableRitz
open scoped Matrix
open NLAlib

example : lanczosRitzValue (-(1 : Matrix (Fin 1) (Fin 1) ℝ))
    (fun _ => 1) 1 = 0 := by
  apply le_antisymm ?_ (lanczosRitzValue_nonneg _ _ _)
  apply csSup_le
  · exact ⟨_, 0, (krylovSpace _ _ _).zero_mem, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [rayleighQuotient_eq_div]
    simp only [Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (dotProduct_self_nonneg _))
      (dotProduct_self_nonneg _)
```

To reproduce, save this code block to `/tmp/ritz_counterexample.lean` and, from the `lean/`
directory, run `flock /tmp/nlalib-f4-build.lock lake env lean /tmp/ritz_counterexample.lean`.
The identical proof was compiled successfully as part of the scratch check noted above.

Mathlib already demonstrates the appropriate domain convention: `ContinuousLinearMap.image_rayleigh_eq_image_rayleigh_sphere` and `iSup_rayleigh_eq_iSup_rayleigh_sphere`, in `Mathlib/Analysis/InnerProductSpace/Rayleigh.lean:84–103`, use nonzero vectors or a positive-radius sphere. The problem is not Mathlib's totalization of the quotient; it is including its zero-vector value in this optimization domain.

Direction: define the general Ritz value on nonzero Krylov vectors, or the unit sphere in that subspace, with an explicit convention for the trivial space. Prove equality with the largest eigenvalue of an orthonormal compression under the natural Hermitian/nontrivial-space hypotheses. Recover the current PSD use as a theorem. If this definition is intentionally PSD-only, give it an explicitly restricted name/contract rather than a general largest-Ritz-value claim.

Impact is bounded: `RandomStartLanczos.lean:308` and `:416` assume PSD matrices, so this example does **not** refute their expectation bounds. It does block reuse for shifted or indefinite Hermitian problems. The rational-supremum measurability proof will need a genuine domain adjustment, not simply deletion of the nonnegativity lemma.

### 2. High: ordinary algorithm interfaces expose unproved recurrence correctness

Locations of the eight direct `sorry` proofs in this scope:

| Source | Missing proof |
|---|---|
| `Krylov/Solvers/CGRecurrence.lean:210`, `:221` | Residual orthogonality and conjugate search directions |
| `Krylov/Processes/LanczosRecurrence.lean:206` | Three-term recurrence equals the canonical Arnoldi basis |
| `Krylov/Processes/Bidiagonalization.lean:250`, `:266`, `:283` | Golub–Kahan realization, breakdown characterization, coefficient identification |
| `Krylov/Spectral/QRAlgorithm.lean:241` | Leading-column simultaneous-iteration interpretation |
| `Krylov/Spectral/PowerMethod.lean:437` | Scalar tangent/principal-angle bridge |

The fresh index marks **25 of 774 public declarations in these three areas** as depending on `sorryAx`; all 25 are in Krylov. This includes derived theorems with ordinary proof bodies and confident docstrings, for example `isCGIterate_cgRecurrence` (`CGRecurrence.lean:343`), finite termination, and the Lanczos realization/positivity chain. Some QR propagation also comes from imported dependencies, so eight local holes are not a complete dependency-root inventory.

The scratch check confirms:

```text
NLAlib.isCGIterate_cgRecurrence:
  [propext, sorryAx, Classical.choice, Quot.sound]
NLAlib.existsUnique_isCGIterate:
  [propext, Classical.choice, Quot.sound]
```

This is a meaningful distinction. The CG optimality predicate and its existence/uniqueness theorem are genuine proved mathematics. The assertion that the implemented recurrence produces that iterate is still unproved. A supplied `IsCGIterate` hypothesis is therefore useful, but a reader cannot treat the recurrence bridge as a certified implementation.

The aggregate files `Krylov/Solvers.lean:2`, `Krylov/Processes.lean:3,5`, and `Krylov/Spectral.lean:3–4` expose these declarations through normal imports. Importing a scaffold does not make every independent theorem scaffold-dependent; the risk is using its theorem unknowingly.

Direction: finish the recurrence invariant proofs, or establish a clearly named experimental/scaffold import boundary while keeping the proved variational API available. Gate the intended trusted library import set against `sorryAx`, including transitive dependencies. Ensure generated documentation shows the trust status beside derived theorems, not only beside the source `sorry`.

### 3. Medium: SLQ “step counts” constrain a supplied space, not the cost of a constructed algorithm

Locations: `Estimation/Quadrature/SLQ.lean:43`, `:60–66`, `:107–113`; `SLQAnalyticSteps.lean:26–35`; `SLQLipschitz.lean:55–61`.

The estimator accepts arbitrary matrices `Q k : Matrix n r ℝ`. Its theorems assume orthonormal columns and containment of `K_q(A,g_k)` in the supplied range. There is no relation between `card r` and `q`, and the supplied `Q` need not have been computed from the probes by Lanczos. In particular, a full ambient orthonormal basis satisfies the containment hypothesis for every `q`, although applying `cfc` to the resulting full compression is not a `q`-step algorithm.

These are substantive, valid compression error theorems. They are not vacuous and do not assume their error conclusion. Their “logarithmic step count” interpretation requires an additional realization and size argument.

There is also a concrete breakdown obstacle to the obvious instantiation: the standard `arnoldiMatrix A b q` has zero columns beyond the grade, so it cannot satisfy fixed-size `HasOrthonormalCols` for arbitrary probes/matrices. For `A=I` and nonzero `b`, the grade is one; using two or more unmodified Arnoldi columns fails. The current probability theorems ask for these certificates for every sample, not merely almost surely.

Direction: retain the generic compression theorem, then add a separate actual-estimator interface with grade-aware dimensions or a specified completion/stopping rule. Prove its containment, orthonormality, and dimension/matvec bounds. Identify the resulting estimator with the compressed formula; handle zero starts and early exact termination explicitly. A measurable constructor or suitable almost-everywhere formulation would also make downstream probabilistic use easier. Absence of a measurability hypothesis on arbitrary `Q` alone is not a contradiction: the current measure bounds can use outer-measure monotonicity.

### 4. Medium: Hutch++ and XTrace are useful kernels, but callers still supply the algorithm and analytic obligations

Locations: `Estimation/Trace/Unbiased.lean:103`, `:164–170`, `:182`, `:196–205`.

`hutchPlusPlusEstimate` accepts any deflation basis. The random unbiasedness result takes a supplied basis function, independence, isotropic moments and product-law integrability. XTrace similarly takes arbitrary leave-one-out statistics, a basis function, independence and integrability. No assertion in these theorem signatures enforces that the basis spans the sketch image used by the named algorithm.

This is appropriate as a general unbiasedness lemma: the identity genuinely holds for any independent orthonormal deflation basis. It should not be confused with a complete implementation or a proved sample-complexity theorem for the published algorithms. The docstrings already disclose much of this limitation.

Direction: keep the generic kernels, add concrete constructors and corollaries for the intended Gaussian/Rademacher sketches, and discharge independence and integrability for those constructors. Avoid adding another custom “algorithm certificate” that merely repeats the current hypotheses without constructing a witness.

### 5. Medium: field-generic spaces have real-only elementary APIs

Locations: `Krylov/Spaces/Basic.lean:27`, `Krylov/Spaces/Polynomial.lean:33,48`; analogous block-space usage in `LowRank/PolynomialMethods/ComplexPolynomialFilter.lean`.

The Krylov-space definition is field-generic, but even generator membership and the polynomial characterization are specialized to real matrices. These statements use algebraic span and polynomial evaluation, not order or real analysis. A downstream complex user cannot apply the obvious API and must repeat a proof from the generators. The preceding compile-recovery work actually needed such a direct proof in the complex polynomial-filter consumer.

Direction: generalize these algebraic lemmas at their current names to an appropriate field/algebra setting, preserving specialization by type inference. Then generalize inner-product results where mathematically natural using Mathlib's `RCLike`/Hermitian interfaces. Do not create a second family of `Complex...` copies or demand complex generality from intrinsically real probability results.

### 6. Low: the real Chebyshev coefficient entry point requires a complex function

Locations: `Polynomial/FunctionApproximation/AnalyticCoefficients.lean:21,28`; `AnalyticApproximation.lean:92`.

The contour-based coefficients are explicit and their decay/reconstruction is proved; this is not an assumed-approximation certificate. But the “real” coefficient API accepts `F : ℂ → ℂ` and takes real parts. A user starting with an integrable real function on `[-1,1]` has no direct coefficient API or checked bridge to the customary cosine/weighted-integral normalization.

Pinned Mathlib already supplies `Polynomial.Chebyshev.measureT`, `integrable_measureT`, `integral_measureT_eq_integral_cos`, and the Chebyshev orthogonality constants (`Orthogonality.lean:49,67,78,117–143`).

Direction: add the real weighted-integral/cosine-integral coefficient and prove its equality with the contour coefficient when an extension agrees on the interval. Keep the contour form for analytic decay proofs. This is an interoperability improvement, not evidence that the existing analytic approximation bounds are wrong.

## Totalization and edge cases that are not themselves bugs

- `hutchinsonEstimate` divides by `card κ`. For `κ = Fin 0` it is zero; this was checked in Lean. The unbiasedness theorem correctly requires `[Nonempty κ]` (`Unbiased.lean:84`). Preserve a total definition if convenient, but document the zero-sample convention at the definition. SLQ/XTrace have the same average convention.
- Power/Lanczos relative error at `A=0` is explicitly zero, and the proved PSD expectation bounds include empty dimensions. This is a reasonable declared convention.
- `tanSqAngle` (`Krylov/Spectral/Ritz.lean:236`) and `tanThetaMax` use zero at vanishing overlap. Their docstrings disclose this, and real division/trigonometric functions in Lean are total. It is unsuitable as an extended measure of misalignment at orthogonality; use the current quantities only with the stated nonzero-overlap interpretation, or add an extended-valued interface if such comparisons are needed. Do not infer that the error is small from this junk value.
- Polynomial degree uses Mathlib's `WithBot` convention. In particular, the zero polynomial has degree below zero, making the `q=0` Krylov characterization describe `{0}` correctly rather than an empty witness domain.

## Custom definitions worth keeping

- `krylovSpace` and `blockKrylovSpace`: direct `Submodule.span` definitions with standard generator semantics. Add generic lemmas; no replacement abstraction is needed.
- `arnoldiBasis` (`ArnoldiProcess.lean:50`): directly uses pinned Mathlib's `gramSchmidtNormed`. `arnoldiDecomp` at line 247 constructs the witness under the grade bound, so the bundled decomposition is not merely an assumed output certificate.
- `IsAffineMinimizer` (`Minimizer.lean:49`) has an explicit bridge to Mathlib's `IsMinOn` and `AffineSubspace` at line 58. CG/GMRES specialize it, prove existence, and obtain convergence from a shared approximation argument. These are sensible specifications even before every recurrence bridge is finished.
- `qrAlgorithm` (`QRAlgorithm.lean:77`) abstracts over a QR routine and explicitly checks `IsQR` along the run. That parameterization is reasonable. Correctness of a particular routine and scaffold-free instantiation must be distinguished from the generic theorem.
- `spectralMeasure`, quadratic-form trace estimators, and `cfc`-based compression formulas are recognizable domain concepts on Mathlib measures/matrices, not a competing probability or functional-calculus framework.
- Chebyshev residual/amplifier polynomials reuse Mathlib's `Polynomial.Chebyshev.T`. `chebyshevUSequence` (`BestApproximation/SineBasis.lean:18`) is a small adapter into Mathlib's `Polynomial.Sequence`, followed by its spanning theorem; it is useful integration rather than reinvention.
- The Bernstein ellipse/Joukowski definitions and explicit analytic truncations support genuine analytic proofs. Classical choice for a proved interpolation/critical-point witness is not, by itself, a vacuous definition.

## Suggested sequence before a reusable-library checkpoint

1. Correct or restrict the Ritz definition and prove the compression-eigenvalue bridge, including negative-definite and trivial-space regression examples.
2. Establish the trusted import surface and prevent `sorryAx` from entering it; complete CG/Lanczos realization before claiming certified recurrences.
3. Generalize the algebraic Krylov API and add concrete, breakdown-aware stochastic estimator constructors with size/cost guarantees.
4. Add the real Chebyshev coefficient bridge and small totalization documentation improvements.

This review found one reproduced semantic-definition failure and several specific trust/usability gaps. It does not claim all 774 declarations were individually re-proved or all numerical algorithms were exhaustively audited.
