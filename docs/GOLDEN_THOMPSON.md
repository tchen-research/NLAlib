# Golden–Thompson formalization

Based on upstream commit `641010e4172758f5963099727a2f88795daf3bd5`.
The other five matrix-toolkit targets in the requested screenshot are already marked proved
upstream and use their existing implementations: Courant–Fischer, Eckart–Young–Mirsky,
Weyl–Mirsky, Cauchy interlacing, and the von Neumann trace inequality.

For complex Hermitian matrices `H` and `K` over any finite index type, including the empty
type, this change proves

```lean
traceExp (H + K) ≤ (Matrix.trace (matrixExp H * matrixExp K)).re
```

`NLAlib.golden_thompson_trace` gives the direct complex-trace statement in `ComplexOrder`.
Both traces are real; this form retains equality of their imaginary parts.
`NLAlib.traceExp_add_matrixLog_le` gives the equivalent positive-definite variant
`traceExp (H + matrixLog X) ≤ (Matrix.trace (matrixExp H * X)).re`.

The proof uses the existing Lieb concavity theorem. In an eigenbasis of `H`, averaging `X`
with each coordinate sign reflection increases the Lieb trace function while preserving
positive definiteness. Finitely many averages leave the original diagonal. Functional
calculus on that diagonal gives the weighted trace, and substituting `X = matrixExp K`
proves Golden–Thompson. The original matrices need only be Hermitian.

Files:

- `Matrix/CoordinatePinching.lean`: coordinate reflections, finite averaging, and its exact
  diagonal endpoint.
- `Concentration/Matrix/OperatorConvexity/UnitaryCalculus.lean`: unitary/reflection covariance,
  real diagonal functional calculus, and finite-index transport.
- `Concentration/Matrix/OperatorConvexity/GoldenThompson.lean`: the trace inequality and variants.

The barrels expose these modules. The `golden-thompson` atlas entry records the three main
declarations, usage, and dependencies on Lieb concavity and matrix functional calculus.
No existing theorem statement or proof is modified.

Source: Bhatia, *Matrix Analysis* (1997), Chapter IX.3; the finite pinching argument in
the supplied matrix-toolkit operator derivations, §7.

## Verification

The full library build passed (4162 jobs). The audit output was:

```text
audited 1791 theorems in [NLAlib]; 0 depend on sorry (scaffolds): []
OK: no axioms beyond propext / Classical.choice / Quot.sound (and sorryAx in scaffolds)
```

Import-layer checks, declaration extraction, atlas synchronization, atlas reference checks,
and naming checks passed. The generated index contains 1859 public declarations.
Full Draft 2020-12 schema validation passed using both Python `jsonschema` and Ajv;
the latter also checked the date and URI formats.
