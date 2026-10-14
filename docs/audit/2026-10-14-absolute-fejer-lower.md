# Absolute-value finite Fejér lower certificate

`Polynomial/BestApproximation/AbsoluteLower.lean` checks with `autoImplicit=false`
and proves
`1 / (18 * Real.pi * (n + 1)) ≤ absoluteMinimaxError n`.
The error is the library's genuine attained minimax error on `[-1,1]`.

The actual dual integral is convolution at angle `π/2` with
`cos(4Kt) F_K(2t)`, where `K = n / 2 + 1`. The checked reusable
`ForMathlib/Analysis/FejerModulation.lean` proves its finite frequency expansion,
the doubled positive kernel's normalized Haar integral one, and the positive
majorant of the modulated kernel's absolute value. Thus the actual dual annihilates
every degree-at-most-`n` polynomial and is bounded by the uniform competitor error.

The already proved absolute-value Chebyshev coefficients give each even cosine
moment at the cusp exactly `-2 / (π * (4j²-1))`. Every frequency in the finite band
has `K ≤ j ≤ 3K`, so its magnitude is at least `1 / (18πK²)`. The averaged
Dirichlet representation counts `(K+1)²` terms before division by `K+1`; hence
`(K+1)/(18πK²) ≤ -absoluteFejerDual K abs`. Since `K ≤ n+1`, this implies the
displayed minimax lower bound. This uses a slightly coarser intermediate denominator
than the source's `π(36K²-1)` and retains exactly its final `1/(18π(n+1))` constant.

There is no assumed separating functional, unspecified positive constant, numerical
Bernstein value, additional axiom, or admitted proof. The separate scalar Bernstein
sequence convergence route may now combine this lower bound with the actual
Chebyshev upper bound to enclose its positive limit between `1/(18π)` and `2/π`.
