# Analytic and rational formalization scope

The reviewed families in the adjacent JSON file are the source contracts from
`open_mathematical_items_operator_derivations.tex` and the corrected coefficient
route in Section 4 of `four_focused_mathematical_reroutes.tex`.

The second-kind family proves native complex Bochner transforms, the associated
polynomial recurrence, actual Gauss residues, both exact transform cancellations,
the explicit order-at-infinity estimate, locally uniform Markov convergence, and
exact finite-support termination. Continued fractions use polynomial numerator /
denominator pairs or justified nonzero tail denominators. A formal literal nested
fraction at an intermediate zero is not identified with the full resolvent.

The rational Gauss family constructs the actual divided measure and its actual
rule for a finite positive measure on a compact support enclosure. Finite mass
is explicit: compact support alone does not imply it. Positivity of the
denominator and the requested support threshold are explicit. Repeated poles are handled by
the unique cleared partial-fraction system. Its polynomial part has degree below
`d-m`; in the edge case `d=m` this is the zero polynomial, rather than a constant.
The explicit scalar conversion identifies monic factors `X-v` with the source
factors `1+ζX`. No rational Krylov algorithm is claimed.

The Christoffel--Uvarov measure specialization also uses finite mass and the
actual divided polynomial moments. Its generic coefficient/determinant branch
works over a scalar field with the specified finite nonsingular Hankel systems;
it does not require a representing measure or impose positivity on that branch.
The Christoffel--Uvarov family uses the focused re-derivation's actual real
coefficient/remainder formulation as its primary contract. It proves the full
monomial and compressed original-polynomial determinants and their actual
normalization minors, rather than assuming a nonzero determinant. The compressed
system uses `min(n,m)` inverse-moment rows; `m` separate pole equations would be
incorrect when `m>n`. Polynomial remainders cover repeated numerator roots and
the full monomial construction does not require original polynomials beyond a
finite-support termination index. Traditional simple-root evaluation / individual
Cauchy-transform row presentations are not separately exposed Lean corollaries;
their row-coordinate changes are optional presentations in the focused source.
The arbitrary-complex-point nonvanishing claim is excluded as mathematically
false; the justified exterior-real Christoffel result is separate.

The general Jordan-contour target was deferred by the user on 2026-10-14.
The contour specializations and prerequisite development are preserved locally
at `E:/NLAlib-local/DeferredJordanContour-2026-10-14` and excluded from this PR.
Shared Stieltjes and second-kind algebra remains partial evidence for that card;
it does not establish the general contour integral formula.
