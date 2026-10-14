# Final estimation and low-rank statement audit

All 32 primary records in the companion JSON now carry final audit phase,
actual current source signatures and exact current open clauses. Original
records are preserved verbatim under baseline_audit and the original prose
below is historical evidence. The final inventory has 171 current declaration
signatures. This statement readback does not replace the parent's full
compilation, trust, layer and index checks; no Lean or Lake build was run here.

For this PR, the user deferred the entire Gauss contour target AQ24–AQ25.
Its complete pre-deferral reports and contour-specific work are preserved in
the [local archive](E:/NLAlib-local/DeferredJordanContour-2026-10-14). The other
30 retained source targets and their theorem evidence are unchanged. This
report contains no new Gauss contour completion claim.

## Genuine trace and diagonal wrappers

NLAlib.abs_trace_compression_add_quadForm_residual_le is a frame-independent
bound for the actual compressed-trace plus residual-quadratic kernel, valid
for every real matrix, including nonsymmetric matrices and empty indices.
It derives product-law integrability from probe second moments, with no frame
moment premise.

NLAlib.integral_deflatedTraceEstimate_comp_eq_trace_of_measurable and
NLAlib.integral_deflatedTraceEstimate_comp_eq_trace_of_ae_hasOrthonormalCols
prove independent measurable random-frame deflation unbiasedness, including
almost-sure orthonormality on the original probability space. The average is
nonempty; its probes have the stated isotropic second moments. No regular
conditional distribution or standard-Borel condition is introduced.

NLAlib.indepFun_leaveOneOutSketch_col derives held-out independence from
disjoint subfamilies. NLAlib.integral_leaveOneOutDeflatedTraceEstimate_eq_trace_of_iIndepFun
then proves the actual measurable leave-one-out average unbiased without an
integrability conclusion supplied as a premise. Independent probes may have
different distributions; exchangeability alone is insufficient. The theorem
uses supplied measurable orthonormal correction maps depending only on the
other probes and does not assert measurability of an arbitrary selected basis.

The direct NLAlib.integral_mul_mulVec_apply_eq_of_second_moments proves
diagonal-estimate unbiasedness from isotropy alone, without zero means or
independence. General variance still needs centered independent coordinates
and a common finite fourth moment; actual Gaussian/Rademacher wrappers derive
those premises. The formula is sum_j A_ij²+(m4−2)A_ii².

## Independent interpolative-decomposition mathematics

NLAlib.exists_interpolative_decomposition selects distinct actual columns,
gives identity interpolation and coefficients bounded by one, and proves
spectral error at most sqrt(1+k(n−k)) times the library's zero-based sigma_k.
The premise is k≤rank A. The actual rank-sized endpoint
NLAlib.exists_exact_interpolative_decomposition reconstructs A exactly,
including rank zero and empty labels. Its proof uses the existing genuine
strong-RRQR existence theorem.

This independent ID item is retained under the user's exclusion of only
Chen–Persson LRA work. Its composite card remains partial: an existence
selection with coefficients bounded by one does not realize a computable
coefficient-two selection algorithm or certify its cost.

## Reopenings and algorithm boundaries

The existing Nyström structural projector, PSD, Gram-residual and exact
trace/spectral-norm-square facts are genuine. The retained joint-block
generalized Schur-complement clause is not closed by a named theorem and the
composite card remains partial. Sketched regression has the actual fitted
core/noise and projection-residual isometry; the arbitrary complementary-range
error-matrix clause also remains open.

The candidate randomized Nyström theorem currently bounds expected residual
trace by the Gram factor's best-rank squared Frobenius optimum. A full nuclear
error/eigenvalue-tail statement still needs the PSD nuclearNorm=trace and
factor-optimum spectral-tail wrappers. It is not promoted from the trace bound.

Partial Cholesky requires PSD A even when zero/repeated pivots are permitted.
Its residual positivity, pivot-zero and factor-residual identities are trusted;
the exact column-Nyström identity remains a named scaffold and its Schur
consumer inherits that dependency.

Full Hutch++ high-probability relative trace complexity and the gap-independent
block-Krylov rank-k extraction/probability theorem are separate unfinished
algorithm guarantees. Genuine unbiased trace kernels, deterministic polynomial
filters and variance bounds do not supply those probability or operation-count
conclusions. The standalone RSVD Gaussian tail target also has no closing
local theorem.

Chen–Persson early-truncation and conditional external cards remain outside
new formalization. Existing trusted low-rank facts are statement-audited;
external references are not recast as local proofs. The projected truncation
wrapper remains a genuine independent coefficient-one bound and its displayed
coefficient-two corollary, without settling the excluded early-truncation work.

## Domain and library-design readback

The actual weak-threshold Gaussian relative Hutchinson endpoint requires
positive trace, nonempty probes and the stated epsilon range; at zero threshold
and A=0 the weak failure event is all samples. The spectral RSVD expectation
endpoint requires k≤n; zero-padding does not remove that premise.

The complex polynomial-filter bundle genuinely distinguishes its spectral
and explicitly scoped Frobenius norm statements, even when a pretty-printed
index renders both as the same norm symbol. Full row rank and positive head
filter minima are explicit. Its public scoped norm instances and raw Gram
frame equalities remain a named-norm/HasOrthonormalCols API-design issue.
The report retains that issue rather than claiming a migration occurred.

The shared generic polynomial-zero-set and flat-coordinate Gram null-set
proofs now derive the non-Gaussian algebraic prerequisite used by Gaussian
rank consumers. The root-owned probability report audits the distributional
endpoints; the matrix helper itself is not a law-free randomized algorithm
guarantee.

## Preserved baseline audit

# Estimation and low-rank statement audit — 2026-10-14

All 32 atlas cards in `estimation` and `lra` were compared with their owning sources and
exact indexed Lean signatures. The companion JSON records a separate mathematical and
correspondence assessment for every card, decisive signatures, unfinished dependencies,
and suggested metadata repairs. Candidate or external-only cards are explicitly pending;
reading their metadata is not a proof of the informal target.

The trace items need two genuine bridges beyond the existing fixed-frame identities:
uniform domination independent of the orthonormal frame, and independence of a held-out
probe from the remaining independent family. `Matrix/Norms/DeflatedTraceBounds.lean` proves
the exact bound for arbitrary nonsymmetric real matrices, including empty indices.
`Estimation/Trace/Independent.lean` uses it to derive product-law integrability and prove
independent measurable deflation and the leave-one-out average without an integrability
premise. An additional endpoint permits almost-sure orthonormality. Identical distributions
are unnecessary. These statements concern supplied measurable correction maps; they do not
silently assert measurability of an arbitrary choice of sketch-image basis.

The diagonal-estimation card had a smaller premise gap: isotropy alone does not imply zero
coordinate means, while its original general endpoint assumed centered independent
coordinates. The new direct second-moment endpoint covers the stated general unbiasedness.
The variance clause still needs explicit centered coordinates and a common finite fourth
moment, or the existing actual Gaussian/Rademacher laws.

Coverage gaps retained for coordination are the Nyström Schur-complement specification,
the sketched-regression isometry for arbitrary matrices in the complementary range, and
the candidate nuclear-error Nyström wrapper. Source claims must remain pending until those
clauses are linked to actual proofs. The Chen–Persson early-truncation cards remain excluded
from new formalization at the user's request. Their conditional external references are
reviewed without treating them as local trusted proofs.

Premise clarifications are needed for the Gaussian relative Hutchinson endpoint's positive
trace, the spectral RSVD endpoint's `k ≤ n`, and the required PSD matrix in partial Cholesky
(it is positivity of individual pivots that can be dropped). The complex polynomial-filter
proofs have correct mathematics but retain public scoped matrix norms and raw frame Gram
equalities; this is a library-design issue under the current named-norm/frame standards.

Validation for this slice: the deterministic trace-bound module, independent-estimation
module and modified diagonal-estimation module are checked individually with Lean. Root
coordination owns the full build, declaration extraction, atlas synchronization and
repository-wide trust/layer checks.
