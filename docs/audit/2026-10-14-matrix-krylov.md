# Final matrix and Krylov statement audit

All 158 primary records in the companion JSON now carry final audit phase,
current source signatures, exact readbacks and current open clauses. Each
complete original record is preserved verbatim under baseline_audit, and the
original prose below is historical evidence. Earlier uncovered-clause and
pending-index observations are not substituted for the final judgment.

The final source inventory records 1,266 actual declaration signatures.
Unchanged manual baseline mathematical judgments are retained; this readback
does not claim independent proof rederivation of every legacy theorem. The
parent owns full compilation, trusted dependency audits, layer checks and
declaration/atlas synchronization. No Lean or Lake build was run for this
report refresh.

For this PR, the user deferred the entire Gauss contour target AQ24–AQ25.
Its complete pre-deferral reports and contour-specific work are preserved in
the [local archive](E:/NLAlib-local/DeferredJordanContour-2026-10-14). The other
30 retained source targets and their theorem evidence are unchanged. This
report contains no new Gauss contour completion claim.

## Complete structural and complex additions

The field-general Krylov grade family now has actual vector-relative minimal
polynomials, annihilator ideal/divisibility, dimension min(q,grade),
independence thresholds and invariant terminal spaces. Zero vectors and empty
matrices are included. General K_q is only mapped into K_(q+1); invariance of
the same space occurs at and after the grade.

The companion/cyclic family has concrete companion characteristic and minimal
polynomials, full-grade Krylov basis realization, unique bounded-degree
commuting-matrix evaluations and the actual splitting-field eigenspace
criterion. The real-matrix geometric criterion is applied to complexification,
whose minimal-polynomial degree is proved preserved. Two real rotation blocks
show why real eigenvalues alone cannot characterize a real cyclic matrix.

The actual residual-polynomial interfaces include both iterate directions,
extended supremum/infimum minimax on arbitrary complex sets, degree/domain
monotonicity, empty/unbounded conventions, compact attainment modulo invisible
evaluation directions and the exact positive-interval Chebyshev value.
Invertibility is needed for the specified-iterate residual converse; a forward
error identity with a supplied exact solution does not need it.

The numerical range is now the actual finite complex quadratic-form image,
with compactness, spectrum/disk containment, affine and unitary rules,
orthonormal compression, full Toeplitz–Hausdorff convexity and the normal
convex-hull identity. The real-image eigenvalue interval requires positive
dimension; an empty matrix has empty numerical range.

The PSD Hermitian-part family now proves actual common kernel and rank
relations, row/column inclusion, principal invertibility in the PD case,
relative determinant factors, Ostrowski–Taussky/equality, determinant-sum and
Fan power bounds. Empty dimensions are included in the kernel and basic
determinant clauses; the sum inequality needs dimension at least two and the
2/n exponent needs positive dimension.

Actual canonical Jacobi and signed Lanczos identities use mass M=‖b‖²:
first eigenvector-coordinate squares are weights for μ_b/M, and multiplying
by M gives original-measure weights and the finite second-kind approximant.
The finite unscaled resolvent is not the full nonterminal Stieltjes transform.
Descending strict interlacing is θ_i(T_(q+1))>θ_i(T_q)>θ_(i+1)(T_(q+1))
and requires a valid size-(q+1) decomposition, hence q+1≤grade.

Signed normalized multiplied/confluent CD uses 1≤m<q. Monic norm-divided
kernels may use a zero-norm top polynomial when preceding norms are positive;
fully normalized top formulas require h_m>0. Size-q stored norm products and
alpha quotient bridges use j<q. The absent total coupling a_q=0 does not
compute a nonterminal h_q; characteristic recurrences and continuants still
include the final leading order. Exact-grade termination is separate.

Ordinary nested fractions require all intermediate denominators nonzero,
derived for nonreal shifts and in the existing real-above-spectrum branch.
Robust determinant/spectral fractions cover every final off-spectrum shift,
including real tail poles. The totalized Cramer identity at a spectral pole
is not an ordinary analytic resolvent there. Order zero has fraction zero and
empty determinant one, without a first coordinate or normalized zero-mass rule.

This Jacobi readback follows the corrected human atlas and current sources;
final declaration extraction/synchronization remains pending. It is not a
fresh whole-index verification.

Representative actual endpoints and reviewed full clause inventories are
recorded in the JSON and structural/Jacobi companion inventories. These include
NLAlib.aeval_mulVec_eq_zero_iff_vectorMinpoly_dvd,
NLAlib.natDegree_minpoly_real_eq_card_iff_complex_eigenvalue_finrank_eq_one,
NLAlib.exists_polynomialSupNorm_eq_residualMinimaxError,
NLAlib.convex_numericalRange and
NLAlib.re_det_rpow_add_norm_det_rpow_le_norm_det_add_I_smul_rpow.

## Corrected statements and exact scope

Spectral norm uses a total operator-norm definition; a maximum over unit
vectors needs a nonempty domain. Wide full-row-rank matrices can have positive
smallest thin singular value while the smallest domain Gram eigenvalue is
zero. The valid SVD comparison uses the zero-padded domain singular value or a
tall-only restriction.

Householder uses the chosen sign equal to one at zero, not ordinary sign(0).
The power-iteration absolute Rayleigh bound uses a bound on all absolute
eigenvalue distances, such as spectral diameter. Ordering the dominant
eigenvalue by modulus does not make a signed extreme difference nonnegative.

Map conditioning has actual Euclidean derivative and scaled relative-map
bridges. Nonzero normalization is required for a relative interpretation;
the total coordinate-scaled formula does not force the entire norm to vanish
when one coordinate is zero. The parent corrected that misleading doc sentence.
For example, identity on R² at (0,1) gives scaled matrix diag(0,1) of norm one.

Lanczos recurrence and CG convergence are proved for their supplied mathematical
decomposition/variational specifications. The explicit Lanczos and CG recursion
realizations remain separately named scaffold cards. The same distinction is
retained for the QR/simultaneous-iteration and Golub–Kahan realization scaffolds.
No algebraic specification theorem is advertised as an implemented recursion
or operation-count guarantee.

## Retained open clauses

LU growth upper bounds remain proved, but the worst-case attainment witnesses
are open. Hessenberg realization, tridiagonality and implicit-Q sign uniqueness
remain proved, while the advertised Arnoldi-basis coincidence needs a genuine
graded-Krylov realization bridge. These composite claims remain partial.

The real diagonalizable GMRES bound does not close the complex-diagonalization
and normal worst-case sharpness variants. The equal-width disconnected MINRES
rate, full FOM solvability/inverse/residual contract and full preconditioned
Richardson guarantee remain open. Rayleigh quotient iteration has no closing
local cubic-rate theorem and needs an explicit singular-shift convention.
The optional named Kantorovich equivalence bridge remains separate from its
two actual inequalities and dimension guards.

Other unformalized targets and existing scaffolds keep their explicit open
judgments. The user-excluded Crouzeix–Palencia analytic interface remains a
source statement, not a local completion claim.

## Shared genuine generic-rank prerequisite

The new MvPolynomial.ae_eval_ne_zero applies to atomless sigma-finite product
laws, with Lebesgue measure as a special case. Actual Gram determinant
polynomials are nonzero by embedded identity witnesses. Matrix.volume_det_mul_transpose_eq_zero
and Matrix.volume_det_transpose_mul_eq_zero prove the flat-entry singular Gram
loci Lebesgue-null under explicit wide/tall inequalities, including zero-size
Gram determinant one. Gaussian consumers reuse this genuine proof. This is a
shared matrix/measure prerequisite; its Gaussian probability card is audited
in the root-owned probability report, not added as a duplicate matrix card.

## Preserved baseline audit

# Matrix and Krylov statement audit — 14 October 2026

Reviewed 158 cards from the matrix areas and Krylov algebra, spaces, solvers and eigenvalue areas against their human hypotheses and linked interface inventory. The JSON preserves the exact baseline signatures and source locations. Orthogonal-polynomial mathematics is audited separately.

This audit separates mathematical statements from implementation guarantees. Kernel compilation proves the Lean proposition; it does not automatically establish that every sentence on a card has been formalized. Findings below preserve true but uncovered clauses instead of silently deleting or weakening them.

## Complete additions

The field-general Krylov grade, vector-relative minimal polynomial, companion/cyclic-vector equivalences (including complexification), and residual-polynomial minimax contracts now have reviewed proof families in `2026-10-14-structural-proof-families.json`. Their modules passed direct Lean checks without new unfinished proofs.

## Findings requiring action

- **krylov-subspace — invariance**: For arbitrary q the proved map is A K_q subset K_(q+1), not invariance of K_q. For A=[[0,0],[1,0]] and b=e1, K1 is not A-invariant. True same-space invariance occurs at/after the grade.
- **lanczos-recurrence — algorithm_scope**: The algebraic LanczosDecomp recurrence is kernel-proved. The recursion-to-decomposition bridge lives under the separate scaffold lanczos-recurrence-algorithm. Distinguish this specification from a proved guarantee of the explicit Lanczos recursion.
- **cg-convergence — algorithm_scope**: The rate is proved for the variational IsCGIterate specification. The realization by cgRecurrence is separately catalogued as a scaffold, so the card should distinguish the proved specification guarantee from an unfinished algorithm bridge.
- **matrix-norms-def — empty_dimension**: The displayed maximum over the unit sphere requires a nonempty column index. The total Lean spectral norm is zero when the domain is zero-dimensional; use an operator-norm definition and state this empty convention.
- **svd-def — rectangular_domain**: The smallest thin singular value of a wide full-row-rank matrix is positive while the smallest eigenvalue of A* A is zero. State the domain-side, zero-padded singular value at card(columns)-1, with positive domain dimension, or restrict the thin smallest-value identity to tall matrices.
- **residual-polynomial — unnecessary_hypothesis**: The specified-iterate residual converse requires IsUnit A, but the forward error identity for an affine-Krylov iterate and a supplied exact solution does not. Minimal-polynomial, attainment and monotonicity additions now close the mathematical result family.
- **gmres-diagonalizable — coverage_gap**: The current theorem is a real diagonalizable squared-residual bound. The card also asks for complex diagonalization of real data and a normal worst-case sharpness equality; these clauses are not yet linked and the candidate status is accurate.
- **minres-bound — coverage_gap**: Existing declarations cover a polynomial spectral bound and positive single-interval Chebyshev rate. The equal-width disconnected-interval rate remains open and candidate status is accurate.
- **fom-def — coverage_gap**: Arnoldi orthogonality equivalence and SPD-to-CG bridge are present. Full unique-solvability iff, explicit inverse representation and residual formula remain open; current candidate status is accurate.
- **richardson-iteration — coverage_gap**: Existing implementation and rates are unpreconditioned P=I. The full preconditioned A/P-norm guarantee is not closed; current candidate status and partial tags are accurate.
- **field-of-values-def — empty_dimension**: The numerical range is empty for zero-dimensional matrices. The equality Re W(A)=[lambdaMin(H),lambdaMax(H)] needs positive dimension. Other set clauses are valid in empty dimension.
- **lu-growth-factor — coverage_gap**: Both indexed Lean results prove the upper bound. No indexed witness attains the bound, so the card's additional sharpness clause is not yet formalized.
- **householder-reflector-def — sign_at_zero**: The library uses householderSign(t)=1 for t>=0 and -1 otherwise. The ordinary real sign has sign(0)=0 and makes the displayed reduction false for a nonzero x with first coordinate zero. Specify the chosen sign convention.
- **hessenberg-reduction — coverage_gap**: Realization, tridiagonality and implicit-Q sign uniqueness are linked. The human assertion that the columns form the Arnoldi basis needs a graded-Krylov realization bridge or an explicit derivation from the unreduced Hessenberg relation; no such bridge is indexed on this card.
- **power-iteration — dominant_negative_eigenvalue**: The dominant eigenvalue is ordered by modulus, so lambda1-lambdan need not be nonnegative. For diag(-2,1) it is -3, contradicting the claimed absolute Rayleigh bound for a mixed vector. The Lean theorem correctly takes D>=all absolute distances to the selected eigenvalue; use spectral diameter lambdaMax-lambdaMin or this D.
- **rayleigh-quotient-iteration — singular_shift**: The local cubic rate needs a well-defined nonsingular shifted solve, or a specified termination/continuation convention at a shift equal to an eigenvalue. A vector near the middle eigenvector of diag(-1,0,1), with equal small extreme components, has Rayleigh quotient exactly zero without being an eigenvector. The open card has no Lean statement yet.
- **companion-matrix — splitting_field**: The geometric criterion must use eigenvalues over a splitting field. For real A two copies of a 2x2 real rotation have no real eigenvalues but minimal degree 2<4. ScalarExtension now proves the correct complexification criterion.
- **psd-hermitian-part — dimension**: The Fan expression with 2/n requires n>=1. The determinant-sum inequality correctly needs n>=2; H=K=[1] refutes it at n=1. The determinant bound/equality and kernel statements include n=0.
- **kantorovich-inequality — coverage_gap**: The two inequalities are proved separately. Their equivalence is a mathematical source observation; no Lean equivalence declaration is indexed. The extreme-eigenvalue ratio also needs positive dimension, while the sandwich form includes empty matrices.

## Scope of new numerical-range and accretivity work

NumericalRange, NumericalRangeNormal, NumericalRangeHermitian, NumericalRangeTwo and NumericalRangeConvex now prove every numerical-range clause. Convexity includes the full Bloch sphere parameterization, a reusable sphere/closed-ball linear-image lemma, and compression to the span of two vectors. Empty dimensions are included except for the explicitly guarded real-image interval. The reviewed complete family is in the companion JSON.

AccretiveKernels, AccretiveInclusion and AccretiveDeterminant now prove every kernel, rank, row/column inclusion and determinant clause. The shared definite-pair congruence is generalized to real/complex scalars; the Fan bound uses the continuous PSD-boundary extension of the existing Minkowski inequality. The reviewed full family is in the companion JSON.

## Integrity and limitations

Every baseline NLAlib declaration is included; historical external references are preserved separately. Each local declaration is included with its signature, module, line and unfinished-dependency indicator. Root must regenerate the index and synchronize the atlas after integrating proofs, then run the complete repository/trust checks. Cards with no Lean declaration remain open. Excluded Crouzeix–Palencia mathematics is only statement-audited. The report records unsupported clauses and does not certify them by status label alone.
