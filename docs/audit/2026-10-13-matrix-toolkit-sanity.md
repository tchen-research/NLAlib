# Matrix toolkit coverage sanity check

This review compares the human atlas contracts with the existing Lean statements
on main after PR #35. It records existing proofs; it adds no mathematical proof
and does not change any statement or hypothesis.

All twelve reviewed entries have complete coverage by families of separately proved
declarations. Their component tags remain accurately marked `partial`; every
reviewed declaration is recorded as `sorry: false` in the declaration index.
The matrix toolkit consequently has 108 of 108 entries proved.
Previously, atlas synchronization could recognize only an individually complete
tagged declaration, so deletion of the former bundled declarations left these
completed families classified as candidates.

## Horn product inequality

`prod_singularValues_mul_le` proves the full product-prefix inequality, and
`sum_range_singularValues_mul_rpow_le` proves its positive-power-sum consequence.
The latter gives the stated Ky Fan comparison at exponent one. The statements
allow arbitrary compatible finite real index types, every padded prefix,
rank-deficient matrices, and empty shapes. Together they cover the entire
advertised contract.

## Least-squares perturbation

`norm_least_squares_sub_div_le` proves the exact finite joint data/matrix
perturbation solution bound. `norm_least_squares_residual_sub_div_le` proves the
stronger residual coefficient `1 + κ`, hence the advertised `1 + 2κ` coefficient.
`exists_least_squares_angle_error_bound` constructs the geometric angle and proves
the source first-order coefficient with an explicit quadratic remainder.

The quantities are the actual Moore–Penrose least-squares solutions, connected
to native minimization and uniqueness by `LeastSquaresEuclidean`. Rank
preservation is derived in `LeastSquaresPerturbation`, rather than assumed for
the perturbed matrix. The rectangular full-rank condition number is the named
Moore–Penrose norm product, as appropriate here. The explicit nonnegative
perturbation-size premise follows from the norm bound when the old solution is
nonzero, so it does not omit a source case.

## Normal matrices

`normal_iff_exists_unitary_diagonalization` and
`normal_iff_exists_orthonormalBasis_eigenvectors` cover the complex spectral
characterizations. `sum_norm_sq_characteristic_eq_frobSq_iff_normal` covers the
Frobenius characterization for a full root list with multiplicities.
`upper_fromBlocks_eq_diagonal_of_normal` covers block triangularity, and
`exists_unitary_similarity_iff_charpoly_eq_of_normal` covers similarity with
eigenvalue multiplicities preserved.

`exists_orthogonal_real_normal_form` supplies the real block form. Its predicate
combines nonadjacent subdiagonal blocks, equal paired diagonal entries, and
opposite off-diagonal entries; it therefore describes the actual scalar and
rotation-dilation blocks. The skew-symmetric and orthogonal specializations add
zero diagonals and the unit-circle equations. The rectangular Fuglede–Putnam
equivalence covers arbitrary compatible matrix sizes. Empty dimensions are
included throughout. These declarations jointly cover every advertised clause.

## LU row inclusion

`exists_isLU_iff_rowInclusion` proves the unit-lower LU equivalence, and
`exists_lower_unitUpper_iff_columnInclusion` proves the dual unit-upper
equivalence. `exists_unit_triangular_factorizations_of_leading_minors_through_rank`
gives both existence conclusions when leading principal blocks through the rank
are nonsingular. These are genuine row/column inclusion conditions on the
original matrix, without assuming nonzero pivots. Singular matrices, rank zero,
and empty matrices are covered.

## Ostrowski congruence eigenvalues

`exists_eigenvalues₀_congruence_scale` gives the sorted scaling factors between
the squared smallest singular value and squared spectral norm; the spectral norm
is the largest singular value by the existing spectral API. The nonnegative and
nonpositive eigenvalue bounds give the respective orders, including zero
eigenvalues. Positive and negative eigenvalue-cardinality inequalities prove
the advertised quantitative inertia consequence. The transformation may be
singular; no invertibility hypothesis was silently introduced.

## Bauer–Fike

The absolute-norm perturbation and residual quotient declarations cover the full
source contract for arbitrary complex diagonalizable matrices, invertible
diagonalizers, repeated eigenvalues, and every induced absolute vector norm.
The interface's compatible matrix-action bound permits the induced norm and
even larger compatible bounds. The normal perturbation and normal residual
declarations supply coefficient one for the spectral/Euclidean norm, without
requiring a Hermitian matrix or real spectrum. The nonzero approximate vector
premise is exactly the condition needed for the residual quotient.


## Remaining six matrix entries

| Entry | Existing proved components | Coverage conclusion |
|---|---:|---|
| `polar-decomposition` | 10 | Tall and wide arbitrary-rank existence; positive-factor uniqueness; exact full-rank isometry/coisometry uniqueness; inverse-square-root formula; common square factor; nearest factors in every invariant norm. |
| `orthogonal-procrustes` | 16 | Attained one-sided and two-sided minima; nearest scaled orthogonal matrix in positive dimension; separate empty case; Mirsky/von Neumann equality and both PSD cross-products. |
| `schur-product-inequalities` | 18 | Strict product positivity; powers and nonnegative power series with radius interface; exact exponential strictness; Oppenheim, inverse and minimum-spectrum bounds; symmetric-comparand quadratic dominance. |
| `log-det-concavity` | 12 | Strict log-det concavity and determinant Jensen equality; determinant-root concavity and Minkowski positive-proportionality equality in positive dimension; strict inverse-trace convexity and equality. |
| `psd-block-contraction` | 16 | Weak and strict identity-block tests, bilinear tests, contraction factors, relative spectral-radius tests, Schur test, equal diagonal blocks, inverse principal compression, and inverse Gram block positivity. |
| `hadamard-fischer-inequalities` | 23 | Hadamard and column-norm bounds with correct equality cases; Fischer; arbitrary-set Koteljanski including PSD continuity; normalized Szász monotonicity and nontrivial SPD equality. |

## Evidence and scope

- Polar: `exists_isometry_mul_sqrt_gram_eq`, `eq_sqrt_gram_of_isometry_mul_eq`,
  `polar_isometry_unique_iff_rank_eq_card`, `eq_polarFrame_of_isometry_mul_sqrt_gram_eq`,
  `exists_sqrt_rowGram_mul_coisometry_eq`, `polar_coisometry_unique_iff_rank_eq_card`,
  and `sqrt_rowGram_mul_eq_of_isometry_mul_sqrt_gram_eq` cover the factorization clauses
  in `Matrix/Factorizations/PolarDecomposition.lean`. The two
  `invariantNorm_sub_polar_le_sub_*` theorems in `NearestPolar.lean` cover the invariant
  norm minima on arbitrary finite real index types, including empty dimensions.
- Procrustes: the two `isLeast_frobSq_sub_orthogonal_*` theorems give attained minima;
  `frobSq_sub_mul_eq_of_cross_polar` identifies the polar minimizer.
  `ScaledOrthogonal.lean` treats positive dimension and the separate empty case.
  `frobSq_sub_eq_sum_singularValues_sub_sq_iff` and
  `posSemidef_cross_products_of_frobSq_sub_eq_sum_singularValues_sub_sq` cover equality
  without assuming rank or positive dimension.
- Schur: `posSemidef_map_of_nonneg_powerSeries` takes entrywise scalar `HasSum`, while
  `posSemidef_map_ofScalarsSum_of_lt_radius` derives it from the formal convergence
  radius. `posDef_map_exp_iff_rows_injective` includes the exact converse and empty
  index type. The minimum-eigenvalue theorem
  `max_sInf_spectrum_mul_le_sInf_spectrum_hadamard` requires a nonempty index type;
  add positive dimension explicitly to that human clause. The dominance theorem
  assumes all four comparands are real symmetric; arbitrary nonsymmetric comparands
  are deliberately excluded and a counterexample is already proved.
- Log-det: `strictConcaveOn_log_det` and `strictConvexOn_trace_inv` include the empty
  singleton cone. The determinant-root and Minkowski theorems require
  `0 < Fintype.card n`, and their equality factors are strictly positive. The human
  informal statement repeats “for n≥1” and “for some c>0” three times; the helper
  removes only those accidental repetitions.
- Block contraction: the weak square-root factorization includes singular PSD
  diagonal blocks and empty blocks. Strict product tests quantify over nonzero
  vectors in both blocks; strict sum tests quantify over pairs not both zero. The
  relative spectral-radius characterization assumes PD diagonal blocks. Inverse
  compression uses an injective finite index map, which includes every principal
  subset and the empty subset.
- Determinants: inequalities extend to PSD input, but SPD equality descriptions
  must not be carried unchanged to PSD input. The proved PSD Hadamard equality is
  `IsDiag ∨ ∃ i, A i i = 0`. Koteljanski's SPD equality is vanishing of the
  overlapping Schur off-diagonal block. Normalized Szász indices are valid positive
  orders; consecutive equality requires `1 ≤ k < card n` and PD input. No general
  singular-PSD equality classification is claimed for Fischer, Koteljanski, or Szász.

No complex generalization is needed to close any of these six present atlas contracts.
The exact reviewed clause-to-declaration mappings are recorded in each atlas entry's `proof_family`.
