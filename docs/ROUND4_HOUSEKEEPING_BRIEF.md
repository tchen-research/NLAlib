# Round 4: housekeeping

Read `docs/STANDARDS.md` and `docs/ROUND1_BRIEF.md` (working rules: single-file checks with
`lake env lean`, build oleans with `lake build NLAlib.<Module>`, wait and retry on a lock, no full
`lake build`, no atlas edits). Everything below is a move, a merge or a rename; no statement
changes except free generalisations. Every file you touch must end warning-free. Write a rename
map `docs/renames/2026-10-09-housekeeping-<group>.json` (`{"NLAlib.old": "NLAlib.new"}`) for every
public name that changes, and list moved declarations (same name, new module) in the report.

New in STANDARDS §2: `NLAlib/ForMathlib/` (layer −1, imported by anything) holds general facts
that are not about NLAlib's objects and are candidates for upstreaming: real inequalities,
integrability of finite sups, measure-preserving coordinate updates, `det ≠ 0` from full rank.
Files there are named by Mathlib's directory they would land in (`ForMathlib/Analysis/Real.lean`,
`ForMathlib/MeasureTheory/Integral.lean`, `ForMathlib/LinearAlgebra/Matrix.lean`).

## Groups (exclusive file ownership)

**H1 — matrix concentration** (`NLAlib/Concentration/Matrix/**`, `NLAlib/Concentration/Matrix.lean`,
`docs/TroppMatrixConcentration.md`):
1. Merge the helpers duplicated across files into public, named lemmas in one shared file
   `NLAlib/Concentration/Matrix/Defs/Calculus.lean` (imports the other Defs files): the six
   copies of `matrixExp_smul_eq`, `traceExp_eq_sum`, `spec_le`, `abs_le_norm`, the reindexing group
   (`reindexStarC`, `norm_reindex`, `lambdaMax_reindex`, `integral_reindex`), `dilLin`,
   `dilation_sq`, `incl₁`/`incl₂`, `integral_fromBlocks_diag`. One copy each, STANDARDS §1 names,
   every former copy deleted and its uses redirected.
2. Rename the chapter-flavoured module files: `Defs/Ch4ScalarLaws` → `Defs/ScalarLaws`,
   `Defs/Ch5ChernoffFunctions` → `Defs/ChernoffFunctions`, `Defs/Ch7Intrinsic` →
   `Defs/IntrinsicDimension`, `Defs/Ch8Entropy` → `Defs/RelativeEntropy`, `Defs/Ch8JointTensor` →
   `Defs/JointTensor` (git mv; update every import, including `Matrix.lean` and the docs table).
3. The global Borel `MeasurableSpace (Matrix m n ℂ)` instance in `Defs/Probability.lean` stays (the
   whole development is built on it) but its docstring must say it is a deliberate exception to
   STANDARDS §3 and why; report whether it could be made `scoped`.
4. `intrinsic_matrix_bernstein_expectation` states `∃ C`; add a docstring line naming this as the
   open item (atlas `intrinsic-dimension`), do not attempt the constant now.

**H2a — Gaussian concentration and comparison, scalar concentration, ForMathlib**
(`NLAlib/Gaussian/Concentration/**`, `NLAlib/Gaussian/Concentration.lean`,
`NLAlib/Gaussian/Comparison/**`, `NLAlib/Gaussian/Comparison.lean`, `NLAlib/Concentration/Scalar/**`,
`NLAlib/Concentration/Scalar.lean`, `NLAlib/ForMathlib/**` (create), `NLAlib/ForMathlib.lean`):
1. Move `entropy_pi_le_sum_integral_entropy_update` (and the entropy/Gibbs helpers it needs) to
   `NLAlib/Concentration/Scalar/EntropyTensorization.lean`, and Herbst's argument
   `integral_exp_mul_le_exp_of_entropy_le` to `NLAlib/Concentration/Scalar/Herbst.lean` (layer 1;
   they are not Gaussian-specific). `Gaussian/Concentration/LogSobolev.lean` and `Herbst.lean`
   then import them; the Gaussian-specific Lipschitz entropy bound stays in Gaussian.
2. Create `NLAlib/ForMathlib/Analysis/Real.lean` with `sqrt_sum_sq_le_sum_abs`,
   `abs_mul_log_le_sq_add_one`, `abs_add_mul_log_add_le`, `abs_mul_exp_le_exp_two_mul_add_one`,
   `Gamma_add_half_le_mul_sqrt`-style facts you own, and
   `NLAlib/ForMathlib/MeasureTheory/Integral.lean` with `measurePreserving_update_pi`,
   `integrable_comp_update_pi`, `integral_integral_update_pi`, `integrable_integral_update_pi`,
   `ae_integrable_comp_update_pi`, `integral_le_sqrt_integral_sq`-type lemmas from
   `LowRank/Assembly` are NOT yours (leave). Delete the originals and redirect uses.
3. `gaussianMatrix_eq_map_curry` in `LipschitzConcentration.lean`: group H2b is adding the same
   lemma (same name) to `Gaussian/Basic.lean`. At the END of your work check `Gaussian/Basic.lean`;
   if it has `gaussianMatrix_eq_map_curry`, delete yours and import Basic; if not, keep yours and
   say so in the report.
4. Rewrap lines over 100 characters in your files (Mathlib's limit) where it is mechanical;
   do not restructure proofs to do it.

**H2b — the rest of Gaussian, the matrix toolkit, sketching**
(`NLAlib/Gaussian/{Basic,Invariance,Moments,InverseMoments,Conditioning,Wishart,Extreme}.lean`,
`NLAlib/Gaussian/InverseMoments/**`, `NLAlib/Gaussian/Extreme/**`, `NLAlib/Gaussian/Moments/**`,
`NLAlib/Gaussian.lean`, `NLAlib/Matrix/**`, `NLAlib/Matrix.lean`, `NLAlib/Sketching/**`,
`NLAlib/LowRank/**` only for import fixes):
1. `Gaussian/Basic.lean`: add `gaussianMatrix_eq_map_curry` (from the private copy in
   `Invariance.lean`'s `map_flat_gaussianMatrix`; make it public here, delete the private copy),
   the `isGaussian_gaussianMatrix` instance, `hasGaussianLaw_id_gaussianMatrix`,
   `hasGaussianLaw_id_pi_gaussianReal` and the entry-moment lemmas from
   `Extreme/LinearForms.lean` (`integral_gaussianMatrix_entry_eq_zero`,
   `integral_gaussianMatrix_entry_sq_eq_one`, …), merged with Basic's private copies. Keep
   `linForm` and its lemmas in LinearForms. Do the Basic additions FIRST and build the olean
   (`lake build NLAlib.Gaussian.Basic`), because group H2a polls for `gaussianMatrix_eq_map_curry`.
2. Matrix layer homes: `frobSq_pinvR_eq_trace_inv` → `Matrix/Pseudoinverse.lean`;
   `specNorm_inv_self_mul_transpose_eq`, `specNorm_pinvR_sq` → `Matrix/Spectral.lean`;
   `exists_iInf_sqrt_mulVec_le_of_sigmaMin_le`, `sqrt_mulVec_smul_dotProduct` → `Matrix/Spectral.lean`;
   `det_ne_zero_of_rank_eq`, `posSemidef_inv_self_mul_transpose`,
   `abs_apply_le_apply_self_add_apply_self` → `Matrix/Pseudoinverse.lean` or a new
   `Matrix/Gram.lean`; `measurable_inv_self_mul_transpose_apply`, `measurable_specNorm_pinvR`,
   `measurable_specNorm_inv_self_mul_transpose`, `measurable_frobSq_of_entries`,
   `measurable_pinvR_entry` → `Matrix/Measurable.lean`; `mulVec_dotProduct_mulVec_self`,
   `mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`, `abs_dotProduct_mulVec_le_specNorm`
   (from `Sketching/SubspaceEmbedding.lean`) → `Matrix/Norms.lean`;
   `measurePreserving_orthonormalBasis_repr_pi_gaussianReal` → `Gaussian/Invariance.lean`;
   `prod_range_add_le_pow` → a new `NLAlib/ForMathlib/Algebra/BigOperators.lean`? No: ForMathlib is
   group H2a's; put it in `Matrix/Spectral.lean`'s neighbour… simplest: leave `prod_range_add_le_pow`
   where it is and list it.
3. Merge the duplicates between `Gaussian/InverseMoments.lean` and `InverseMoments/SchurComplement.lean`
   (same-named private vs public lemmas): one public copy each in the Matrix layer (item 2), both
   files use it. Replace the private Laplace-transform and a.s.-positivity lemmas in
   `InverseMoments.lean` by the public ones in `Extreme/ChiSquare.lean`; since `ChiSquare.lean`
   imports `InverseMoments.lean` for the first inverse moment, MOVE
   `integrable_and_integral_inv_sum_sq_gaussianReal` (+ `_fin`) into `ChiSquare.lean` and reverse
   the import. The private `exists_orthonormal_ker_sq_dist_rowSpace` vs
   `exists_orthonormal_sq_dist_rowSpace_eq_sum_sq`: keep the stronger one, public, in
   `InverseMoments/SchurComplement.lean`. `Gamma_add_half_sq_le` vs `Gamma_add_half_le_mul_sqrt`:
   keep one in `ChiSquare.lean`.
4. Split `Gaussian/InverseMoments.lean` (671 lines) into `InverseMoments/Mean.lean` (the
   inverse-Wishart mean and the pseudoinverse Frobenius moment) and `InverseMoments/Residual.lean`
   (Schur diagonal inverse, residual law); `Gaussian/InverseMoments.lean` becomes the aggregator
   of the whole directory (and `Gaussian/Wishart.lean` goes away: fold its imports into it).
5. Rewrap lines over 100 characters in your files where mechanical.

## Report
Per the Round 1 brief, plus: the list of moved declarations (name, old module, new module), the
rename map, and final `lake build` outputs for `NLAlib.Concentration`, `NLAlib.Gaussian`,
`NLAlib.Matrix`, `NLAlib.Sketching`, `NLAlib.ForMathlib` as applicable.
