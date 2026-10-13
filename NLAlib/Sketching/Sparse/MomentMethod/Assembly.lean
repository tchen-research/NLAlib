/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Sketching.Sparse.MomentMethod.Endgame
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Assembly record for the explicit SparseStack theorem

This module packages every displayed conclusion of the main theorem: the
literal operator-norm tail, its equivalent vector OSE success event, the exact
column sparsity, the rounded parameter lower bounds, and the strict explicit
size bounds.  The assembly theorem still accepts the concrete band envelope;
the final module supplies it from the operator estimates.
-/

namespace NLAlib.SparseSketch

open SparseStackSelectors

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The canonical chosen sparsity parameter is positive.
Source: ported from `SparseFockFormal.MainTheoremAssembly`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem canonicalS_pos {d : ℕ} {delta eps : ℝ} (heps : 0 < eps) :
    0 < sparseColumnSparsity (sparseMomentOrder d delta) eps :=
  sparseColumnSparsity_pos heps

/-- The canonical chosen block size is positive.
Source: ported from `SparseFockFormal.MainTheoremAssembly`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem canonicalB_pos {d : ℕ} {delta eps : ℝ}
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    0 < sparseBlockRows d (sparseMomentOrder d delta) eps := by
  have h := two_le_main_sparseBlockRows (d := d) (delta := delta) heps0 heps1
  omega

/-- Every mathematical conclusion asserted in TeX Theorem 1.1 for a fixed
Parseval frame.

Source: ported from `SparseFockFormal.MainTheoremAssembly`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
structure MainConclusions {n d : ℕ} (delta eps : ℝ) (F : Frame n d)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) : Prop where
  operatorFailure :
    (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n
        (canonicalB_pos (d := d) (delta := delta) heps0 heps1)).prob
      {z | eps < ‖gramError F (sparseStackMatrix (toSample z))‖} ≤ delta
  oseSuccess :
    1 - delta ≤
      (sparseStackSelectorLaw (sparseColumnSparsity (sparseMomentOrder d delta) eps)
          (sparseBlockRows d (sparseMomentOrder d delta) eps) n
          (canonicalB_pos (d := d) (delta := delta) heps0 heps1)).prob
        {z | IsSubspaceEmbedding (sparseStackMatrix (toSample z)) (rowMatrix F.u) eps}
  exactColumnSparsity :
    ∀ (z : SparseStackSelectors (sparseColumnSparsity (sparseMomentOrder d delta) eps)
        (sparseBlockRows d (sparseMomentOrder d delta) eps) n) (i : Fin n),
      Fintype.card
        {r : Fin (sparseColumnSparsity (sparseMomentOrder d delta) eps) ×
            Fin (sparseBlockRows d (sparseMomentOrder d delta) eps) //
          sparseStackMatrix (toSample z) r i ≠ 0} =
        sparseColumnSparsity (sparseMomentOrder d delta) eps
  qAtLeastOne : 1 ≤ sparseMomentOrder d delta
  sparsityLower :
    scaleConstant * ((2 * sparseMomentOrder d delta + 1 : ℕ) : ℝ) / eps ≤
      (sparseColumnSparsity (sparseMomentOrder d delta) eps : ℝ)
  rowsLower :
    rowTarget d (sparseMomentOrder d delta) eps ≤
      (sparseRows d (sparseMomentOrder d delta) eps : ℝ)
  sparsityStrict :
    (sparseColumnSparsity (sparseMomentOrder d delta) eps : ℝ) <
      1356 * (sparseMomentOrder d delta : ℝ) / eps
  rowsStrict :
    (sparseRows d (sparseMomentOrder d delta) eps : ℝ) <
      306456 * ((d : ℝ) + sparseMomentOrder d delta) / eps ^ 2
  bAtLeastTwo : 2 ≤ sparseBlockRows d (sparseMomentOrder d delta) eps
  rowsFactor :
    sparseRows d (sparseMomentOrder d delta) eps =
      sparseColumnSparsity (sparseMomentOrder d delta) eps *
        sparseBlockRows d (sparseMomentOrder d delta) eps

/-- All non-operator parts of the main theorem are automatic once the actual
uniform concrete band estimate is supplied.

Source: ported from `SparseFockFormal.MainTheoremAssembly`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem main_conclusions_of_band_bounds
    {n d : ℕ} {delta eps : ℝ}
    (hd : 1 ≤ d) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) (F : Frame n d)
    (hband : ∀ shift nu,
      nu ≤ 2 * sparseMomentOrder d delta →
      ‖normalizedBand (sparseRows d (sparseMomentOrder d delta) eps) F
          (sparseBlockRows d (sparseMomentOrder d delta) eps) shift *
        gradeProjection (d := d) nu‖ ≤
        bandEnvelope d (sparseMomentOrder d delta)
          (sparseRows d (sparseMomentOrder d delta) eps)
          (sparseColumnSparsity (sparseMomentOrder d delta) eps)) :
    MainConclusions delta eps F heps0 heps1 := by
  have hparams := main_parameter_package
    (d := d) (delta := delta) hd heps0 heps1
  rcases hparams with ⟨hsLower, hmLower, hsStrict, hmStrict, hbTwo⟩
  refine
    { operatorFailure :=
        rounded_operator_norm_failure_le_delta_of_band_bounds
          hd hdelta0 hdelta1 heps0 heps1 F hband
      oseSuccess :=
        rounded_success_probability_of_band_bounds
          hd hdelta0 hdelta1 heps0 heps1 F hband
      exactColumnSparsity := ?_
      qAtLeastOne := one_le_sparseMomentOrder d delta
      sparsityLower := hsLower
      rowsLower := hmLower
      sparsityStrict := hsStrict
      rowsStrict := hmStrict
      bAtLeastTwo := hbTwo
      rowsFactor := sparseRows_eq_s_mul_b d (sparseMomentOrder d delta) eps }
  intro z i
  exact card_filter_sparseStackMatrix_ne_zero (toSample z)
    (canonicalS_pos (d := d) (delta := delta) heps0) i

end

end NLAlib.SparseSketch
