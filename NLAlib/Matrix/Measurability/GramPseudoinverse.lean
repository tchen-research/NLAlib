/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.ForMathlib.MeasureTheory.Matrix
import NLAlib.Matrix.Basic.Pseudoinverse
import NLAlib.Matrix.Basic.TikhonovLimit
import NLAlib.Matrix.Subspaces.RangeProjector
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Measurability of matrix pseudoinverses and range projectors

The ordinary total matrix inverse, and consequently `pinvL` and `pinvR`, are Borel measurable
over both real and complex matrices. This is the guarded full-rank formula used in the OSI
success event. The native Tikhonov limit additionally gives measurability of the full
Moore–Penrose inverse and range projector at every rank, without choosing singular vectors.
Source: determinant/adjugate identity; Camaño–Epperly–Meyer–Tropp (2025), Lemma 2.1.
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

/-- The total determinant/adjugate inverse is measurable over real or complex matrices,
including its zero value on singular matrices. -/
theorem measurable_matrix_inv [DecidableEq n] :
    Measurable (fun A : Matrix n n 𝕜 => A⁻¹) := by
  refine Matrix.measurable_iff_entries.mpr fun i j => ?_
  have hdet : Measurable fun A : Matrix n n 𝕜 => A.det :=
    continuous_id.matrix_det.measurable
  have hadj : Measurable fun A : Matrix n n 𝕜 => A.adjugate i j :=
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hdet.inv.mul hadj

/-- The right Gram pseudoinverse formula is measurable over both scalar fields.
It agrees with the Moore–Penrose inverse whenever the row rank is full. -/
theorem measurable_pinvR [DecidableEq m] : Measurable (pinvR : Matrix m n 𝕜 → Matrix n m 𝕜) := by
  unfold pinvR
  exact Matrix.measurable_conjTranspose.matrix_mul
    (measurable_matrix_inv.comp (measurable_id.matrix_mul Matrix.measurable_conjTranspose))

/-- The left Gram pseudoinverse formula is measurable over both scalar fields. -/
theorem measurable_pinvL [DecidableEq n] : Measurable (pinvL : Matrix m n 𝕜 → Matrix n m 𝕜) := by
  unfold pinvL
  exact (measurable_matrix_inv.comp
    (Matrix.measurable_conjTranspose.matrix_mul measurable_id)).matrix_mul
      Matrix.measurable_conjTranspose

/-- The squared Frobenius norm is measurable over real or complex matrices. -/
theorem measurable_frobSq : Measurable (frobSq : Matrix m n 𝕜 → ℝ) := by
  change Measurable (fun A : Matrix m n 𝕜 => frobSq A)
  simp only [frobSq_eq_sum_norm_sq]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((Matrix.measurable_entry i j).norm).pow_const 2

private theorem rank_eq_card_iff_isUnit_rowGram [DecidableEq m] (A : Matrix m n 𝕜) :
    A.rank = Fintype.card m ↔ IsUnit (A * Aᴴ) := by
  refine ⟨isUnit_mul_conjTranspose_of_rank_eq_card A, fun h => ?_⟩
  apply le_antisymm A.rank_le_card_height
  calc
    Fintype.card m = (A * Aᴴ).rank := (Matrix.rank_of_isUnit _ h).symm
    _ ≤ A.rank := Matrix.rank_mul_le_left _ _

/-- The full-row-rank stratum is measurable, through the determinant of the row Gram matrix.
This makes rank-guarded Moore–Penrose success events measurable without selecting an SVD. -/
theorem measurableSet_setOf_full_row_rank [DecidableEq m] :
    MeasurableSet {A : Matrix m n 𝕜 | A.rank = Fintype.card m} := by
  have he : {A : Matrix m n 𝕜 | A.rank = Fintype.card m} =
      {A : Matrix m n 𝕜 | (A * Aᴴ).det ≠ 0} := by
    ext A
    change (A.rank = Fintype.card m) ↔ (A * Aᴴ).det ≠ 0
    rw [rank_eq_card_iff_isUnit_rowGram, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [he]
  exact (measurableSet_eq_fun
    (continuous_id.matrix_mul continuous_id.matrix_conjTranspose).matrix_det.measurable
    measurable_const).compl

/-- The full Moore–Penrose inverse is measurable at every rank: it is the pointwise limit of
measurable positive Tikhonov regularizations. No measurable singular-vector selector is used. -/
theorem measurable_moorePenroseInverse [DecidableEq m] [DecidableEq n] :
    Measurable (moorePenroseInverse : Matrix m n 𝕜 → Matrix n m 𝕜) := by
  let β := fun j : ℕ => 1 / ((j : ℝ) + 1)
  have hβ : Filter.Tendsto β Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun j => ?_⟩
    change 0 < 1 / ((j : ℝ) + 1)
    positivity
  have hm (j : ℕ) : Measurable (fun A : Matrix m n 𝕜 => tikhonovInverse A (β j)) := by
    have hc : Continuous (fun A : Matrix m n 𝕜 => tikhonovNormal A (β j)) := by
      unfold tikhonovNormal
      fun_prop
    change Measurable (fun A : Matrix m n 𝕜 => (tikhonovNormal A (β j))⁻¹ * Aᴴ)
    exact (measurable_matrix_inv.comp hc.measurable).matrix_mul Matrix.measurable_conjTranspose
  refine Matrix.measurable_iff_entries.mpr fun i j => ?_
  exact measurable_of_tendsto_metrizable
    (fun l => (Matrix.measurable_entry i j).comp (hm l))
    (tendsto_pi_nhds.mpr fun A => (continuous_apply_apply i j).continuousAt.tendsto.comp
      ((tendsto_tikhonovInverse_zero A).comp hβ))

/-- The actual range projector is a measurable function of a real or complex matrix at every
rank, as a product of the input with its measurable Moore–Penrose inverse. -/
theorem measurable_rangeProjector [DecidableEq m] [DecidableEq n] :
    Measurable (rangeProjector : Matrix m n 𝕜 → Matrix m m 𝕜) := by
  change Measurable (fun A : Matrix m n 𝕜 => A * moorePenroseInverse A)
  exact measurable_id.matrix_mul measurable_moorePenroseInverse

end NLAlib
