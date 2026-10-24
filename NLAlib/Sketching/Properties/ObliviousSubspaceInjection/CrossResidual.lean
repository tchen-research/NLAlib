/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Sketching.Properties.ObliviousSubspaceInjection.Bounds
import NLAlib.Matrix.Measurability.GramPseudoinverse
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Joint rank and cross-residual event for an OSI

The lower embedding and Markov events need no independence. Their two failure bounds of
`1/20` give the joint full-row-rank and cross-residual event with probability at least `9/10`,
with squared Frobenius factor `20/α`. The event is measurable through a rational inverse on
the full-row-rank stratum. Empty numerator dimensions and the zero numerator are included.

Source: Camaño–Epperly–Meyer–Tropp (2025), Lemma 2.1;
`NLA-lib/NLAlib` commit `6a845a2ec27f37c1a98118c107a06a13ce45273d`,
`Regression/Oblivious.lean` (Apache-2.0), adapted to the exact joint native event.
-/

noncomputable section
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {Ω 𝕜 k n s t : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  [Fintype k] [Fintype n] [Fintype s] [Fintype t]
  [DecidableEq k] [DecidableEq n] [DecidableEq s] {d : ℕ}

/-- The exact CEMT cross-residual success event, jointly with full row rank. `S` has the sketch
orientation, so a test matrix `Ω` from the informal statement is passed as `S = Ωᴴ`.
Atlas: `osi-cross-residual-bound`. -/
def osiCrossSuccessEvent (S : Ω → Matrix k n 𝕜) (Q : Matrix n (Fin d) 𝕜)
    (Qperp : Matrix n s 𝕜) (B : Matrix t s 𝕜) (α : ℝ) : Set Ω :=
  {ω | ((S ω * Q)ᴴ).rank = d ∧
    frobSq (B * (S ω * Qperp)ᴴ * moorePenroseInverse ((S ω * Q)ᴴ)) ≤
      (20 / α) * frobSq B}

omit [DecidableEq k] [DecidableEq n] [DecidableEq s] in
/-- The joint full-row-rank and Moore–Penrose cross-residual event is measurable over either
scalar field. On its rank stratum the inverse is exactly the measurable rational `pinvR`. -/
theorem measurableSet_osiCrossSuccessEvent {S : Ω → Matrix k n 𝕜} (hS : Measurable S)
    (Q : Matrix n (Fin d) 𝕜) (Qperp : Matrix n s 𝕜) (B : Matrix t s 𝕜) (α : ℝ) :
    MeasurableSet (osiCrossSuccessEvent S Q Qperp B α) := by
  let X := fun ω => (S ω * Q)ᴴ
  let Z := fun ω => B * (S ω * Qperp)ᴴ
  have hX : Measurable X := Matrix.measurable_conjTranspose.comp (hS.matrix_mul measurable_const)
  have hZ : Measurable Z := measurable_const.matrix_mul
    (Matrix.measurable_conjTranspose.comp (hS.matrix_mul measurable_const))
  have hR : MeasurableSet {ω | (X ω).rank = d} := by
    simpa only [Set.preimage, Set.mem_ofPred_eq, Fintype.card_fin] using
      (measurableSet_setOf_full_row_rank (m := Fin d) (n := k)).preimage hX
  have hF : Measurable (fun ω => frobSq (Z ω * pinvR (X ω))) :=
    measurable_frobSq.comp (hZ.matrix_mul (measurable_pinvR.comp hX))
  have he : osiCrossSuccessEvent S Q Qperp B α =
      {ω | (X ω).rank = d ∧ frobSq (Z ω * pinvR (X ω)) ≤ (20 / α) * frobSq B} := by
    ext ω
    change ((X ω).rank = d ∧ frobSq (Z ω * moorePenroseInverse (X ω)) ≤ (20 / α) * frobSq B) ↔
      ((X ω).rank = d ∧ frobSq (Z ω * pinvR (X ω)) ≤ (20 / α) * frobSq B)
    by_cases hr : (X ω).rank = d
    · rw [moorePenroseInverse_eq_pinvR _
        (isUnit_mul_conjTranspose_of_rank_eq_card _ (by simpa only [Fintype.card_fin] using hr))]
    · simp only [hr, false_and]
  rw [he]
  exact hR.inter (measurableSet_le hF measurable_const)

/-- An OSI satisfies the cross-residual estimate with factor `20/α`, jointly with full row
rank, with probability at least `9/10`. No independence between the numerator and inverse is
required. Orthogonality of `Q` and `Qperp` is allowed but is not needed by the estimate.
Camaño–Epperly–Meyer–Tropp (2025), Lemma 2.1. Atlas: `osi-cross-residual-bound`.
atlas: osi-cross-residual-bound -/
theorem IsObliviousSubspaceInjection.measureReal_osiCrossSuccessEvent_ge
    {S : Ω → Matrix k n 𝕜} {α : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsObliviousSubspaceInjection S d α μ) (hα : 0 < α)
    (Q : Matrix n (Fin d) 𝕜) (hQ : HasOrthonormalCols Q)
    (Qperp : Matrix n s 𝕜) (hQperp : HasOrthonormalCols Qperp) (B : Matrix t s 𝕜) :
    9 / 10 ≤ μ.real (osiCrossSuccessEvent S Q Qperp B α) := by
  let Z := fun ω => B * (S ω * Qperp)ᴴ
  let f := fun ω => frobSq (Z ω)
  have hfe (ω : Ω) : f ω = frobSq (S ω * (Qperp * Bᴴ)) := by
    change frobSq (Z ω) = _
    rw [← frobSq_conjTranspose (Z ω)]
    simp only [Z, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hfI : Integrable f μ :=
    (h.isotropic.integrable_frobSq_mul (Qperp * Bᴴ)).congr
      (ae_of_all μ fun ω => (hfe ω).symm)
  have hfE : ∫ ω, f ω ∂μ = frobSq B := by
    simp_rw [hfe]
    rw [h.isotropic.integral_frobSq_mul,
      frobSq_mul_left_of_orthonormal hQperp.conjTranspose_mul_self,
      frobSq_conjTranspose]
  have hfM : Measurable f :=
    measurable_frobSq.comp (measurable_const.matrix_mul
      (Matrix.measurable_conjTranspose.comp (h.measurable.matrix_mul measurable_const)))
  have hmark : μ.real {ω | 20 * frobSq B < f ω} ≤ 1 / 20 := by
    by_cases hB : B = 0
    · have hz : ∀ ω, f ω = 0 := by simp [f, Z, hB]
      simp only [hB, frobSq_zero, mul_zero, hz, lt_self_iff_false,
        Set.ofPred_false, measureReal_empty]
      norm_num
    · have hb : 0 < frobSq B := lt_of_le_of_ne (frobSq_nonneg B)
        (Ne.symm fun hz => hB ((frobSq_eq_zero_iff B).mp hz))
      have hm := mul_meas_ge_le_integral_of_nonneg
        (ae_of_all μ fun ω => frobSq_nonneg (Z ω)) hfI (20 * frobSq B)
      rw [hfE] at hm
      calc
        μ.real {ω | 20 * frobSq B < f ω} ≤ μ.real {ω | 20 * frobSq B ≤ f ω} :=
          measureReal_mono fun ω hω => by
            change 20 * frobSq B < f ω at hω
            change 20 * frobSq B ≤ f ω
            exact hω.le
        _ ≤ frobSq B / (20 * frobSq B) :=
          (le_div_iff₀ (mul_pos (by norm_num) hb)).mpr (by simpa only [mul_comm] using hm)
        _ = 1 / 20 := by field_simp [hb.ne']
  let bad := {ω | ¬ IsSubspaceInjection (S ω) Q α} ∪ {ω | 20 * frobSq B < f ω}
  have hbadM : MeasurableSet bad :=
    (measurableSet_isSubspaceInjection h.measurable Q α).compl.union
      (measurableSet_lt measurable_const hfM)
  have hbad : μ.real bad ≤ 1 / 10 := by
    calc
      μ.real bad ≤ μ.real {ω | ¬ IsSubspaceInjection (S ω) Q α} +
          μ.real {ω | 20 * frobSq B < f ω} := measureReal_union_le _ _
      _ ≤ 1 / 20 + 1 / 20 := add_le_add (h.injection Q hQ) hmark
      _ = 1 / 10 := by norm_num
  have hgood : 9 / 10 ≤ μ.real badᶜ := by
    rw [measureReal_compl hbadM, probReal_univ]
    linarith
  refine hgood.trans (measureReal_mono ?_)
  intro ω hω
  change ¬((¬IsSubspaceInjection (S ω) Q α) ∨ 20 * frobSq B < f ω) at hω
  change ((S ω * Q)ᴴ).rank = d ∧
    frobSq (Z ω * moorePenroseInverse ((S ω * Q)ᴴ)) ≤ (20 / α) * frobSq B
  have hinj : IsSubspaceInjection (S ω) Q α := by
    by_contra hnot
    exact hω (Or.inl hnot)
  have hf : f ω ≤ 20 * frobSq B := not_lt.mp fun hnot => hω (Or.inr hnot)
  refine ⟨?_, ?_⟩
  · simpa only [Fintype.card_fin] using hinj.rank_conjTranspose_mul_eq_card hQ hα
  · calc
      frobSq (Z ω * moorePenroseInverse ((S ω * Q)ᴴ)) ≤ frobSq (Z ω) / α :=
        hinj.frobSq_mul_moorePenroseInverse_conjTranspose_le hQ hα (Z ω)
      _ ≤ (20 * frobSq B) / α := div_le_div_of_nonneg_right hf hα.le
      _ = (20 / α) * frobSq B := by ring

end NLAlib
