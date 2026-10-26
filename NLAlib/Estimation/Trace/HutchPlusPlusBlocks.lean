import NLAlib.Estimation.Trace.HutchPlusPlusRange
import NLAlib.RandomMatrix.Gaussian.Basic.ColumnBlocks

/-!
# Amplification by concatenated Gaussian range blocks

The range of the full sketch contains each block range. Consequently failure of the
full range approximation implies failure of every independent block. This is one
Hutch++ estimator with a wider Gaussian sketch, not a median of several estimators.
Source: the block amplification route in the supplied estimation derivations, §1.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-- The range error of a concatenated sketch is no greater than the error of any block. -/
theorem frobSq_sub_rangeProjector_mul_le_columnBlock {n b t : Type*}
    [Fintype n] [Fintype b] [Fintype t] [DecidableEq n]
    (A : Matrix n n ℝ) (S : Matrix n (b × t) ℝ) (a : b) :
    frobSq ((1 - rangeProjector (A * S)) * A) ≤
      frobSq ((1 - rangeProjector (A * Matrix.of (fun i j => S i (a, j)))) * A) := by
  have hfix : rangeProjector (A * S) * (A * Matrix.of (fun i j => S i (a, j))) =
      A * Matrix.of (fun i j => S i (a, j)) := by
    ext i j
    exact congrArg (fun M => M i (a, j)) (rangeProjector_mul (A * S))
  simpa only [Matrix.sub_mul, Matrix.one_mul] using
    frobSq_sub_rangeProjector_mul_le_of_mul_eq hfix A

/-- Concatenating `L` independent Gaussian range blocks gives failure at most `4⁻ᴸ`.
The block laws and independence are derived from the actual Gaussian matrix law.
The estimate includes empty input matrices and a zero trace. -/
theorem measureReal_frobSq_hutchPlusPlusResidual_gt_le_pow_quarter
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n k L : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hk : 0 < k)
    {S : Ω → Matrix (Fin n) (Fin L × Fin (2 * k + 1)) ℝ}
    (hS : HasLaw S (gaussianMatrix (Fin n) (Fin L × Fin (2 * k + 1))) μ) :
    μ.real {ω | 8 * A.trace ^ 2 / k < frobSq (hutchPlusPlusResidual A (S ω))} ≤
      (1 / 4 : ℝ) ^ L := by
  let : IsProbabilityMeasure μ := hS.isProbabilityMeasure
  let B : Fin L → Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ :=
    fun a ω => Matrix.of fun i j => S ω i (a, j)
  let E : Set (Matrix (Fin n) (Fin (2 * k + 1)) ℝ) :=
    {G | 8 * A.trace ^ 2 / k < frobSq ((1 - rangeProjector (A * G)) * A)}
  have hE : MeasurableSet E := by
    have hP := measurable_rangeProjector.comp
      (measurable_const.matrix_mul measurable_id :
        Measurable fun G : Matrix (Fin n) (Fin (2 * k + 1)) ℝ => A * G)
    have hF : Measurable (fun G : Matrix (Fin n) (Fin (2 * k + 1)) ℝ =>
        frobSq ((1 - rangeProjector (A * G)) * A)) :=
      measurable_frobSq.comp (by
        apply Matrix.measurable_iff_entries.mpr
        have hp := Matrix.measurable_iff_entries.mp hP
        intro i j
        simp only [Matrix.mul_apply, Matrix.sub_apply]
        fun_prop)
    exact measurableSet_lt measurable_const hF
  have hind := iIndepFun_gaussianMatrix_columnBlocks hS
  have hsingle (a : Fin L) : μ (B a ⁻¹' E) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
    have h := measureReal_frobSq_sub_rangeProjector_mul_gt_le_quarter hA hk
      (hasLaw_gaussianMatrix_columnBlock hS a)
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (B a ⁻¹' E))]
    exact ENNReal.ofReal_le_ofReal h
  have hsub : {ω | 8 * A.trace ^ 2 / k < frobSq (hutchPlusPlusResidual A (S ω))} ⊆
      ⋂ a, B a ⁻¹' E := by
    intro ω hω
    apply Set.mem_iInter.mpr
    intro a
    exact hω.trans_le ((frobSq_hutchPlusPlusResidual_le A (S ω)).trans
      (frobSq_sub_rangeProjector_mul_le_columnBlock A (S ω) a))
  have hbound : μ {ω | 8 * A.trace ^ 2 / k < frobSq (hutchPlusPlusResidual A (S ω))} ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ L) := by
    calc
      _ ≤ μ (⋂ a, B a ⁻¹' E) := measure_mono hsub
      _ = ∏ a, μ (B a ⁻¹' E) := hind.meas_iInter (fun _ => ⟨E, hE, rfl⟩)
      _ ≤ ∏ _a : Fin L, ENNReal.ofReal (1 / 4 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => zero_le) (fun a _ => hsingle a)
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound

end NLAlib
