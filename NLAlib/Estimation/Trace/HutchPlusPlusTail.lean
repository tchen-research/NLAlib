import NLAlib.Estimation.Trace.HutchPlusPlusBlocks
import NLAlib.Estimation.Trace.HutchinsonTail
import NLAlib.ForMathlib.Probability.IndependentTail

/-!
# The relative-error tail of the native Hutch++ estimator

The concatenated Gaussian range sketch and the independent Gaussian residual probes
give an explicit relative tail. No approximation or concentration event is supplied
as a hypothesis. Source: Meyer et al. (2021), Algorithm 1 and Theorem 1; the block
amplification proof in the supplied estimation derivations, §1.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped Matrix
namespace NLAlib

variable {Ω n r : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
  [Fintype r] {μ : Measure Ω}

open scoped Matrix.Norms.L2Operator in
/-- The Gaussian Hutchinson tail for a residual with a trace-scaled Frobenius bound.
The zero residual has an empty strict-error event. -/
theorem measureReal_abs_hutchinsonEstimate_sub_trace_gt_le_of_frobSq_le
    [Nonempty r] (C : Matrix n n ℝ) {Z : Ω → Matrix n r ℝ}
    (hZ : HasLaw Z (gaussianMatrix n r) μ) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : frobSq C ≤ 8 * ε * T ^ 2) :
    μ.real {ω | ε * T < |hutchinsonEstimate C (Z ω) - C.trace|} ≤
      2 * exp (-(Fintype.card r * ε / (2048 * exp 1 ^ 2))) := by
  classical
  let : IsProbabilityMeasure μ := hZ.isProbabilityMeasure
  by_cases hC0 : C = 0
  · subst C
    have hempty : {ω | ε * T < |hutchinsonEstimate (0 : Matrix n n ℝ) (Z ω) -
        (0 : Matrix n n ℝ).trace|} = ∅ := by
      ext ω
      simp [hutchinsonEstimate, quadForm, not_lt.mpr (mul_nonneg hε.le hT)]
    rw [hempty, measureReal_empty]
    positivity
  have hF : 0 < frobNorm C := lt_of_le_of_ne (frobNorm_nonneg C)
    (Ne.symm fun h => hC0 ((frobNorm_eq_zero_iff C).1 h))
  have hN : 0 < specNorm C := by
    simpa only [specNorm_eq_norm] using norm_pos_iff.mpr hC0
  have hTs : 0 < T := by
    have hf := frobNorm_sq C
    nlinarith
  have hbound : specNorm C ≤ 8 * T := by
    have hs := specNorm_le_frobNorm C
    have hfs := frobNorm_sq C
    nlinarith [mul_le_mul_of_nonneg_right hε1 (sq_nonneg T)]
  have hfirst : (Fintype.card r : ℝ) * ε / 8 ≤
      Fintype.card r * (ε * T) ^ 2 / frobNorm C ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hF)).2
    rw [frobNorm_sq]
    have h := mul_le_mul_of_nonneg_left hC
      (show 0 ≤ (Fintype.card r : ℝ) * ε / 8 by positivity)
    nlinarith
  have hsecond : (Fintype.card r : ℝ) * ε / 8 ≤
      Fintype.card r * (ε * T) / specNorm C := by
    apply (le_div_iff₀ hN).2
    have h := mul_le_mul_of_nonneg_left hbound
      (show 0 ≤ (Fintype.card r : ℝ) * ε / 8 by positivity)
    nlinarith
  have ht := measureReal_le_abs_hutchinsonEstimate_sub_trace_le_of_hasLaw_gaussianMatrix
    C hZ (ε * T) (mul_nonneg hε.le hT)
  apply (measureReal_mono (show {ω | ε * T < |hutchinsonEstimate C (Z ω) - C.trace|} ⊆
    {ω | ε * T ≤ |hutchinsonEstimate C (Z ω) - C.trace|} from
    fun ω h => show ε * T ≤ _ from le_of_lt h)).trans
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply exp_le_exp.mpr
  have hmin := le_min hfirst hsecond
  have hpos : 0 < (1 / (256 * exp 1 ^ 2) : ℝ) := by positivity
  calc
    _ ≤ -(1 / (256 * exp 1 ^ 2)) * (Fintype.card r * ε / 8) :=
      mul_le_mul_of_nonpos_left hmin (neg_nonpos.mpr hpos.le)
    _ = _ := by ring

/-- The actual independent Gaussian Hutch++ estimator has an explicit relative tail.
Concatenating `L` range blocks of width `2k+1` yields the first failure term; the residual
probes yield the second. Constants are explicit and nonoptimal.
atlas: hutchpp (partial) -/
theorem measureReal_abs_hutchPlusPlusEstimate_sub_trace_gt_le
    {n k L r : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (hk : 0 < k) (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hkε : (1 : ℝ) ≤ ε * k)
    {S : Ω → Matrix (Fin n) (Fin L × Fin (2 * k + 1)) ℝ}
    {Z : Ω → Matrix (Fin n) (Fin r) ℝ}
    (hS : HasLaw S (gaussianMatrix (Fin n) (Fin L × Fin (2 * k + 1))) μ)
    (hZ : HasLaw Z (gaussianMatrix (Fin n) (Fin r)) μ) (hind : IndepFun Z S μ) :
    μ.real {ω | ε * A.trace < |hutchPlusPlusEstimate A (S ω) (Z ω) - A.trace|} ≤
      2 * exp (-((r : ℝ) * ε / (2048 * exp 1 ^ 2))) + (1 / 4 : ℝ) ^ L := by
  let : IsProbabilityMeasure μ := hS.isProbabilityMeasure
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let E : Set (Matrix (Fin n) (Fin r) ℝ ×
      Matrix (Fin n) (Fin L × Fin (2 * k + 1)) ℝ) :=
    {p | ε * A.trace < |hutchPlusPlusEstimate A p.2 p.1 - A.trace|}
  let G : Set (Matrix (Fin n) (Fin L × Fin (2 * k + 1)) ℝ) :=
    {S | frobSq (hutchPlusPlusResidual A S) ≤ 8 * A.trace ^ 2 / k}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (((measurable_hutchPlusPlusEstimate A).comp measurable_swap).sub measurable_const).abs
  have hG : MeasurableSet G := measurableSet_le
    (measurable_frobSq.comp (measurable_hutchPlusPlusResidual A)) measurable_const
  apply hind.measureReal_mem_le_add hZ.aemeasurable hS.aemeasurable hE hG (by positivity)
  · intro S hgood
    have hc : frobSq (hutchPlusPlusResidual A S) ≤ 8 * ε * A.trace ^ 2 := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hdiv : (1 : ℝ) / k ≤ ε := (div_le_iff₀ hkR).2 hkε
      change frobSq (hutchPlusPlusResidual A S) ≤ 8 * A.trace ^ 2 / k at hgood
      have hh := mul_le_mul_of_nonneg_left hdiv
        (show 0 ≤ 8 * A.trace ^ 2 by positivity)
      exact hgood.trans (by simpa only [div_eq_mul_inv, one_mul, mul_assoc,
        mul_left_comm, mul_comm] using hh)
    have ht := measureReal_abs_hutchinsonEstimate_sub_trace_gt_le_of_frobSq_le
      (hutchPlusPlusResidual A S) hZ (Matrix.PosSemidef.trace_nonneg hA) hε hε1 hc
    simpa only [E, Set.mem_ofPred_eq, hutchPlusPlusEstimate_sub_trace, Fintype.card_fin] using ht
  · simpa only [G, Set.mem_ofPred_eq, not_le] using
      measureReal_frobSq_hutchPlusPlusResidual_gt_le_pow_quarter hA hk hS

end NLAlib
