import NLAlib.Sketching.Structured.KhatriRaoEmbedding
import NLAlib.Sketching.Structured.KhatriRaoUpper
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Fixed-parameter rank growth of Khatri--Rao embedding budgets

The full accuracy/confidence budget is bounded by a fixed multiple of
`r (1 + log r)^(d-1)` when tensor order, accuracy and confidence are fixed.
The constants depend only on those parameters and the factor law budget.
Source: Heidary, Theorem `core:thm:ose`.
https://github.com/DiarHaidary/Results/blob/main/manuscripts/08-Khatri-Rao-Embeddings-and-Approximation/Khatri_Rao_Embeddings_and_Approximation_Focused.pdf
-/

noncomputable section

open MeasureTheory Matrix
open scoped Matrix

namespace NLAlib

/-- An explicit constant converting the full embedding budget into its
fixed-accuracy, fixed-confidence rank growth. -/
def khatriRaoFixedParameterConstant (d : ℕ) (C ε δ : ℝ) : ℝ :=
  C * ((1 + Real.log (4 / δ)) / ε ^ 2 +
    ((1 + Real.log (4 / δ)) ^ (d - 1) + (1 + Real.log (4 / δ)) ^ d) / ε)

/-- The fixed-parameter sampling constant is positive at positive
accuracy and a confidence parameter strictly between zero and one.
atlas: khatri-rao-sharp-growth (partial) -/
theorem khatriRaoFixedParameterConstant_pos (d : ℕ) {C ε δ : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < khatriRaoFixedParameterConstant d C ε δ := by
  have hdiv : 1 ≤ (4 : ℝ) / δ := (le_div_iff₀ hδ).2 (by linarith)
  have hL : 0 < 1 + Real.log (4 / δ) := by linarith [Real.log_nonneg hdiv]
  unfold khatriRaoFixedParameterConstant
  positivity

/-- The logarithmic budget has the sharp rank growth at every fixed
accuracy and confidence. This estimate is uniform over real ranks `r≥1`.
atlas: khatri-rao-sharp-growth (partial) -/
theorem khatriRao_budget_le_fixedParameterConstant_mul_rank_log_pow
    {d : ℕ} (hd : 2 ≤ d) {C r ε δ : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    C * (r * Real.log (4 * r / δ) / ε ^ 2 +
      (r * Real.log (4 * r / δ) ^ (d - 1) + Real.log (4 * r / δ) ^ d) / ε) ≤
      khatriRaoFixedParameterConstant d C ε δ * r * (1 + Real.log r) ^ (d - 1) := by
  let L := 1 + Real.log (4 / δ)
  let l := 1 + Real.log r
  let t := Real.log (4 * r / δ)
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hl1 : 1 ≤ l := by dsimp [l]; linarith [Real.log_nonneg hr]
  have hL1 : 1 ≤ L := by
    have hdiv : 1 ≤ (4 : ℝ) / δ := (le_div_iff₀ hδ).2 (by linarith)
    dsimp [L]
    linarith [Real.log_nonneg hdiv]
  have htl : t = l + L - 2 := by
    dsimp [t, l, L]
    rw [show 4 * r / δ = r * (4 / δ) by ring,
      Real.log_mul hr0.ne' (ne_of_gt (div_pos (by norm_num) hδ))]
    ring
  have ht0 : 0 ≤ t := by rw [htl]; linarith
  have ht : t ≤ L * l := by
    rw [htl]
    nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (sub_nonneg.mpr hl1)]
  have hlr : l ≤ r := by
    dsimp [l]
    linarith [Real.log_le_sub_one_of_pos hr0]
  have hlpow : l ≤ l ^ (d - 1) := by
    have h := pow_le_pow_right₀ hl1 (show 1 ≤ d - 1 by omega)
    simpa only [pow_one] using h
  have h1 : r * t ≤ L * r * l ^ (d - 1) := by
    calc
      _ ≤ r * (L * l) := mul_le_mul_of_nonneg_left ht hr0.le
      _ ≤ r * (L * l ^ (d - 1)) := by gcongr
      _ = _ := by ring
  have h2 : r * t ^ (d - 1) ≤ L ^ (d - 1) * r * l ^ (d - 1) := by
    calc
      _ ≤ r * (L * l) ^ (d - 1) := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have h3 : t ^ d ≤ L ^ d * r * l ^ (d - 1) := by
    calc
      _ ≤ (L * l) ^ d := pow_le_pow_left₀ ht0 ht d
      _ = L ^ d * l ^ (d - 1) * l := by
        have he : l ^ d = l ^ (d - 1) * l := by
          conv_lhs => rw [show d = (d - 1) + 1 by omega]
          rw [pow_succ]
        rw [mul_pow, he]
        ring
      _ ≤ L ^ d * l ^ (d - 1) * r := by gcongr
      _ = _ := by ring
  change C * (r * t / ε ^ 2 + (r * t ^ (d - 1) + t ^ d) / ε) ≤ _
  calc
    _ ≤ C * (L * r * l ^ (d - 1) / ε ^ 2 +
        (L ^ (d - 1) * r * l ^ (d - 1) + L ^ d * r * l ^ (d - 1)) / ε) := by gcongr
    _ = _ := by dsimp [khatriRaoFixedParameterConstant, L, l]; ring

/-- At fixed factor parameter, accuracy and confidence, a constant times
`r log(er)^(d-1)` rows suffices under the actual independent factor law.
The constant is explicit and independent of rank and mode dimensions.
Source: Heidary, Theorem `core:thm:ose`.
atlas: khatri-rao-sharp-growth (partial) -/
theorem measureReal_not_isSubspaceEmbedding_khatriRaoSketch_le_of_rank_log_budget
    {d r m : ℕ} {n : Fin d → ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (ν : ∀ j : Fin d, MeasureTheory.Measure (Fin (n j) → ℝ))
    [∀ j, MeasureTheory.IsProbabilityMeasure (ν j)] {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ j (u : Fin (n j) → ℝ), ‖WithLp.toLp 2 u‖ = 1 →
      ∫⁻ g, ENNReal.ofReal (Real.exp ((u ⬝ᵥ g / K) ^ 2)) ∂ν j ≤ 2)
    (hsecond : ∀ j (a b : Fin (n j)),
      ∫ g, g a * g b ∂ν j = if a = b then 1 else 0)
    (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ) (hU : HasOrthonormalCols U)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbudget : khatriRaoFixedParameterConstant d (khatriRaoSharpEmbeddingConstant d K) ε δ *
      r * (1 + Real.log r) ^ (d - 1) ≤ m) :
    (khatriRaoSampleLaw ν m).real
      {g | ¬ IsSubspaceEmbedding (khatriRaoSketch g) U ε} ≤ δ := by
  apply measureReal_not_isSubspaceEmbedding_khatriRaoSketch_le hd hr hm ν hK
    hpsi hsecond U hU hε hδ hδ1.le
  have hC : 0 ≤ khatriRaoSharpEmbeddingConstant d K := by
    unfold khatriRaoSharpEmbeddingConstant khatriRaoEmbeddingConstant
    positivity
  exact (khatriRao_budget_le_fixedParameterConstant_mul_rank_log_pow hd hC
    (by exact_mod_cast hr) hε hδ hδ1).trans hbudget

end NLAlib
