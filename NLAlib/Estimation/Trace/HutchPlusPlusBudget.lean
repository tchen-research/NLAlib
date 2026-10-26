import NLAlib.Estimation.Trace.HutchPlusPlusTail

/-!
# Explicit Hutch++ sample budgets

The Gaussian range blocks and residual probes have independently chosen widths.
The total budget is twice the range width plus the residual width. Constants are
deliberately loose. Source: the supplied estimation derivations, §1.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace NLAlib

/-- Positive target rank for relative accuracy `ε > 0`. -/
def hutchPlusPlusRank (ε : ℝ) : ℕ := ⌈1 / ε⌉₊

/-- Number of independent Gaussian range blocks for failure `δ`. -/
def hutchPlusPlusBlocks (δ : ℝ) : ℕ := ⌈log (2 / δ) / log 4⌉₊

/-- Number of independent Gaussian residual probes. -/
def hutchPlusPlusProbes (ε δ : ℝ) : ℕ := ⌈2048 * exp 1 ^ 2 / ε * log (4 / δ)⌉₊

/-- Scalar matrix-vector budget: two products per range-sketch column and one per probe. -/
def hutchPlusPlusQueryBudget (ε δ : ℝ) : ℕ :=
  2 * (hutchPlusPlusBlocks δ * (2 * hutchPlusPlusRank ε + 1)) + hutchPlusPlusProbes ε δ

/-- The explicit rank is positive and satisfies `ε k ≥ 1`. -/
theorem hutchPlusPlusRank_pos_and_one_le_mul {ε : ℝ} (hε : 0 < ε) :
    0 < hutchPlusPlusRank ε ∧ 1 ≤ ε * hutchPlusPlusRank ε := by
  have h := Nat.le_ceil (1 / ε)
  refine ⟨Nat.ceil_pos.mpr (by positivity), ?_⟩
  have hh := (div_le_iff₀ hε).mp h
  simpa [hutchPlusPlusRank, mul_comm] using hh

/-- The amplified range failure under the explicit block budget is at most `δ/2`. -/
theorem pow_quarter_hutchPlusPlusBlocks_le {δ : ℝ} (hδ : 0 < δ) :
    (1 / 4 : ℝ) ^ hutchPlusPlusBlocks δ ≤ δ / 2 := by
  have h4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have hL := (div_le_iff₀ h4).mp (Nat.le_ceil (log (2 / δ) / log 4))
  have he : (1 / 4 : ℝ) ^ hutchPlusPlusBlocks δ =
      exp (-((hutchPlusPlusBlocks δ : ℝ) * log 4)) := by
    rw [neg_mul_eq_mul_neg, exp_nat_mul, exp_neg, exp_log (by norm_num : (0 : ℝ) < 4)]
    simp only [one_div]
  rw [he]
  calc
    _ ≤ exp (-log (2 / δ)) := exp_le_exp.mpr (neg_le_neg hL)
    _ = δ / 2 := by rw [exp_neg, exp_log (by positivity)]; field_simp

/-- The explicit residual width is positive and makes its failure at most `δ/2`. -/
theorem hutchPlusPlusProbes_pos_and_tail_le {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < hutchPlusPlusProbes ε δ ∧
      2 * exp (-((hutchPlusPlusProbes ε δ : ℝ) * ε / (2048 * exp 1 ^ 2))) ≤ δ / 2 := by
  have hl : 0 < log (4 / δ) := log_pos ((one_lt_div hδ).2 (by linarith))
  have hc : 0 < 2048 * exp 1 ^ 2 / ε * log (4 / δ) := by positivity
  refine ⟨Nat.ceil_pos.mpr hc, ?_⟩
  have hr := Nat.le_ceil (2048 * exp 1 ^ 2 / ε * log (4 / δ))
  have hC : 0 < 2048 * exp 1 ^ 2 := by positivity
  have hrl : log (4 / δ) ≤ hutchPlusPlusProbes ε δ * ε / (2048 * exp 1 ^ 2) := by
    apply (le_div_iff₀ hC).2
    have hh := mul_le_mul_of_nonneg_right hr hε.le
    dsimp only [hutchPlusPlusProbes]
    convert hh using 1
    field_simp
  calc
    _ ≤ 2 * exp (-log (4 / δ)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hrl)) (by norm_num)
    _ = δ / 2 := by rw [exp_neg, exp_log (by positivity)]; field_simp; ring

/-- With the explicit widths, the native Gaussian Hutch++ estimate has relative error
at most `ε` outside an event of probability at most `δ`.
Zero input, rank deficiency, empty matrices and oversized sketch ranks are included.
atlas: hutchpp (partial) -/
theorem measureReal_abs_hutchPlusPlusEstimate_sub_trace_gt_le_of_budget
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    {S : Ω → Matrix (Fin n)
      (Fin (hutchPlusPlusBlocks δ) × Fin (2 * hutchPlusPlusRank ε + 1)) ℝ}
    {Z : Ω → Matrix (Fin n) (Fin (hutchPlusPlusProbes ε δ)) ℝ}
    (hS : HasLaw S (gaussianMatrix (Fin n)
      (Fin (hutchPlusPlusBlocks δ) × Fin (2 * hutchPlusPlusRank ε + 1))) μ)
    (hZ : HasLaw Z (gaussianMatrix (Fin n) (Fin (hutchPlusPlusProbes ε δ))) μ)
    (hind : IndepFun Z S μ) :
    μ.real {ω | ε * A.trace < |hutchPlusPlusEstimate A (S ω) (Z ω) - A.trace|} ≤ δ := by
  obtain ⟨hk, hkε⟩ := hutchPlusPlusRank_pos_and_one_le_mul hε
  obtain ⟨hr, hrt⟩ := hutchPlusPlusProbes_pos_and_tail_le hε hδ hδ1
  have h := measureReal_abs_hutchPlusPlusEstimate_sub_trace_gt_le hA hk hr hε hε1 hkε hS hZ hind
  have hL := pow_quarter_hutchPlusPlusBlocks_le hδ
  linarith

/-- An explicit `ε⁻¹` times logarithmic failure budget, with every rounding term included.
The right-hand coefficient is affine in `log(1/δ)` by the logarithm quotient identities.
atlas: hutchpp (partial) -/
theorem hutchPlusPlusQueryBudget_le {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (hutchPlusPlusQueryBudget ε δ : ℝ) ≤
      (10 * (log (2 / δ) / log 4 + 1) + 2048 * exp 1 ^ 2 * log (4 / δ) + 1) / ε := by
  have hk : (hutchPlusPlusRank ε : ℝ) ≤ 2 / ε := by
    have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / ε)).le
    dsimp only [hutchPlusPlusRank]
    have he : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).2 (by simpa using hε1)
    simp only [div_eq_mul_inv, one_mul] at hh he ⊢
    linarith
  have hl : 0 ≤ log (2 / δ) / log 4 := by
    apply div_nonneg
    · exact (log_pos ((one_lt_div hδ).2 (by linarith))).le
    · exact (log_pos (by norm_num : (1 : ℝ) < 4)).le
  have hL : (hutchPlusPlusBlocks δ : ℝ) ≤ log (2 / δ) / log 4 + 1 :=
    (Nat.ceil_lt_add_one hl).le
  have hr : (hutchPlusPlusProbes ε δ : ℝ) ≤ 2048 * exp 1 ^ 2 / ε * log (4 / δ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by positivity)
      (log_pos ((one_lt_div hδ).2 (by linarith))).le)).le
  have hw : 2 * (hutchPlusPlusRank ε : ℝ) + 1 ≤ 5 / ε := by
    have he : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).2 (by simpa using hε1)
    simp only [div_eq_mul_inv, one_mul] at hk he ⊢
    linarith
  have hprod := mul_le_mul hL hw (by positivity) (by linarith : 0 ≤ log (2 / δ) / log 4 + 1)
  unfold hutchPlusPlusQueryBudget
  push_cast
  have he : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).2 (by simpa using hε1)
  simp only [div_eq_mul_inv, one_mul] at hr hprod he ⊢
  nlinarith

/-- A universal constant bounds the actual query budget by
`C ε⁻¹ (1 + log(1/δ))`, independently of the matrix dimension.
atlas: hutchpp (partial) -/
theorem exists_hutchPlusPlusQueryBudget_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
      (hutchPlusPlusQueryBudget ε δ : ℝ) ≤ C / ε * (1 + log (1 / δ)) := by
  let a : ℝ := 10 / log 4 + 2048 * exp 1 ^ 2
  let b : ℝ := 10 * log 2 / log 4 + 11 + 2048 * exp 1 ^ 2 * log 4
  have hl4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨a + b, add_pos ha hb, ?_⟩
  intro ε δ hε hε1 hδ hδ1
  have hx : 0 ≤ log (1 / δ) := (log_pos ((one_lt_div hδ).2 hδ1)).le
  have h2 : log (2 / δ) = log 2 + log (1 / δ) := by
    rw [log_div (by norm_num) hδ.ne', log_div one_ne_zero hδ.ne', log_one, zero_sub]
    ring
  have h4 : log (4 / δ) = log 4 + log (1 / δ) := by
    rw [log_div (by norm_num) hδ.ne', log_div one_ne_zero hδ.ne', log_one, zero_sub]
    ring
  apply (hutchPlusPlusQueryBudget_le hε hε1 hδ hδ1).trans
  rw [h2, h4]
  have he : 10 * ((log 2 + log (1 / δ)) / log 4 + 1) +
      2048 * exp 1 ^ 2 * (log 4 + log (1 / δ)) + 1 = a * log (1 / δ) + b := by
    dsimp [a, b]
    ring
  rw [he, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hε.le
  nlinarith [mul_nonneg hb.le hx]

end NLAlib
