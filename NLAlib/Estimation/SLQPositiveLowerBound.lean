import NLAlib.Estimation.SLQLipschitz
import NLAlib.Estimation.SLQAnalyticSteps
import NLAlib.Matrix.CFCTrace

/-!
# Computable relative SLQ budgets from a positive scalar lower bound

The interval lower bound supplies positivity and `tr f(A) ≥ n f_min`. The resulting
analytic and Lipschitz step budgets do not require knowledge of the unknown trace.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory Real Set
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω n κ r : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype r] [DecidableEq r]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A positive lower bound `f_min` on the spectral interval makes the condition
`E ≤ ε f_min/4` sufficient for relative SLQ with `m ≥ 1024e² ε⁻² log(2/δ)` probes.
Positivity of the matrix function and the positive trace are derived from the actual
scalar lower bound. This general transfer keeps its polynomial approximation explicit.
Source: operator rederivations `rt:slq-relative`, computable-condition paragraph.
atlas: slq-error (partial) -/
theorem measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher_lower_bound
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k)) {q : ℕ}
    (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {f : ℝ → ℝ} {p : Polynomial ℝ} (hp : p.degree < 2 * q) {a c E b : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (hb : 0 < b)
    (hmin : ∀ x ∈ Icc a c, b ≤ f x) (hfp : ∀ x ∈ Icc a c, |f x - p.eval x| ≤ E)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hbudget : E ≤ ε * b / 4)
    (hm : 1024 * exp 1 ^ 2 * log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    (μ {ω | ε * (cfc f A).trace <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤ δ := by
  have hF := posSemidef_cfc_of_nonneg_eigenvalues hA (fun i => hb.le.trans (hmin _ (hspec i)))
  have htrle := mul_card_le_trace_cfc_of_le hA (fun i => hmin _ (hspec i))
  have hn : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have htr : 0 < (cfc f A).trace := (mul_pos hb hn).trans_le htrle
  apply measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_card_ge_rademacher
    hA hF htr hind hlaw hQ hK hp hspec hfp hε hε1 hδ _ hm
  calc 2 * (Fintype.card n : ℝ) * E ≤ 2 * (Fintype.card n : ℝ) * (ε * b / 4) := by
        gcongr
    _ = (ε / 2) * (b * Fintype.card n) := by ring
    _ ≤ (ε / 2) * (cfc f A).trace := mul_le_mul_of_nonneg_left htrle (by positivity)

/-- A positive scalar lower bound gives the computable Lipschitz step count
`q ≥ πL(c-a)/(2ε f_min)` and sample count `m ≥ 1024e² ε⁻² log(2/δ)` for relative SLQ.
All approximation, positivity, and trace premises are derived from the scalar hypotheses.
Source: operator rederivations `rt:slq-relative` and `rt:lipschitz-quad`.
atlas: slq-error -/
theorem measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher_lipschitz_lower_bound
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k)) {q : ℕ} (hq : 0 < q)
    (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {f : ℝ → ℝ} {a c b : ℝ} {L : NNReal} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (hf : LipschitzOnWith L f (Icc a c))
    (hb : 0 < b) (hmin : ∀ x ∈ Icc a c, b ≤ f x)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hsteps : Real.pi * (L : ℝ) * (c - a) / (2 * ε * b) ≤ q)
    (hm : 1024 * exp 1 ^ 2 * log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    (μ {ω | ε * (cfc f A).trace <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤ δ := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_jackson_interval hac hf (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  apply measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher_lower_bound
    hA hind hlaw hQ hK hdeg hspec hb hmin hfp hε hε1 hδ _ hm
  have hcast : ((2 * q - 1 : ℕ) : ℝ) + 1 = 2 * (q : ℝ) := by
    exact_mod_cast (show 2 * q - 1 + 1 = 2 * q by omega)
  rw [hcast, div_le_iff₀ (by exact_mod_cast (show 0 < 4 * (2 * q) by omega))]
  rw [div_le_iff₀ (by positivity)] at hsteps
  nlinarith

/-- A positive scalar lower bound gives the computable analytic step count
`q ≥ (1+log(8M/(ε f_min(ρ-1)))/log ρ)/2` and the exact Rademacher sample count
`m ≥ 1024e² ε⁻² log(2/δ)` for relative SLQ. Holomorphy and boundedness are on the
original open Bernstein ellipse, and the case `M=0` is included.
Source: operator rederivations `rt:slq-relative` and `rt:analytic-quad`.
atlas: slq-error -/
theorem measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher_analytic_lower_bound
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k)) {q : ℕ} (hq : 0 < q)
    (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a c ρ M b : ℝ} (hac : a < c) (hρ : 1 < ρ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M)
    (hmatch : ∀ t ∈ Icc (-1 : ℝ) 1, F t = (f (((c - a) * t + c + a) / 2) : ℂ))
    (hb : 0 < b) (hmin : ∀ x ∈ Icc a c, b ≤ f x)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hsteps : (1 + log (8 * M / (ε * b * (ρ - 1))) / log ρ) / 2 ≤ q)
    (hm : 1024 * exp 1 ^ 2 * log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    (μ {ω | ε * (cfc f A).trace <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤ δ := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse_interval
    hac hρ hFd hM hmatch (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  apply measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher_lower_bound
    hA hind hlaw hQ hK hdeg hspec hb hmin hfp hε hε1 hδ _ hm
  have hM0 : 0 ≤ M := nonneg_of_norm_le_on_open_bernsteinEllipse hρ hM
  rcases hM0.eq_or_lt with hzero | hpos
  · simp only [← hzero, mul_zero, zero_div]
    positivity
  · apply div_pow_sub_one_le_of_log_steps (show 0 < 2 * M by positivity)
      (show 0 < ε * b / 4 by positivity) hρ hq
    have hratio : 2 * M / ((ε * b / 4) * (ρ - 1)) = 8 * M / (ε * b * (ρ - 1)) := by
      field_simp
      norm_num
    simpa only [hratio] using hsteps

end NLAlib
