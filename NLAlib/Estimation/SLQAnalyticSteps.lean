import NLAlib.Estimation.SLQAnalytic
import NLAlib.ForMathlib.Analysis.GeometricRate

/-!
# Explicit logarithmic step counts for analytic SLQ

The analytic domain and magnitude parameters determine the Krylov step budget, while the
proved Hutchinson tail determines the probe count. Zero function size and zero dimension
are covered through the zero geometric-error branch.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory Real Set
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω n κ r : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype r] [DecidableEq r]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An explicit logarithmic analytic SLQ step budget gives absolute error threshold `ε`;
the stochastic tail is evaluated at `ε/2` with the exact Hanson–Wright constant.
Source: operator rederivations `rt:slq` (absolute analytic choice);
Ubaru–Chen–Saad 2017, Theorem 4.1, using NLAlib's concentration constant.
atlas: slq-error -/
theorem measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher_analytic_log_steps
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k)) {q : ℕ} (hq : 0 < q)
    (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a c ρ M : ℝ} (hac : a < c) (hρ : 1 < ρ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M)
    (hmatch : ∀ t ∈ Icc (-1 : ℝ) 1, F t = (f (((c - a) * t + c + a) / 2) : ℂ))
    {ε : ℝ} (hε : 0 < ε)
    (hsteps : (1 + log (8 * (Fintype.card n : ℝ) * M / (ε * (ρ - 1))) / log ρ) / 2 ≤ (q : ℝ)) :
    (μ {ω | ε < |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * (ε / 2) ^ 2 / frobNorm (cfc f A) ^ 2)
          (Fintype.card κ * (ε / 2) / specNorm (cfc f A))) := by
  have hM0 := nonneg_of_norm_le_on_open_bernsteinEllipse hρ hM
  have hbudget : 4 * (Fintype.card n : ℝ) * M / ρ ^ (2 * q - 1) / (ρ - 1) ≤ ε / 2 := by
    rcases eq_or_lt_of_le (show 0 ≤ 4 * (Fintype.card n : ℝ) * M by positivity) with hzero | hpos
    · rw [← hzero]; simp; positivity
    · apply div_pow_sub_one_le_of_log_steps hpos (show 0 < ε / 2 by positivity) hρ hq
      have hratio : 4 * (Fintype.card n : ℝ) * M / ((ε / 2) * (ρ - 1)) =
          8 * (Fintype.card n : ℝ) * M / (ε * (ρ - 1)) := by field_simp; ring
      rw [hratio]
      exact hsteps
  have hraw := measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher_open_bernsteinEllipse
    hA hind hlaw hQ hq hK hac hρ hspec hFd hM hmatch (η := ε / 2) (by positivity)
  refine (measureReal_mono (fun ω hω => ?_)).trans hraw
  change ε < _ at hω
  change ε / 2 + 4 * (Fintype.card n : ℝ) * M / ρ ^ (2 * q - 1) / (ρ - 1) < _
  linarith

/-- The fully explicit analytic relative-error SLQ choices: the geometric step budget
`q≥(1+log(8nM/(ετ(ρ-1)))/logρ)/2`, `q≥1`, and
`m≥1024e² log(2/δ)/ε²` imply failure probability at most `δ` for `|SLQ-τ|>ετ`.
Here `τ=tr f(A)>0` and `f(A)` is positive semidefinite.
Source: operator rederivations `rt:slq-relative` and the analytic step formula.
atlas: slq-error -/
theorem measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher_analytic_log_steps
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ} (hF : (cfc f A).PosSemidef)
    (htr : 0 < (cfc f A).trace) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k)) {q : ℕ} (hq : 0 < q)
    (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {F : ℂ → ℂ} {a c ρ M : ℝ} (hac : a < c) (hρ : 1 < ρ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M)
    (hmatch : ∀ t ∈ Icc (-1 : ℝ) 1, F t = (f (((c - a) * t + c + a) / 2) : ℂ))
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hsteps : (1 + log (8 * (Fintype.card n : ℝ) * M / (ε * (cfc f A).trace * (ρ - 1))) / log ρ) / 2 ≤
      (q : ℝ)) (hm : 1024 * exp 1 ^ 2 * log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    (μ {ω | ε * (cfc f A).trace <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤ δ := by
  apply measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher_analytic_card_ge
    hA hF htr hind hlaw hQ hq hK hac hρ hspec hFd hM hmatch hε hε1 hδ _ hm
  have hM0 := nonneg_of_norm_le_on_open_bernsteinEllipse hρ hM
  rcases eq_or_lt_of_le (show 0 ≤ 4 * (Fintype.card n : ℝ) * M by positivity) with hzero | hpos
  · rw [← hzero]; simp; positivity
  · apply div_pow_sub_one_le_of_log_steps hpos (show 0 < (ε / 2) * (cfc f A).trace by positivity) hρ hq
    have hratio : 4 * (Fintype.card n : ℝ) * M / (((ε / 2) * (cfc f A).trace) * (ρ - 1)) =
        8 * (Fintype.card n : ℝ) * M / (ε * (cfc f A).trace * (ρ - 1)) := by field_simp; ring
    rw [hratio]
    exact hsteps

end NLAlib
