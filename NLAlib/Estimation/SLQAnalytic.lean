import NLAlib.Estimation.SLQRademacher
import NLAlib.Krylov.AnalyticQuadrature

/-!
# Analytic stochastic Lanczos quadrature

Original open Bernstein ellipse hypotheses produce the scalar polynomial needed by the
general Rademacher trace tail; no approximation certificate or boundary extension is assumed.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory Real Set
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω n κ r : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype r] [DecidableEq r]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Analytic SLQ with independent Rademacher probes has the exact tail threshold
`η+4nM/(ρ^(2q-1)(ρ-1))`. The tail constant is the proved NLAlib Hanson–Wright constant,
and the analytic domain and size parameters remain explicit.
Source: Ubaru–Chen–Saad 2017, Theorem 4.1; operator rederivations `rt:slq-tail` and
`rt:analytic-quad`.
atlas: slq-error -/
theorem measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher_open_bernsteinEllipse
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
    {η : ℝ} (hη : 0 ≤ η) :
    (μ {ω | η + 4 * (Fintype.card n : ℝ) * M / ρ ^ (2 * q - 1) / (ρ - 1) <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * η ^ 2 / frobNorm (cfc f A) ^ 2)
          (Fintype.card κ * η / specNorm (cfc f A))) := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse_interval
    hac hρ hFd hM hmatch (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  have h := measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher
    hA hind hlaw hQ hK hdeg hspec hfp hη
  have hthresh : η + 2 * (Fintype.card n : ℝ) * (2 * M / ρ ^ (2 * q - 1) / (ρ - 1)) =
      η + 4 * (Fintype.card n : ℝ) * M / ρ ^ (2 * q - 1) / (ρ - 1) := by ring
  simpa only [hthresh] using h

/-- Relative analytic SLQ with the exact Rademacher sample budget has failure probability
at most `δ` once the concrete geometric rate pays half the error budget.
Source: operator rederivations `rt:slq-relative`, Ubaru–Chen–Saad 2017, Theorem 4.1;
constant `1024e²` comes from the proved Hanson–Wright constant.
atlas: slq-error -/
theorem measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher_analytic_card_ge
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
    (hsteps : 4 * (Fintype.card n : ℝ) * M / ρ ^ (2 * q - 1) / (ρ - 1) ≤
      (ε / 2) * (cfc f A).trace)
    (hm : 1024 * exp 1 ^ 2 * log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    (μ {ω | ε * (cfc f A).trace <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤ δ := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse_interval
    hac hρ hFd hM hmatch (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  exact measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_card_ge_rademacher hA hF htr
    hind hlaw hQ hK hdeg hspec hfp hε hε1 hδ (by convert hsteps using 1; ring) hm

end NLAlib
