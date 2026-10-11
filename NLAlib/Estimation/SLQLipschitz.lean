import NLAlib.Estimation.SLQRademacher
import NLAlib.Krylov.LipschitzQuadrature

/-!
# Lipschitz stochastic Lanczos quadrature with concrete budgets

The actual sharp Jackson polynomial gives the deterministic term `πLn(c-a)/(4q)`.
The established Rademacher Hanson–Wright tail then gives both absolute and relative
error with explicit step and sample counts.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory Real Set
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω n κ r : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype r] [DecidableEq r]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- SLQ for any interval-Lipschitz function has threshold `η+πLn(c-a)/(4q)` and the
established exact Hanson–Wright tail constant `1/(256e²)`. The scalar approximant is
constructed from the Lipschitz hypothesis rather than supplied as a certificate.
Source: Ubaru–Chen–Saad 2017, Theorem 4.1; operator rederivations `rt:slq-tail`
and `rt:lipschitz-quad`.
atlas: slq-error -/
theorem measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher_lipschitzOnWith
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k)) {q : ℕ} (hq : 0 < q)
    (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {f : ℝ → ℝ} {a c : ℝ} {L : NNReal} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (hf : LipschitzOnWith L f (Icc a c))
    {η : ℝ} (hη : 0 ≤ η) :
    (μ {ω | η + Real.pi * (L : ℝ) * (Fintype.card n : ℝ) * (c - a) / (4 * q) <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * η ^ 2 / frobNorm (cfc f A) ^ 2)
          (Fintype.card κ * η / specNorm (cfc f A))) := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_jackson_interval hac hf (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  have h := measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher
    hA hind hlaw hQ hK hdeg hspec hfp hη
  have hcast : ((2 * q - 1 : ℕ) : ℝ) + 1 = 2 * (q : ℝ) := by
    exact_mod_cast (show 2 * q - 1 + 1 = 2 * q by omega)
  rw [hcast] at h
  have hthresh : η + 2 * (Fintype.card n : ℝ) * (Real.pi * (L : ℝ) * (c - a) / (4 * (2 * q))) =
      η + Real.pi * (L : ℝ) * (Fintype.card n : ℝ) * (c - a) / (4 * q) := by ring
  simpa only [hthresh] using h

/-- The concrete Lipschitz step count `q ≥ πLn(c-a)/(2ε)` leaves half of an absolute
error budget for the stochastic term. No norm or polynomial approximation is assumed.
Source: operator rederivations `rt:slq-tail` and the paragraph following `rt:slq-relative`.
atlas: slq-error -/
theorem measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher_lipschitz_steps
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k)) {q : ℕ} (hq : 0 < q)
    (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {f : ℝ → ℝ} {a c : ℝ} {L : NNReal} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (hf : LipschitzOnWith L f (Icc a c))
    {ε : ℝ} (hε : 0 < ε)
    (hsteps : Real.pi * (L : ℝ) * (Fintype.card n : ℝ) * (c - a) / (2 * ε) ≤ q) :
    (μ {ω | ε < |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * (ε / 2) ^ 2 / frobNorm (cfc f A) ^ 2)
          (Fintype.card κ * (ε / 2) / specNorm (cfc f A))) := by
  have hraw := measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher_lipschitzOnWith
    hA hind hlaw hQ hq hK hac hspec hf (η := ε / 2) (by positivity)
  have hbudget : Real.pi * (L : ℝ) * (Fintype.card n : ℝ) * (c - a) / (4 * q) ≤ ε / 2 := by
    rw [div_le_iff₀ (by exact_mod_cast (show 0 < 4 * q by omega))]
    rw [div_le_iff₀ (by positivity)] at hsteps
    nlinarith
  refine (measureReal_mono ?_).trans hraw
  intro ω hω
  change ε < _ at hω
  change ε / 2 + Real.pi * (L : ℝ) * (Fintype.card n : ℝ) * (c - a) / (4 * q) < _
  linarith

/-- For a positive semidefinite matrix function with trace `τ>0`, the concrete Lipschitz
step count `q ≥ πLn(c-a)/(2ετ)` and sample count
`m ≥ 1024e² ε⁻² log(2/δ)` give relative error at most `ε` with failure at most `δ`.
Source: Ubaru–Chen–Saad 2017, Theorem 4.1; operator rederivations `rt:slq-relative`.
atlas: slq-error -/
theorem measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher_lipschitz_steps
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ} (hF : (cfc f A).PosSemidef)
    (htr : 0 < (cfc f A).trace) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k)) {q : ℕ} (hq : 0 < q)
    (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {a c : ℝ} {L : NNReal} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (hf : LipschitzOnWith L f (Icc a c))
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hsteps : Real.pi * (L : ℝ) * (Fintype.card n : ℝ) * (c - a) /
      (2 * ε * (cfc f A).trace) ≤ q)
    (hm : 1024 * exp 1 ^ 2 * log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    (μ {ω | ε * (cfc f A).trace <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤ δ := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_jackson_interval hac hf (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  apply measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_card_ge_rademacher hA hF htr
    hind hlaw hQ hK hdeg hspec hfp hε hε1 hδ _ hm
  have hcast : ((2 * q - 1 : ℕ) : ℝ) + 1 = 2 * (q : ℝ) := by
    exact_mod_cast (show 2 * q - 1 + 1 = 2 * q by omega)
  rw [hcast]
  have hbudget : Real.pi * (L : ℝ) * (Fintype.card n : ℝ) * (c - a) / (4 * q) ≤
      (ε / 2) * (cfc f A).trace := by
    rw [div_le_iff₀ (by exact_mod_cast (show 0 < 4 * q by omega))]
    rw [div_le_iff₀ (by positivity)] at hsteps
    nlinarith
  convert hbudget using 1
  ring

end NLAlib
