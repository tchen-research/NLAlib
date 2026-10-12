import Mathlib.Probability.Moments.Variance

/-!
# Expectation-level assembly of the randomized SVD and generalized Nyström bounds

This file checks the *probabilistic assembly* of Chen–Persson, *One- and two-pass algorithms
for low-rank approximation*, Theorems `thm:RSVD` and `thm:GN` (the Frobenius-norm expected
error bounds of HMT 2011, Thm 10.5, and Tropp–Webber 2023, Thm 5.1).

Everything is phrased for real random variables on an abstract probability space `(Ω, μ)`;
expectations are Bochner integrals `∫ ω, X ω ∂μ`. No matrices appear; the matrix statements
are in `NLAlib/LowRank/RSVD.lean` and `NLAlib/LowRank/GeneralizedNystrom.lean`.

* The deterministic, pointwise inequalities (Chen–Persson `prop:hmt-struct`, i.e. HMT 2011,
  Thm 9.1) enter as *pointwise hypotheses* `∀ ω, …`.
* The Gaussian facts (Chen–Persson `lem:moments`, `lem:invmom`, `lem:completion`) enter ONLY
  as *explicit hypotheses on expectations*, exactly in the form the paper uses them after
  conditioning.
* Integrability of every random variable whose integral is manipulated is an explicit
  hypothesis.

What is proved here is the paper's own reasoning: linearity and monotonicity of expectation,
Jensen `E Y ≤ √(E Y²)`, and the arithmetic with explicit constants.

Ported from the LRA project (Chen–Persson formalization, same Mathlib pin),
`LRA/Probability/Assembly.lean` (`expectation_jensen_sqrt`, here
`integral_le_sqrt_integral_sq`; `rsvd_assembly`, `rsvd_explicit`, `gn_assembly`, `gn_explicit`)
and `LRA/Arithmetic/Constants.lean` (`completion_factor_mono`).

Atlas: `rsvd-expected-error`, `gn-expected-error`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace NLAlib.Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### A. Jensen and the completion factor -/

/-- Jensen's inequality in the form used throughout Chen–Persson: for a nonnegative
square-integrable random variable `Y`, `E Y ≤ √(E Y²)`. Proved from
`0 ≤ Var Y = E Y² − (E Y)²`. Helper for atlas `rsvd-expected-error` (Frobenius-norm,
unsquared form of HMT 2011, Thm 10.5). -/
theorem integral_le_sqrt_integral_sq [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : 0 ≤ Y)
    (hYi : Integrable Y μ) (hY2 : Integrable (fun ω => Y ω ^ 2) μ) :
    ∫ ω, Y ω ∂μ ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
  have hL2 : MemLp Y 2 μ := (memLp_two_iff_integrable_sq hYi.aestronglyMeasurable).mpr hY2
  have hvar := variance_nonneg Y μ
  rw [variance_eq_sub hL2] at hvar
  have h2 : (∫ ω, Y ω ∂μ) ^ 2 ≤ ∫ ω, Y ω ^ 2 ∂μ := by
    have : μ[Y ^ 2] = ∫ ω, Y ω ^ 2 ∂μ := rfl
    linarith
  exact (Real.le_sqrt (integral_nonneg hY) (integral_nonneg fun ω => sq_nonneg _)).mpr h2

/-- Monotonicity of the completion factor (Chen–Persson, proof of `thm:GN`): `q ↦ q/(s−q−1)`
is increasing for `q < s − 1`, so the factor of `lem:completion` for dimension `q ≤ k` is at
most that for `k`. Helper for atlas `gn-expected-error`. -/
theorem completion_factor_mono {q k s : ℝ} (hq : 0 ≤ q) (hqk : q ≤ k) (hks : k < s - 1) :
    q / (s - q - 1) ≤ k / (s - k - 1) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ### B. Randomized SVD (`thm:RSVD`) -/

/-- Assembly of Chen–Persson, Theorem `thm:RSVD` (HMT 2011, Thm 10.5, Frobenius case).
* `X = ‖A − Â‖_F²`, `Zsq = ‖Σ₂ Ω₂ Ω₁†‖_F²`, `OPTsq = ‖Σ₂‖_F² = ‖A − ⟦A⟧ₖ‖_F²`.
* `hX` is `prop:hmt-struct` (deterministic; `NLAlib.frobSq_residual_le_of_range_subset`).
* `hZ` encodes `lem:moments` + `lem:invmom` after the tower property:
  `E ‖Σ₂ Ω₂ Ω₁†‖_F² = ‖Σ₂‖_F² · k/(t−k−1)`; here with a general constant `c`.
Atlas `rsvd-expected-error`. -/
theorem rsvd_assembly [IsProbabilityMeasure μ] {X Zsq : Ω → ℝ} {OPTsq c : ℝ}
    (hX : ∀ ω, X ω ≤ OPTsq + Zsq ω) (hZ : ∫ ω, Zsq ω ∂μ = c * OPTsq)
    (hXi : Integrable X μ) (hZi : Integrable Zsq μ) :
    ∫ ω, X ω ∂μ ≤ (1 + c) * OPTsq := by
  calc ∫ ω, X ω ∂μ ≤ ∫ ω, (OPTsq + Zsq ω) ∂μ :=
        integral_mono hXi ((integrable_const _).add hZi) hX
    _ = OPTsq + c * OPTsq := by
        rw [integral_add (integrable_const _) hZi, integral_const, probReal_univ, one_smul, hZ]
    _ = (1 + c) * OPTsq := by ring

/-- Chen–Persson, Theorem `thm:RSVD` (HMT 2011, Thm 10.5, Frobenius case), expectation level,
with the paper's constant `c = k/(t−k−1)`. Atlas `rsvd-expected-error`.
atlas: rsvd-expected-error -/
theorem rsvd_explicit [IsProbabilityMeasure μ] {X Zsq : Ω → ℝ} {OPTsq k t : ℝ}
    (hX : ∀ ω, X ω ≤ OPTsq + Zsq ω) (hZ : ∫ ω, Zsq ω ∂μ = k / (t - k - 1) * OPTsq)
    (hXi : Integrable X μ) (hZi : Integrable Zsq μ) :
    ∫ ω, X ω ∂μ ≤ (1 + k / (t - k - 1)) * OPTsq :=
  rsvd_assembly hX hZ hXi hZi

/-! ### C. Generalized Nyström (`thm:GN`) -/

/-- Abstract assembly of Chen–Persson, Theorem `thm:GN` (Tropp–Webber 2023, Thm 5.1).
* `X = ‖A − Â‖_F²`, `Y = ‖(I − QQᵀ)A‖_F²` (the range-finder error),
  `cfac ω = 1 + q(ω)/(s − q(ω) − 1)` with `q = rank(AΩ)` the (random) number of columns of `Q`.
* `hcond` encodes `lem:completion` after the tower property (conditioning on `Ω`, using
  independence of `Ψ` and `Ω`): `E X = E[(1 + q/(s−q−1)) Y]`.
* `hc` is the deterministic bound `q ≤ t` and monotonicity of `q ↦ q/(s−q−1)`
  (`completion_factor_mono`).
* `hYbound` is the range-finder theorem (`thm:RSVD`).
Atlas `gn-expected-error`. -/
theorem gn_assembly {X Y cfac : Ω → ℝ} {cmax B : ℝ} (hY : 0 ≤ Y) (hcmax : 0 ≤ cmax)
    (hc : ∀ ω, cfac ω ≤ cmax) (hcond : ∫ ω, X ω ∂μ = ∫ ω, cfac ω * Y ω ∂μ)
    (hYbound : ∫ ω, Y ω ∂μ ≤ B)
    (hcYi : Integrable (fun ω => cfac ω * Y ω) μ) (hYi : Integrable Y μ) :
    ∫ ω, X ω ∂μ ≤ cmax * B := by
  rw [hcond]
  calc ∫ ω, cfac ω * Y ω ∂μ ≤ ∫ ω, cmax * Y ω ∂μ :=
        integral_mono hcYi (hYi.const_mul _) fun ω => mul_le_mul_of_nonneg_right (hc ω) (hY ω)
    _ = cmax * ∫ ω, Y ω ∂μ := integral_const_mul _ _
    _ ≤ cmax * B := mul_le_mul_of_nonneg_left hYbound hcmax

/-- Chen–Persson, Theorem `thm:GN` (Tropp–Webber 2023, Thm 5.1), expectation level:
`t ≥ k+2`, `s ≥ t+2`,
`E‖A − Â‖_F² ≤ (1 + t/(s−t−1)) (1 + k/(t−k−1)) ‖A − ⟦A⟧ₖ‖_F²`.
Hypotheses: `hc` (`lem:completion`'s factor with `q = rank(AΩ) ≤ t`), `hcond`
(`lem:completion` + tower property), `hstruct` (`prop:hmt-struct` for
`Y = ‖(I−QQᵀ)A‖_F²`), `hZ` (`lem:moments` + `lem:invmom`, as in the proof of `thm:RSVD`).
The hypothesis `hk` is not used by the arithmetic; it is kept for fidelity.
Atlas `gn-expected-error` (uses `rsvd-expected-error`).
atlas: gn-expected-error -/
theorem gn_explicit [IsProbabilityMeasure μ] {X Y cfac Zsq : Ω → ℝ} {k t s OPTsq : ℝ}
    (hk : 0 ≤ k) (hkt : k + 2 ≤ t) (hts : t + 2 ≤ s)
    (hY : 0 ≤ Y) (hc : ∀ ω, cfac ω ≤ 1 + t / (s - t - 1))
    (hcond : ∫ ω, X ω ∂μ = ∫ ω, cfac ω * Y ω ∂μ)
    (hstruct : ∀ ω, Y ω ≤ OPTsq + Zsq ω) (hZ : ∫ ω, Zsq ω ∂μ = k / (t - k - 1) * OPTsq)
    (hcYi : Integrable (fun ω => cfac ω * Y ω) μ) (hYi : Integrable Y μ)
    (hZi : Integrable Zsq μ) :
    ∫ ω, X ω ∂μ ≤ (1 + t / (s - t - 1)) * ((1 + k / (t - k - 1)) * OPTsq) := by
  have hcmax : 0 ≤ 1 + t / (s - t - 1) := by
    have : 0 ≤ t / (s - t - 1) := div_nonneg (by linarith) (by linarith)
    linarith
  exact gn_assembly hY hcmax hc hcond (rsvd_explicit hstruct hZ hYi hZi) hcYi hYi

end NLAlib.Assembly

end
