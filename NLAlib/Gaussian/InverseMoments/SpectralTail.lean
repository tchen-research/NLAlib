/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_tw_inverse_moment_numeric`, `Sol_GaussianMatrix_pinv_spectral_tail`,
`Sol_GaussianMatrix_pinv_spectral_expectation`,
`Sol_GaussianMatrix_inverse_wishart_spectral_moment`).
-/
import NLAlib.Gaussian.InverseMoments.LambdaMinTail
import NLAlib.Gaussian.InverseMoments.SpectralProbe
import NLAlib.Matrix.Measurable
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Spectral tails and moments of the Gaussian pseudoinverse

For an `r × k` standard Gaussian matrix `G` with pseudoinverse `G† = pinvR G = Gᵀ (G Gᵀ)⁻¹`:

* `gaussianMatrix_lt_specNorm_pinvR_le`: the tail
  `P[‖G†‖ > t] ≤ (2π(k-r+1))^{-1/2} (e√k/(k-r+1))^{k-r+1} t^{-(k-r+1)}` for `2 ≤ r ≤ k`
  (HMT 2011, Prop A.3; Chen–Dongarra 2005; atlas `pinv-spectral-tail`);
* `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le`: `E‖G†‖ ≤ e√k/(k-r)` for
  `2 ≤ r`, `r + 1 ≤ k` (HMT 2011, Prop A.4; atlas `pinv-spectral-expectation`);
* `integrable_and_integral_specNorm_inv_self_mul_transpose_pow_gaussianMatrix_le`:
  `E‖(G Gᵀ)⁻¹‖^p ≤ (e² (k+r) / (2 (k-r)²))^p` for `1 ≤ p ≤ 18`, `r + 2p ≤ k`
  (Tropp–Webber 2023, Lemma B.4; atlas `inverse-wishart-spectral-moment`);
* `one_add_div_mul_inv_Gamma_rpow_le`: the numerical inequality (B.8) of Tropp–Webber 2023
  behind the last bound.

The two moment statements use the direct Gaussian quadratic-probe route and
are independent of the smallest-eigenvalue density. The tail statement uses
`gaussianMatrix_sigmaMin_transpose_sq_le_le`, atlas `wishart-lambda-min-tail`.

Proof source: Prove2me workspace, Gaussian Random Matrices series; the workspace's
`integral_le_of_tail_bound` is `NLAlib.integrable_and_integral_le_of_tail_le_rpow`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### The numerical inequality (B.8) -/

/-- The integer inequality `(2p+1)^(2p+2) ≤ 46^(2p)` for `1 ≤ p ≤ 18`. -/
private lemma two_mul_add_one_pow_le {p : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18) :
    (2 * p + 1) ^ (2 * p + 2) ≤ 46 ^ (2 * p) := by
  interval_cases p <;> norm_num

/-- `46 ≤ 2π e²`. -/
private lemma forty_six_le_two_pi_mul_exp_sq : (46 : ℝ) ≤ 2 * Real.pi * Real.exp 1 ^ 2 := by
  have he := Real.exp_one_gt_d9
  have hpi := Real.pi_gt_d2
  nlinarith

/-- `(c+2) log(c+1) ≤ c (log (2π) + 2)` for `c = 2p`, `1 ≤ p ≤ 18`. -/
private lemma mul_log_le_of_le_eighteen {p : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18) :
    (2 * (p : ℝ) + 2) * Real.log (2 * p + 1)
      ≤ 2 * (p : ℝ) * (Real.log (2 * Real.pi) + 2) := by
  have hint : ((2 * p + 1 : ℕ) : ℝ) ^ (2 * p + 2) ≤ ((46 : ℕ) : ℝ) ^ (2 * p) := by
    exact_mod_cast two_mul_add_one_pow_le hp hp18
  push_cast at hint
  have h46 : (46 : ℝ) ^ (2 * p) ≤ (2 * Real.pi * Real.exp 1 ^ 2) ^ (2 * p) :=
    pow_le_pow_left₀ (by norm_num) forty_six_le_two_pi_mul_exp_sq _
  have hpos : (0 : ℝ) < (2 * p + 1) ^ (2 * p + 2) := by positivity
  have hlog := Real.log_le_log hpos (hint.trans h46)
  rw [Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_exp] at hlog
  push_cast at hlog
  linarith

/-- **Numerical inequality for the inverse Wishart spectral moments.** For integers
`1 ≤ p ≤ 18` and `x ≥ 2p`,
`(1 + 2p/(x+1-2p)) · (1/Γ(x+2))^{2p/(x+1)} ≤ (e/x)^{2p}`.

Tropp–Webber 2023, (B.8) (the range `p ≤ 18` is where the integer check
`(2p+1)^{2p+2} ≤ 46^{2p} ≤ (2π e²)^{2p}` holds). Atlas: `inverse-wishart-spectral-moment`
(helper). Proof: Stirling's lower bound for `(x+1)!`, concavity of `log`, and the integer check.
Ported from Prove2me solution `GaussianMatrix.tw_inverse_moment_numeric`. -/
theorem one_add_div_mul_inv_Gamma_rpow_le {p x : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18)
    (hx : 2 * p ≤ x) :
    (1 + 2 * (p : ℝ) / ((x : ℝ) + 1 - 2 * p))
        * (1 / Real.Gamma ((x : ℝ) + 2)) ^ (2 * (p : ℝ) / ((x : ℝ) + 1))
      ≤ (Real.exp 1 / x) ^ (2 * p) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hxR : 2 * (p : ℝ) ≤ x := by exact_mod_cast hx
  set X : ℝ := (x : ℝ) with hX
  set c : ℝ := 2 * (p : ℝ) with hc
  set n : ℝ := X + 1 with hn
  have hc0 : 0 < c := by rw [hc]; linarith
  have hX0 : 0 < X := by linarith
  have hn0 : 0 < n := by linarith
  have hnc : 0 < n - c := by rw [hn]; linarith
  have hG : Real.Gamma (X + 2) = ((x + 1).factorial : ℝ) := by
    have h2 : ((x + 1 : ℕ) : ℝ) + 1 = X + 2 := by rw [hX]; push_cast; ring
    rw [← Real.Gamma_nat_eq_factorial, h2]
  set F : ℝ := ((x + 1).factorial : ℝ) with hF
  have hF0 : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  rw [hG]
  set a : ℝ := 1 + c / (X + 1 - c) with ha
  have ha' : a = n / (n - c) := by
    have hd : X + 1 - c ≠ 0 := by linarith
    rw [ha, hn]; field_simp; ring
  have ha0 : 0 < a := by rw [ha']; positivity
  have hL : 0 < a * (1 / F) ^ (c / n) := by positivity
  have hR : 0 < (Real.exp 1 / X) ^ (2 * p) := by positivity
  have hF1 : (0 : ℝ) < 1 / F := by positivity
  have hrp : (0 : ℝ) < (1 / F) ^ (c / n) := Real.rpow_pos_of_pos hF1 _
  rw [← Real.log_le_log_iff hL hR, Real.log_mul ha0.ne' hrp.ne',
    Real.log_rpow hF1, Real.log_pow, Real.log_div (Real.exp_pos 1).ne' hX0.ne',
    Real.log_exp, one_div, Real.log_inv]
  -- S1: Stirling
  have hS1 : (1 / 2) * Real.log (2 * Real.pi * n) + n * Real.log n - n ≤ Real.log F := by
    have h := Stirling.le_factorial_stirling (x + 1)
    have hcast : ((x + 1 : ℕ) : ℝ) = n := by rw [hn, hX]; push_cast; ring
    rw [hcast] at h
    have hpos : 0 < Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ (x + 1) := by positivity
    have hl := Real.log_le_log hpos h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
      Real.log_pow, Real.log_div hn0.ne' (Real.exp_pos 1).ne', Real.log_exp] at hl
    have hcast2 : ((x + 1 : ℕ) : ℝ) = n := hcast
    rw [hcast2] at hl
    linarith
  -- S2: concavity of log
  have hS2 : n * (Real.log n - Real.log (n - c)) ≤ (c + 1) * Real.log (c + 1) := by
    have hconc := strictConcaveOn_log_Ioi.concaveOn
    have hb0 : 0 ≤ (c + 1) / n := by positivity
    have hb1 : (c + 1) / n ≤ 1 := by rw [div_le_one hn0]; rw [hn]; linarith
    have h : (1 - (c + 1) / n) • Real.log 1 + ((c + 1) / n) • Real.log (1 / (c + 1))
        ≤ Real.log ((1 - (c + 1) / n) • (1 : ℝ) + ((c + 1) / n) • (1 / (c + 1))) :=
      hconc.2 (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 (by positivity)) (by linarith) hb0
        (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at h
    have hpt : 1 - (c + 1) / n + (c + 1) / n * (1 / (c + 1)) = (n - c) / n := by
      field_simp; ring
    rw [hpt, Real.log_div hnc.ne' hn0.ne', one_div, Real.log_inv] at h
    have h2 : n * ((c + 1) / n * -Real.log (c + 1)) ≤ n * (Real.log (n - c) - Real.log n) :=
      mul_le_mul_of_nonneg_left h hn0.le
    have h3 : n * ((c + 1) / n * -Real.log (c + 1)) = -((c + 1) * Real.log (c + 1)) := by
      field_simp
    linarith
  -- S3: `n log((n-1)/n) ≤ -1`
  have hS3 : n * Real.log X - n * Real.log n ≤ -1 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := n / X) (by positivity)
    rw [Real.log_div hn0.ne' hX0.ne', inv_div] at h
    have h1 : 1 - X / n = 1 / n := by rw [hn]; field_simp; ring
    rw [h1] at h
    have h2 : n * (1 / n) ≤ n * (Real.log n - Real.log X) := mul_le_mul_of_nonneg_left h hn0.le
    rw [mul_one_div_cancel hn0.ne'] at h2
    linarith
  -- S4: the numerical check
  have hS4 : (c + 2) * Real.log (c + 1) ≤ c * (Real.log (2 * Real.pi) + 2) := by
    have := mul_log_le_of_le_eighteen hp hp18
    rw [hc]; linarith
  -- S5: monotonicity of log
  have hS5 : Real.log (2 * Real.pi * (c + 1)) ≤ Real.log (2 * Real.pi * n) :=
    Real.log_le_log (by positivity) (by
      have : c + 1 ≤ n := by rw [hn]; linarith
      nlinarith [Real.pi_pos])
  have hS5' : Real.log (2 * Real.pi * (c + 1)) = Real.log (2 * Real.pi) + Real.log (c + 1) :=
    Real.log_mul (by positivity) (by positivity)
  have hla : Real.log a = Real.log n - Real.log (n - c) := by
    rw [ha', Real.log_div hn0.ne' hnc.ne']
  rw [hla]
  have hpc : ((2 * p : ℕ) : ℝ) = c := by rw [hc]; push_cast; ring
  rw [hpc]
  have key : n * (Real.log n - Real.log (n - c)) - c * Real.log F
      ≤ n * (c * (1 - Real.log X)) := by
    have e1 : c * ((1 / 2) * Real.log (2 * Real.pi * n) + n * Real.log n - n)
        ≤ c * Real.log F := mul_le_mul_of_nonneg_left hS1 hc0.le
    have e3 : c * (n * Real.log X - n * Real.log n) ≤ c * (-1) :=
      mul_le_mul_of_nonneg_left hS3 hc0.le
    have e5 : c * Real.log (2 * Real.pi * (c + 1)) ≤ c * Real.log (2 * Real.pi * n) :=
      mul_le_mul_of_nonneg_left hS5 hc0.le
    rw [hS5'] at e5
    nlinarith
  have hfin : n * (Real.log n - Real.log (n - c) + c / n * -Real.log F)
      ≤ n * (c * (1 - Real.log X)) := by
    have : n * (Real.log n - Real.log (n - c) + c / n * -Real.log F)
        = n * (Real.log n - Real.log (n - c)) - c * Real.log F := by field_simp; ring
    rw [this]; exact key
  exact le_of_mul_le_mul_left hfin hn0

/-! ### Tail and expectation of `‖G†‖` -/

/-- The scalar inequality behind the Stirling simplification: for an integer `N ≥ 1`,
`(1/Γ(N+1)) ((K+R)/(2t²))^{N/2} ≤ (2πN)^{-1/2} (e√K/N)^N t^{-N}` when `0 ≤ R ≤ K`. -/
private lemma inv_Gamma_mul_rpow_le {N : ℕ} (hN : 1 ≤ N) (K R t : ℝ) (hRK : R ≤ K)
    (hR : 0 ≤ R) (ht : 0 < t) :
    (1 / Real.Gamma ((N : ℝ) + 1)) * (1 / t ^ 2 * (K + R) / 2) ^ ((N : ℝ) / 2)
      ≤ (1 / Real.sqrt (2 * Real.pi * N)) * (Real.exp 1 * Real.sqrt K / N) ^ (N : ℝ)
          * t ^ (-(N : ℝ)) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK : 0 ≤ K := le_trans hR hRK
  rw [Real.Gamma_nat_eq_factorial]
  have hst := Stirling.le_factorial_stirling N
  have hS0 : 0 < Real.sqrt (2 * Real.pi * N) * (N / Real.exp 1) ^ N := by
    have : 0 < 2 * Real.pi * N := by positivity
    positivity
  set y : ℝ := 1 / t ^ 2 * (K + R) / 2 with hy_def
  have hy0 : 0 ≤ y := by positivity
  have hy : y ^ ((N : ℝ) / 2) = (Real.sqrt y) ^ N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy0]
    ring_nf
  have hsy : Real.sqrt y = Real.sqrt ((K + R) / 2) / t := by
    rw [show y = ((K + R) / 2) / t ^ 2 by rw [hy_def]; ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq ht.le]
  have hle : Real.sqrt ((K + R) / 2) ≤ Real.sqrt K := Real.sqrt_le_sqrt (by linarith)
  rw [hy, hsy, Real.rpow_natCast, Real.rpow_neg ht.le, Real.rpow_natCast]
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  calc 1 / (N.factorial : ℝ) * (Real.sqrt ((K + R) / 2) / t) ^ N
      ≤ 1 / (N.factorial : ℝ) * (Real.sqrt K / t) ^ N := by
        gcongr
    _ ≤ 1 / (Real.sqrt (2 * Real.pi * N) * (N / Real.exp 1) ^ N) * (Real.sqrt K / t) ^ N := by
        gcongr
    _ = 1 / Real.sqrt (2 * Real.pi * N) * (Real.exp 1 * Real.sqrt K / N) ^ N * (t ^ N)⁻¹ := by
        have h1 : Real.sqrt (2 * Real.pi * N) ≠ 0 := by
          have : 0 < 2 * Real.pi * N := by positivity
          positivity
        have h2 : (N : ℝ) ≠ 0 := by positivity
        simp only [div_pow, mul_pow]
        field_simp

/-- **Tail bound for the spectral norm of the Gaussian pseudoinverse.** For an `r × k`
standard Gaussian matrix `G` with `2 ≤ r ≤ k` and `t > 0`,
`P[‖G†‖ > t] ≤ (2π(k-r+1))^{-1/2} (e√k/(k-r+1))^{k-r+1} t^{-(k-r+1)}`,
with `G† = pinvR G`.

HMT 2011, Prop A.3; Chen–Dongarra 2005, Lemma 4.1. Atlas: `pinv-spectral-tail`. Proof:
`‖G†‖² = ‖(G Gᵀ)⁻¹‖ = 1/σ_min(Gᵀ)²` (`specNorm_pinvR_sq`,
`specNorm_inv_self_mul_transpose_eq`, atlas `pseudoinverse`), the `λ_min` lower tail
(`gaussianMatrix_sigmaMin_transpose_sq_le_le`, atlas `wishart-lambda-min-tail`, which uses the
proved operator bound (B.5)) and Stirling's formula. Ported from Prove2me solution
`GaussianMatrix.pinv_spectral_tail`.
atlas: pinv-spectral-tail -/
theorem gaussianMatrix_lt_specNorm_pinvR_le {r k : ℕ} (hr : 2 ≤ r) (hrk : r ≤ k) (t : ℝ)
    (ht : 0 < t) :
    (gaussianMatrix r k) {G | t < specNorm (pinvR (Matrix.of G))}
      ≤ ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi * ((k : ℝ) - r + 1)))
          * (Real.exp 1 * Real.sqrt k / ((k : ℝ) - r + 1)) ^ ((k : ℝ) - r + 1)
          * t ^ (-((k : ℝ) - r + 1))) := by
  have hsub : {G : Fin r → Fin k → ℝ | t < specNorm (pinvR (Matrix.of G))}
      ⊆ {G | sigmaMin (Matrix.of G)ᵀ ^ 2 ≤ 1 / t ^ 2} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    have hsq : specNorm (pinvR (Matrix.of G)) ^ 2 = 1 / sigmaMin (Matrix.of G)ᵀ ^ 2 := by
      rw [specNorm_pinvR_sq, specNorm_inv_self_mul_transpose_eq]
    have h1 : t ^ 2 < 1 / sigmaMin (Matrix.of G)ᵀ ^ 2 := by
      rw [← hsq]; exact pow_lt_pow_left₀ hG ht.le (by norm_num)
    have hs2 : 0 < sigmaMin (Matrix.of G)ᵀ ^ 2 := by
      rcases (sq_nonneg (sigmaMin (Matrix.of G)ᵀ)).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at h1; nlinarith
    have ht2 : 0 < t ^ 2 := by positivity
    rw [lt_div_iff₀ hs2] at h1
    rw [le_div_iff₀ ht2]
    linarith
  refine (measure_mono hsub).trans ?_
  have hr1 : 1 ≤ r := by omega
  refine (gaussianMatrix_sigmaMin_transpose_sq_le_le hr1 hrk (1 / t ^ 2) (by positivity)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  set N : ℕ := k - r + 1 with hN_def
  have hN : (N : ℝ) = (k : ℝ) - r + 1 := by
    rw [hN_def, Nat.cast_add, Nat.cast_sub hrk]; push_cast; ring
  have hN2 : (k : ℝ) - r + 2 = (N : ℝ) + 1 := by rw [hN]; ring
  rw [hN2, ← hN]
  have hRK : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have := inv_Gamma_mul_rpow_le (N := N) (by omega) (k : ℝ) (r : ℝ) t hRK (by positivity) ht
  convert this using 3

/-- **Expectation of the spectral norm of the Gaussian pseudoinverse.** For an `r × k`
standard Gaussian matrix `G` with `2 ≤ r` and `r + 1 ≤ k`, `‖G†‖` is integrable and
`E‖G†‖ ≤ e√k/(k-r)`, with `G† = pinvR G`.

HMT 2011, Prop A.4 (`E‖Ω₁†‖ ≤ e√(k+p)/p` with `Ω₁` of size `k × (k+p)`). Atlas:
`pinv-spectral-expectation`. Proof: Gaussian quadratic probes, Schur residual laws,
scalar Gamma estimates, and positive moment comparison. The sharper expectation
bound with k+r-1 is proved in SpectralProbe and implies the source constant.
This proof has no density or spectral-tail dependency.
atlas: pinv-spectral-expectation -/
theorem integrable_and_integral_specNorm_pinvR_gaussianMatrix_le {r k : ℕ} (hr : 2 ≤ r)
    (hrk : r + 1 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) (gaussianMatrix r k) ∧
    ∫ G, specNorm (pinvR (Matrix.of G)) ∂(gaussianMatrix r k)
      ≤ Real.exp 1 * Real.sqrt k / ((k : ℝ) - r) := by
  have hr1 : 1 ≤ r := by omega
  have hrk' : r < k := by omega
  obtain ⟨hint, hbound⟩ :=
    integrable_and_integral_specNorm_pinvR_gaussianMatrix_le_sharp hr1 hrk'
  refine ⟨hint, hbound.trans ?_⟩
  have hgap : (0 : ℝ) < (k : ℝ) - r := sub_pos.mpr (by exact_mod_cast hrk')
  have hcast : (r : ℝ) < k := by exact_mod_cast hrk'
  have hsqrt : Real.sqrt (((k : ℝ) + r - 1) / 2) ≤ Real.sqrt k :=
    Real.sqrt_le_sqrt (by linarith)
  calc Real.exp 1 / ((k : ℝ) - r) * Real.sqrt (((k : ℝ) + r - 1) / 2)
      ≤ Real.exp 1 / ((k : ℝ) - r) * Real.sqrt k :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = Real.exp 1 * Real.sqrt k / ((k : ℝ) - r) := by ring

/-! ### Spectral moments of the inverse Wishart matrix -/

open scoped Matrix.Norms.L2Operator in
private lemma specNorm_of_isEmpty {m : Type*} [Fintype m] [DecidableEq m] [IsEmpty m]
    (A : Matrix m m ℝ) : specNorm A = 0 := by
  rw [specNorm, Subsingleton.elim A 0, norm_zero]

set_option linter.unusedVariables false in
/-- **Spectral moments of the inverse Wishart matrix.** For an `r × k` standard Gaussian matrix
`G` and integers `1 ≤ p ≤ 18` with `r + 2p ≤ k`, `‖(G Gᵀ)⁻¹‖^p` is integrable and
`E‖(G Gᵀ)⁻¹‖^p ≤ (e² (k+r) / (2 (k-r)²))^p`, i.e.
`(E‖(G Gᵀ)⁻¹‖^p)^{1/p} ≤ e² (k+r) / (2 (k-r)²)`.

Tropp–Webber 2023, Appendix B, (B.4). Atlas: `inverse-wishart-spectral-moment`.
Proof: the direct operator quadratic-probe real moment bound, scalar Gamma estimates,
and moment monotonicity. The source's p ≤ 18 condition is retained in this
corollary; the stronger real-power theorem in SpectralProbe does not need it.
atlas: inverse-wishart-spectral-moment -/
theorem integrable_and_integral_specNorm_inv_self_mul_transpose_pow_gaussianMatrix_le
    {r k p : ℕ} (hp : 1 ≤ p) (hp18 : p ≤ 18) (hrk : r + 2 * p ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p)
      (gaussianMatrix r k) ∧
    ∫ G, specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p ∂(gaussianMatrix r k)
      ≤ (Real.exp 1 ^ 2 * ((k : ℝ) + r) / (2 * ((k : ℝ) - r) ^ 2)) ^ p := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · subst hr0
    have hf : (fun G : Fin 0 → Fin k → ℝ =>
        specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ p) = fun _ => 0 := by
      funext G
      rw [specNorm_of_isEmpty, zero_pow (by omega)]
    rw [hf]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [integral_zero]
    positivity
  have hr : 1 ≤ r := by omega
  have hrk' : r < k := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hgap : 2 * (p : ℝ) ≤ (k : ℝ) - r := by
    have h : ((r + 2 * p : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
    push_cast at h
    linarith
  obtain ⟨hint, hbound⟩ :=
    integrable_and_integral_rpow_specNorm_inv_gaussianMatrix_le_sharp
      hr hrk' (p := (p : ℝ)) hpR (by linarith)
  simp_rw [Real.rpow_natCast] at hint hbound
  refine ⟨hint, hbound.trans ?_⟩
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hkR : (r : ℝ) < k := by exact_mod_cast hrk'
  have hC : 0 ≤ Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) /
      (2 * ((k : ℝ) - r) ^ 2) := by
    apply div_nonneg
    · exact mul_nonneg (sq_nonneg _) (by linarith)
    · positivity
  have hle : Real.exp 1 ^ 2 * ((k : ℝ) + r - 1) /
      (2 * ((k : ℝ) - r) ^ 2) ≤
      Real.exp 1 ^ 2 * ((k : ℝ) + r) / (2 * ((k : ℝ) - r) ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  exact pow_le_pow_left₀ hC hle p

end NLAlib
