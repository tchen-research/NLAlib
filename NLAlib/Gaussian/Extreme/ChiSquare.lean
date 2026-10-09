import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Chi-square lower tail and negative moments

For `X` a standard Gaussian vector in `ℝ^d`, `‖X‖² ∼ χ²_d`. This file provides

* `measure_sum_sq_le_le_gaussianReal`: the lower tail
  `P(χ²_d ≤ u) ≤ (e u / d)^{d/2}` for `0 ≤ u ≤ d` (atlas `chi-square-lower-tail`);
* `integrable_and_integral_rpow_inv_sum_sq_gaussianReal`: the negative moments
  `E[(χ²_d)^{-q}] = Γ(d/2 - q) / (2^q Γ(d/2))` for `0 ≤ q < d/2` (atlas `chi-square-neg-moment`);
* `integrable_and_integral_rpow_inv_sum_sq_gaussianReal_lt`: the `L^q` bound
  `E[(χ²_d)^{-(d-1)/2}] < (3/d)^{(d-1)/2}` for `d ≥ 5` (atlas `chi-square-neg-moment`,
  HMT 2011, Lemma A.10);
* `integrable_and_integral_inv_sum_sq_pow_two_gaussianReal`: `E[(χ²_d)^{-2}] = 1/((d-2)(d-4))`
  for `d ≥ 5` (atlas `inverse-chi-square-moment`);
* `integrable_and_integral_inv_sum_sq_gaussianReal`: the first inverse moment
  `E[1/χ²_d] = 1/(d-2)` for `d ≥ 3` (atlas `inverse-chi-square-moment`; `…_fin` is the `Fin d`
  form);

and the general-purpose helpers `integral_exp_neg_mul_sum_sq_pi_gaussianReal` (Laplace
transform of `χ²_d`), `ae_sum_sq_pos_pi_gaussianReal`, `lintegral_ofReal_mul_rpow_mul_exp_Ioi`
(Euler's integral in `lintegral` form) and `Gamma_add_half_le_mul_sqrt`.

Proof source: Prove2me workspace, Gaussian Random Matrices series (solutions
`chi_square_lower_tail`, `chi_square_neg_moment`, `inv_chi_square_Lq_bound`); the second inverse
moment is derived here from the negative-moment formula instead of the source's separate
Laplace-transform computation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace NLAlib

/-! ### Laplace transform of a chi-square variable -/

/-- One-dimensional Gaussian integral: `E[exp(-((u-1)/2) Y²)] = u^{-1/2}` for `Y ∼ N(0,1)`
and `u > 0`. Atlas: `chi-square-lower-tail` (helper). Ported from Prove2me solution
`GaussianMatrix.chi_square_neg_moment` (`cnm_gauss_exp`). -/
theorem integral_exp_neg_mul_sq_gaussianReal_eq_rpow (u : ℝ) (hu : 0 < u) :
    ∫ y, Real.exp (-((u - 1) / 2) * y ^ 2) ∂(gaussianReal 0 1) = u ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal_def, smul_eq_mul, NNReal.coe_one, sub_zero, mul_one]
  have h : ∀ x : ℝ, (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * rexp (-((u - 1) / 2) * x ^ 2)
      = (√(2 * π))⁻¹ * rexp (-(u / 2) * x ^ 2) := by
    intro x; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have h2 : π / (u / 2) = (2 * π) / u := by field_simp
  rw [h2, Real.sqrt_div (by positivity), Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have : √(2 * π) ≠ 0 := by positivity
  field_simp

/-- **Laplace transform of `χ²_d`.** For a standard Gaussian vector indexed by a finite type of
cardinality `d` and `u > 0`, `E[exp(-((u-1)/2) ∑ⱼ Xⱼ²)] = u^{-d/2}`.
Atlas: `chi-square-lower-tail` (helper). Ported from Prove2me solution
`GaussianMatrix.chi_square_neg_moment` (`cnm_laplace`). -/
theorem integral_exp_neg_mul_sum_sq_pi_gaussianReal {ι : Type*} [Fintype ι] (u : ℝ)
    (hu : 0 < u) :
    ∫ x : ι → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = u ^ (-((Fintype.card ι : ℝ) / 2)) := by
  have h : ∀ x : ι → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      = ∏ j, Real.exp (-((u - 1) / 2) * x j ^ 2) := by
    intro x; rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (fun _ y => Real.exp (-((u - 1) / 2) * y ^ 2))]
  simp only [integral_exp_neg_mul_sq_gaussianReal_eq_rpow u hu, Finset.prod_const,
    Finset.card_univ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  congr 1; ring

/-- A standard Gaussian vector of positive dimension is almost surely nonzero:
`∑ⱼ Xⱼ² > 0` a.s. Atlas: `chi-square-neg-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.chi_square_neg_moment` (`cnm_sum_pos_ae`). -/
theorem ae_sum_sq_pos_pi_gaussianReal {ι : Type*} [Fintype ι] (hd : 1 ≤ Fintype.card ι) :
    ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1), 0 < ∑ j, x j ^ 2 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hnull : (Measure.pi fun _ : ι => gaussianReal 0 1) (Function.eval i₀ ⁻¹' {0}) = 0 :=
    Measure.pi_eval_preimage_null _ (measure_singleton 0)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
  have hx0 : x i₀ ≠ 0 := by simpa using hx
  have h1 : x i₀ ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ _)
  have h2 : 0 < x i₀ ^ 2 := by positivity
  linarith

/-! ### Lower tail -/

/-- Chernoff bound for the lower tail of `χ²_d`:
`P(χ²_d ≤ u) ≤ e^{s u} (1 + 2s)^{-d/2}` for `s ≥ 0`. -/
private lemma measureReal_sum_sq_le_le_exp_mul {d : ℕ} (u s : ℝ) (hs : 0 ≤ s) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real {g | ∑ i, g i ^ 2 ≤ u}
      ≤ Real.exp (s * u) * (1 + 2 * s) ^ (-((d : ℝ) / 2)) := by
  set μ := Measure.pi fun _ : Fin d => gaussianReal 0 1
  have hint : Integrable (fun g : Fin d → ℝ => Real.exp (-s * ∑ i, g i ^ 2)) μ := by
    refine Integrable.mono' (integrable_const (1:ℝ)) ?_ ?_
    · exact (by fun_prop : Measurable (fun g : Fin d → ℝ =>
        Real.exp (-s * ∑ i, g i ^ 2))).aestronglyMeasurable
    · refine ae_of_all _ fun g => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith
  have h := measure_le_le_exp_mul_mgf (X := fun g : Fin d → ℝ => ∑ i, g i ^ 2) (μ := μ) u
    (neg_nonpos.mpr hs) hint
  have hmgf : mgf (fun g : Fin d → ℝ => ∑ i, g i ^ 2) μ (-s)
      = (1 + 2 * s) ^ (-((d : ℝ) / 2)) := by
    have := integral_exp_neg_mul_sum_sq_pi_gaussianReal (ι := Fin d) (1 + 2 * s) (by linarith)
    rw [show -((1 + 2 * s - 1) / 2) = -s by ring, Fintype.card_fin] at this
    exact this
  rw [hmgf, neg_neg] at h
  exact h

/-- **Chi-square lower tail.** For `d ≥ 1` and `0 ≤ u ≤ d`, a `χ²_d` variable satisfies
`P(χ²_d ≤ u) ≤ (e u / d)^{d/2}`.

Chernoff bound with the optimal parameter `s = (d/u - 1)/2`; Davidson–Szarek 2001 / Vershynin
2012 (small-ball step for `σ_min`); Laurent–Massart 2000 give the sharper form.
Atlas: `chi-square-lower-tail`. Ported from Prove2me solution
`GaussianMatrix.chi_square_lower_tail`. -/
theorem measure_sum_sq_le_le_gaussianReal {d : ℕ} (hd : 1 ≤ d) (u : ℝ) (hu : 0 ≤ u)
    (hud : u ≤ d) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1) {g | ∑ i, g i ^ 2 ≤ u}
      ≤ ENNReal.ofReal ((Real.exp 1 * u / d) ^ ((d : ℝ) / 2)) := by
  rcases hu.eq_or_lt with rfl | hu0
  · -- `u = 0`: the event forces `g = 0`, a null set.
    have hnull : (Measure.pi fun _ : Fin d => gaussianReal 0 1)
        {g : Fin d → ℝ | ∑ i, g i ^ 2 ≤ 0} = 0 := measure_eq_zero_iff_ae_notMem.mpr
      ((ae_sum_sq_pos_pi_gaussianReal (ι := Fin d) (by simpa using hd)).mono
        fun g hg hmem => (not_le.mpr hg) hmem)
    rw [hnull]
    exact zero_le
  · set s := ((d:ℝ) / u - 1) / 2 with hs_def
    have hdu : 1 ≤ (d:ℝ) / u := by rw [le_div_iff₀ hu0]; linarith
    have hs : 0 ≤ s := by rw [hs_def]; linarith
    have h1 : 1 + 2 * s = (d:ℝ) / u := by rw [hs_def]; ring
    have hsu : s * u = ((d:ℝ) - u) / 2 := by rw [hs_def]; field_simp
    have hch := measureReal_sum_sq_le_le_exp_mul (d := d) u s hs
    rw [h1, hsu, Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div] at hch
    have hrhs : (Real.exp 1 * u / d) ^ ((d : ℝ) / 2)
        = Real.exp ((d:ℝ) / 2) * (u / d) ^ ((d:ℝ) / 2) := by
      rw [mul_div_assoc, Real.mul_rpow (Real.exp_pos 1).le (by positivity), Real.exp_one_rpow]
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    refine hch.trans ?_
    rw [hrhs]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact Real.exp_le_exp.mpr (by linarith)

/-! ### Negative moments -/

/-- **Euler's integral in `lintegral` form**: `∫₀^∞ c t^{a-1} e^{-rt} dt = c (1/r)^a Γ(a)` for
`a, r > 0` and `c ≥ 0`. Atlas: `chi-square-neg-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.chi_square_neg_moment` (`cnm_gamma_lintegral`). -/
theorem lintegral_ofReal_mul_rpow_mul_exp_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (c : ℝ)
    (hc : 0 ≤ c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c * (t ^ (a - 1) * Real.exp (-(r * t))))
      = ENNReal.ofReal (c * ((1 / r) ^ a * Gamma a)) := by
  have hI := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  have hpos : 0 < (1 / r) ^ a * Gamma a := by
    have : 0 < Gamma a := Gamma_pos_of_pos ha
    positivity
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hI]; exact hpos.ne')
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul c), integral_const_mul, hI]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have : 0 ≤ t ^ (a - 1) := Real.rpow_nonneg ht0.le _
  positivity

/-- The negative moment of a chi-square variable, in `lintegral` form. -/
private lemma lintegral_rpow_inv_sum_sq_gaussianReal {d : ℕ} (q : ℝ) (hq : 0 < q)
    (hqd : q < (d : ℝ) / 2) :
    ∫⁻ x, ENNReal.ofReal (((∑ j, x j ^ 2)⁻¹) ^ q) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = ENNReal.ofReal (Gamma ((d : ℝ) / 2 - q) / (2 ^ q * Gamma ((d : ℝ) / 2))) := by
  set μ := Measure.pi fun _ : Fin d => gaussianReal 0 1 with hμ
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hqd; linarith
    · exact h
  have hx0 : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hGq : 0 < Gamma q := Gamma_pos_of_pos hq
  have hGd : 0 < Gamma ((d : ℝ) / 2) := Gamma_pos_of_pos hx0
  set S : (Fin d → ℝ) → ℝ := fun x => ∑ j, x j ^ 2 with hS
  -- step 1: Euler representation of `S^{-q}`
  set K : (Fin d → ℝ) → ℝ → ENNReal :=
    fun x v => ENNReal.ofReal ((Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v)))) with hK
  have step1 : ∀ᵐ x ∂μ, ENNReal.ofReal (((∑ j, x j ^ 2)⁻¹) ^ q) = ∫⁻ v in Ioi 0, K x v := by
    filter_upwards [ae_sum_sq_pos_pi_gaussianReal (ι := Fin d) (by simpa using hd1)] with x hx
    simp only [hK]
    rw [lintegral_ofReal_mul_rpow_mul_exp_Ioi hq hx (Gamma q)⁻¹ (inv_nonneg.mpr hGq.le)]
    congr 1
    rw [one_div]
    field_simp
  rw [lintegral_congr_ae step1]
  have hKm : Measurable (Function.uncurry K) := by
    simp only [hK, hS]
    fun_prop
  rw [lintegral_lintegral_swap hKm.aemeasurable]
  -- step 2: integrate out `x` (Laplace transform)
  have step2 : ∀ v ∈ Ioi (0 : ℝ), ∫⁻ x, K x v ∂μ
      = ENNReal.ofReal ((Gamma q)⁻¹ * v ^ (q - 1) * (1 + 2 * v) ^ (-((d : ℝ) / 2))) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have hc : 0 ≤ (Gamma q)⁻¹ * v ^ (q - 1) :=
      mul_nonneg (inv_nonneg.mpr hGq.le) (Real.rpow_nonneg hv0.le _)
    have hmeas : Measurable fun x => (Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v))) := by
      simp only [hS]; fun_prop
    have hint : Integrable (fun x => (Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v)))) μ := by
      refine (integrable_const ((Gamma q)⁻¹ * v ^ (q - 1))).mono' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      have hSx : 0 ≤ S x := Finset.sum_nonneg fun j _ => sq_nonneg _
      have he : Real.exp (-(S x * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v)))
          = ((Gamma q)⁻¹ * v ^ (q - 1)) * Real.exp (-(S x * v)) := by ring
        _ ≤ ((Gamma q)⁻¹ * v ^ (q - 1)) * 1 := by gcongr
        _ = _ := mul_one _
    simp only [hK]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1
    have hlap := integral_exp_neg_mul_sum_sq_pi_gaussianReal (ι := Fin d) (1 + 2 * v)
      (by linarith)
    rw [Fintype.card_fin] at hlap
    have hfun : ∀ x : Fin d → ℝ, (Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v)))
        = ((Gamma q)⁻¹ * v ^ (q - 1)) *
          Real.exp (-((1 + 2 * v - 1) / 2) * ∑ j, x j ^ 2) := by
      intro x; simp only [hS]; ring_nf
    simp_rw [hfun]
    rw [integral_const_mul, hlap]
  rw [setLIntegral_congr_fun measurableSet_Ioi step2]
  -- step 3: Euler representation of `(1+2v)^{-d/2}`
  set Gd := Gamma ((d : ℝ) / 2) with hGd'
  set L : ℝ → ℝ → ENNReal := fun v w => ENNReal.ofReal
    ((Gamma q)⁻¹ * v ^ (q - 1) * Gd⁻¹ * (w ^ ((d : ℝ) / 2 - 1) * Real.exp (-((1 + 2 * v) * w))))
    with hL
  have step3 : ∀ v ∈ Ioi (0 : ℝ),
      ENNReal.ofReal ((Gamma q)⁻¹ * v ^ (q - 1) * (1 + 2 * v) ^ (-((d : ℝ) / 2)))
        = ∫⁻ w in Ioi 0, L v w := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have h12 : (0 : ℝ) < 1 + 2 * v := by linarith
    simp only [hL]
    rw [lintegral_ofReal_mul_rpow_mul_exp_Ioi hx0 h12 _ (by
      have := Real.rpow_nonneg hv0.le (q - 1); positivity)]
    congr 1
    rw [one_div, Real.inv_rpow h12.le, ← Real.rpow_neg h12.le]
    field_simp
    exact hGd'
  rw [setLIntegral_congr_fun measurableSet_Ioi step3]
  have hLm : Measurable (Function.uncurry L) := by
    simp only [hL]
    fun_prop
  rw [lintegral_lintegral_swap hLm.aemeasurable]
  -- step 4: integrate out `v`
  have step4 : ∀ w ∈ Ioi (0 : ℝ), ∫⁻ v in Ioi 0, L v w
      = ENNReal.ofReal ((Gd⁻¹ * (2 ^ q)⁻¹) *
          (w ^ ((d : ℝ) / 2 - q - 1) * Real.exp (-(1 * w)))) := by
    intro w hw
    have hw0 : (0 : ℝ) < w := hw
    have hfun : ∀ v : ℝ, L v w = ENNReal.ofReal
        (((Gamma q)⁻¹ * Gd⁻¹ * w ^ ((d : ℝ) / 2 - 1) * Real.exp (-w)) *
          (v ^ (q - 1) * Real.exp (-((2 * w) * v)))) := by
      intro v
      simp only [hL]
      congr 1
      have : Real.exp (-((1 + 2 * v) * w)) = Real.exp (-w) * Real.exp (-((2 * w) * v)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; ring
    simp_rw [hfun]
    rw [lintegral_ofReal_mul_rpow_mul_exp_Ioi hq (by positivity) _ (by
      have := Real.rpow_nonneg hw0.le ((d : ℝ) / 2 - 1); positivity)]
    congr 1
    have h1 : (1 / (2 * w)) ^ q = (2 ^ q)⁻¹ * w ^ (-q) := by
      rw [one_div, Real.inv_rpow (by positivity), Real.mul_rpow (by norm_num) hw0.le,
        Real.rpow_neg hw0.le, mul_inv]
    have h2 : w ^ ((d : ℝ) / 2 - 1) * w ^ (-q) = w ^ ((d : ℝ) / 2 - q - 1) := by
      rw [← Real.rpow_add hw0]; congr 1; ring
    rw [h1, one_mul]
    calc (Gamma q)⁻¹ * Gd⁻¹ * w ^ ((d : ℝ) / 2 - 1) * Real.exp (-w) *
          ((2 ^ q)⁻¹ * w ^ (-q) * Gamma q)
        = ((Gamma q)⁻¹ * Gamma q) * Gd⁻¹ * (2 ^ q)⁻¹ *
          (w ^ ((d : ℝ) / 2 - 1) * w ^ (-q)) * Real.exp (-w) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hGq.ne', h2]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi step4]
  -- step 5: the last Gamma integral
  have ha : (0 : ℝ) < (d : ℝ) / 2 - q := by linarith
  rw [lintegral_ofReal_mul_rpow_mul_exp_Ioi ha one_pos _ (by positivity)]
  congr 1
  rw [div_one, Real.one_rpow, one_mul]
  field_simp

/-- **Negative moments of a chi-square variable.** For `0 ≤ q < d/2`, `(χ²_d)^{-q}` is
integrable and `E[(χ²_d)^{-q}] = Γ(d/2 - q) / (2^q Γ(d/2))`.

Standard Gamma-integral computation (e.g. HMT 2011, proof of Lemma A.10; Johnson–Kotz–
Balakrishnan, ch. 18). Proof: Euler representation of `S^{-q}` and of `(1 + 2v)^{-d/2}`, Tonelli,
and the Laplace transform of `χ²_d`. Atlas: `chi-square-neg-moment`. Ported from Prove2me
solution `GaussianMatrix.chi_square_neg_moment`. -/
theorem integrable_and_integral_rpow_inv_sum_sq_gaussianReal {d : ℕ} (q : ℝ) (hq : 0 ≤ q)
    (hqd : q < (d : ℝ) / 2) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ q)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ q ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = Real.Gamma ((d : ℝ) / 2 - q) / (2 ^ q * Real.Gamma ((d : ℝ) / 2)) := by
  rcases hq.eq_or_lt with h0 | hq0
  · subst h0
    have hx0 : (0 : ℝ) < (d : ℝ) / 2 := hqd
    have hG := (Real.Gamma_pos_of_pos hx0).ne'
    simp only [Real.rpow_zero, sub_zero, one_mul]
    refine ⟨integrable_const _, ?_⟩
    rw [integral_const]
    simp [hG]
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin d => gaussianReal 0 1]
      (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ q) :=
    Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)) _
  have hmeas : Measurable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ q) := by fun_prop
  have hx0 : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hpos : (0 : ℝ) ≤ Real.Gamma ((d : ℝ) / 2 - q) / (2 ^ q * Real.Gamma ((d : ℝ) / 2)) := by
    have := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < (d : ℝ) / 2 - q)
    have := Real.Gamma_pos_of_pos hx0
    positivity
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, lintegral_rpow_inv_sum_sq_gaussianReal q hq0 hqd]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable,
      lintegral_rpow_inv_sum_sq_gaussianReal q hq0 hqd, ENNReal.toReal_ofReal hpos]

/-! ### The `L^{(d-1)/2}` bound (HMT Lemma A.10) -/

/-- `Γ(x + 1/2) ≤ Γ(x) √x` for `x > 0` (log-convexity of `Γ`, Bohr–Mollerup).
Atlas: `chi-square-neg-moment` (helper). Ported from Prove2me solution
`GaussianMatrix.inv_chi_square_Lq_bound` (`icl_Gamma_add_half_le`). -/
theorem Gamma_add_half_le_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Gamma (x + 1 / 2) ≤ Gamma x * √x := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx (by linarith : 0 < x + 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hG : 0 < Gamma x := Gamma_pos_of_pos hx
  rw [show 1 / 2 * x + 1 / 2 * (x + 1) = x + 1 / 2 by ring, Gamma_add_one hx.ne',
    ← Real.mul_rpow hG.le (by positivity), ← Real.sqrt_eq_rpow,
    show Gamma x * (x * Gamma x) = Gamma x ^ 2 * x by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hG.le] at h
  exact h

/-- `e^n · 3 < 2 · 3^n` for `n ≥ 5`. -/
private lemma exp_one_pow_mul_three_lt {n : ℕ} (hn : 5 ≤ n) :
    Real.exp 1 ^ n * 3 < 2 * 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have he3 : Real.exp 1 ≤ 3 := by linarith
  have h5 : Real.exp 1 ^ 5 * 3 < 2 * 3 ^ 5 := by
    have : Real.exp 1 ^ 5 < 2.7182818286 ^ 5 := pow_lt_pow_left₀ he he0.le (by norm_num)
    have : (2.7182818286 : ℝ) ^ 5 * 3 < 2 * 3 ^ 5 := by norm_num
    nlinarith
  have hm : Real.exp 1 ^ m ≤ 3 ^ m := pow_le_pow_left₀ he0.le he3 m
  rw [pow_add, pow_add]
  have : 0 < Real.exp 1 ^ 5 := by positivity
  have : (0 : ℝ) < 3 ^ m := by positivity
  nlinarith

/-- The Gamma-function inequality behind HMT Lemma A.10:
`√π / (2^q Γ(n/2)) < (3/n)^q` for `q = (n-1)/2`, `n ≥ 5`. -/
private lemma sqrt_pi_div_lt_rpow {n : ℕ} (hn : 5 ≤ n) :
    √π / (2 ^ (((n : ℝ) - 1) / 2) * Gamma ((n : ℝ) / 2))
      < (3 / (n : ℝ)) ^ (((n : ℝ) - 1) / 2) := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set x : ℝ := (n : ℝ) / 2 with hx
  have hx0 : 0 < x := by positivity
  set q : ℝ := ((n : ℝ) - 1) / 2 with hq
  set G := Gamma x with hGdef
  have hG : 0 < G := Gamma_pos_of_pos hx0
  set s := √x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  set sp := √π with hsp
  have hspsq : sp ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have F1 : Gamma (x + 1 / 2) ≤ G * s := Gamma_add_half_le_mul_sqrt hx0
  have F2 : G * Gamma (x + 1 / 2) = Gamma n * (2 : ℝ) ^ (1 - (n : ℝ)) * sp := by
    rw [hGdef, Real.Gamma_mul_Gamma_add_half, hx, show 2 * ((n : ℝ) / 2) = n by ring]
  have F3 : (n : ℝ) * Gamma n = (n.factorial : ℝ) := by
    rw [← Real.Gamma_add_one hn0.ne', Real.Gamma_nat_eq_factorial]
  have F4 := Stirling.le_factorial_stirling n
  have F5 : √(2 * π * n) = 2 * sp * s := by
    rw [show 2 * π * (n : ℝ) = 2 ^ 2 * π * x by rw [hx]; ring, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have F6 := exp_one_pow_mul_three_lt hn
  have F7 : (2 : ℝ) ^ (1 - (n : ℝ)) * 2 ^ n = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    norm_num
  have hen : Real.exp 1 ^ n > 0 := by positivity
  have hdivpow : ((n : ℝ) / Real.exp 1) ^ n = (n : ℝ) ^ n / Real.exp 1 ^ n := div_pow _ _ _
  have h1 : G * Gamma (x + 1 / 2) ≤ G ^ 2 * s := by
    have := mul_le_mul_of_nonneg_left F1 hG.le; nlinarith
  have h3 : (n.factorial : ℝ) * sp * 2 ≤ n * 2 ^ n * G ^ 2 * s := by
    have h2 : Gamma n * (2 : ℝ) ^ (1 - (n : ℝ)) * sp ≤ G ^ 2 * s := F2 ▸ h1
    have hpos : (0 : ℝ) ≤ n * 2 ^ n := by positivity
    have := mul_le_mul_of_nonneg_left h2 hpos
    calc (n.factorial : ℝ) * sp * 2
        = (n * Gamma n) * ((2 : ℝ) ^ (1 - (n : ℝ)) * 2 ^ n) * sp := by rw [F3, F7]; ring
      _ = n * 2 ^ n * (Gamma n * (2 : ℝ) ^ (1 - (n : ℝ)) * sp) := by ring
      _ ≤ n * 2 ^ n * (G ^ 2 * s) := this
      _ = n * 2 ^ n * G ^ 2 * s := by ring
  have h4 : 2 * sp * s * ((n : ℝ) ^ n / Real.exp 1 ^ n) ≤ n.factorial := by
    rw [← F5, ← hdivpow]; exact F4
  have h5 : 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * s ≤ n * 2 ^ n * G ^ 2 * s := by
    calc 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * s
        = (2 * sp * s * ((n : ℝ) ^ n / Real.exp 1 ^ n)) * sp * 2 := by rw [← hspsq]; ring
      _ ≤ (n.factorial : ℝ) * sp * 2 := by gcongr
      _ ≤ _ := h3
  have h6 : 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) ≤ n * 2 ^ n * G ^ 2 :=
    le_of_mul_le_mul_right h5 hs0
  have hnn : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  have key : 6 * π * (n : ℝ) ^ n < n * 6 ^ n * G ^ 2 := by
    have h7 : 6 * π * (n : ℝ) ^ n < 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * 3 ^ n := by
      rw [show 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * 3 ^ n
        = (π * (n : ℝ) ^ n) * (2 * (2 * 3 ^ n)) / Real.exp 1 ^ n by ring]
      rw [lt_div_iff₀ hen]
      have hpn : 0 < π * (n : ℝ) ^ n := by positivity
      nlinarith
    calc 6 * π * (n : ℝ) ^ n < 4 * π * ((n : ℝ) ^ n / Real.exp 1 ^ n) * 3 ^ n := h7
      _ ≤ n * 2 ^ n * G ^ 2 * 3 ^ n := by gcongr
      _ = n * 6 ^ n * G ^ 2 := by
        rw [show (6 : ℝ) ^ n = 2 ^ n * 3 ^ n by rw [← mul_pow]; norm_num]; ring
  have h2q : 2 * q = (n : ℝ) - 1 := by rw [hq]; ring
  have hsq : ∀ a : ℝ, 0 < a → (a ^ q) ^ 2 = a ^ n / a := by
    intro a ha
    rw [← Real.rpow_natCast (a ^ q) 2, ← Real.rpow_mul ha.le, show q * ((2 : ℕ) : ℝ) = 2 * q by
      push_cast; ring, h2q, Real.rpow_sub_one ha.ne', Real.rpow_natCast a n]
  have hA : sp * (n : ℝ) ^ q < (6 : ℝ) ^ q * G := by
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    rw [mul_pow, mul_pow, hspsq, hsq _ hn0, hsq 6 (by norm_num)]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have : π * ((n : ℝ) ^ n * (n : ℝ)⁻¹) = (6 * π * (n : ℝ) ^ n) * (6 * (n : ℝ))⁻¹ := by
      field_simp
    rw [this, show (6 : ℝ) ^ n * 6⁻¹ * G ^ 2 = (n * 6 ^ n * G ^ 2) * (6 * (n : ℝ))⁻¹ by
      field_simp]
    exact mul_lt_mul_of_pos_right key (by positivity)
  rw [div_lt_iff₀ (by positivity), Real.div_rpow (by norm_num) hn0.le]
  rw [show (3 : ℝ) ^ q / (n : ℝ) ^ q * (2 ^ q * G) = ((2 : ℝ) ^ q * 3 ^ q) * G / (n : ℝ) ^ q by
    ring, ← Real.mul_rpow (by norm_num) (by norm_num), lt_div_iff₀ (by positivity)]
  norm_num
  linarith

/-- **`L^{(d-1)/2}` bound for the inverse chi-square.** For `d ≥ 5`,
`(χ²_d)^{-(d-1)/2}` is integrable and `E[(χ²_d)^{-(d-1)/2}] < (3/d)^{(d-1)/2}`.

HMT 2011, Lemma A.10 (the moment step of the pseudoinverse Frobenius tail bound): the negative
moment formula with `q = (d-1)/2`, then `Γ(1/2) = √π`, the duplication formula, log-convexity
of `Γ` and Stirling. Atlas: `chi-square-neg-moment`. Ported from Prove2me solution
`GaussianMatrix.inv_chi_square_Lq_bound`. -/
theorem integrable_and_integral_rpow_inv_sum_sq_gaussianReal_lt {d : ℕ} (hd : 5 ≤ d) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2))
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      < (3 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hint, hval⟩ := integrable_and_integral_rpow_inv_sum_sq_gaussianReal (d := d)
    (((d : ℝ) - 1) / 2) (by linarith) (by linarith)
  refine ⟨hint, ?_⟩
  rw [hval, show (d : ℝ) / 2 - ((d : ℝ) - 1) / 2 = 1 / 2 by ring, Real.Gamma_one_half_eq]
  exact sqrt_pi_div_lt_rpow hd

/-! ### The second inverse moment -/

/-- **Second inverse moment of a chi-square variable.** For `d ≥ 5`, `(χ²_d)^{-2}` is integrable
and `E[(χ²_d)^{-2}] = 1/((d-2)(d-4))`.

Used for the inverse-Wishart second moments (Tropp–Webber 2023, App. B; HMT 2011, Prop A.6 /
Lemma A.9). Atlas: `inverse-chi-square-moment`. The source proves it by a separate
Laplace-transform computation (Prove2me solution `GaussianMatrix.inv_sq_chi_square_moment`);
here it is the case `q = 2` of `integrable_and_integral_rpow_inv_sum_sq_gaussianReal`, using
`Γ(d/2) = (d/2 - 1)(d/2 - 2) Γ(d/2 - 2)`. -/
theorem integrable_and_integral_inv_sum_sq_pow_two_gaussianReal {d : ℕ} (hd : 5 ≤ d) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ 2)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = 1 / (((d : ℝ) - 2) * ((d : ℝ) - 4)) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hint, hval⟩ := integrable_and_integral_rpow_inv_sum_sq_gaussianReal (d := d) 2
    (by norm_num) (by linarith)
  simp only [Real.rpow_two] at hint hval
  refine ⟨hint, ?_⟩
  rw [hval]
  have ha : (0 : ℝ) < (d : ℝ) / 2 - 2 := by linarith
  have hG : 0 < Gamma ((d : ℝ) / 2 - 2) := Gamma_pos_of_pos ha
  have hGd : Gamma ((d : ℝ) / 2) = ((d : ℝ) / 2 - 1) * (((d : ℝ) / 2 - 2) *
      Gamma ((d : ℝ) / 2 - 2)) := by
    calc Gamma ((d : ℝ) / 2) = Gamma (((d : ℝ) / 2 - 1) + 1) := by congr 1; ring
      _ = ((d : ℝ) / 2 - 1) * Gamma ((d : ℝ) / 2 - 1) := Real.Gamma_add_one (by linarith)
      _ = ((d : ℝ) / 2 - 1) * Gamma (((d : ℝ) / 2 - 2) + 1) := by congr 2; ring
      _ = _ := by rw [Real.Gamma_add_one ha.ne']
  rw [hGd]
  have h1 : (d : ℝ) - 2 ≠ 0 := by linarith
  have h2 : (d : ℝ) - 4 ≠ 0 := by linarith
  have h3 : (0 : ℝ) < (d : ℝ) / 2 - 1 := by linarith
  rw [div_eq_div_iff (by positivity) (mul_ne_zero h1 h2)]
  ring

/-! ### The first inverse moment -/

/-- `1/S = ∫_1^∞ exp(-((u-1)/2) S)/2 du` for `S > 0`. -/
private lemma integrableOn_and_integral_exp_eq_inv (S : ℝ) (hS : 0 < S) :
    IntegrableOn (fun u : ℝ => Real.exp (-((u - 1) / 2) * S) / 2) (Ioi 1) ∧
    ∫ u in Ioi 1, Real.exp (-((u - 1) / 2) * S) / 2 = S⁻¹ := by
  have h : ∀ u : ℝ, Real.exp (-((u - 1) / 2) * S) / 2
      = Real.exp ((-(S / 2)) * u) * (Real.exp (S / 2) / 2) := by
    intro u; rw [mul_div_assoc', ← Real.exp_add]; congr 2; ring
  simp_rw [h]
  have hneg : -(S / 2) < 0 := by linarith
  refine ⟨(integrableOn_exp_mul_Ioi hneg 1).mul_const _, ?_⟩
  rw [integral_mul_const, integral_exp_mul_Ioi hneg]
  have he : rexp (-(S / 2)) * rexp (S / 2) = 1 := by rw [← Real.exp_add]; simp
  have hS0 : S ≠ 0 := hS.ne'
  rw [mul_one, show -rexp (-(S / 2)) / -(S / 2) * (rexp (S / 2) / 2)
    = (rexp (-(S / 2)) * rexp (S / 2)) / S by field_simp, he, one_div]

private lemma lintegral_inv_sum_sq_gaussianReal {ι : Type*} [Fintype ι]
    (hd : 3 ≤ Fintype.card ι) :
    ∫⁻ x, ENNReal.ofReal (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      = ENNReal.ofReal (1 / ((Fintype.card ι : ℝ) - 2)) := by
  set d := Fintype.card ι with hdd
  set μ := Measure.pi fun _ : ι => gaussianReal 0 1 with hμ
  set K : (ι → ℝ) → ℝ → ℝ := fun x u => Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2) / 2 with hK
  have hK_cont : Continuous (Function.uncurry K) := by
    simp only [hK]; fun_prop
  -- step 1: inner representation
  have step1 : ∀ᵐ x ∂μ, ENNReal.ofReal (∑ j, x j ^ 2)⁻¹
      = ∫⁻ u in Ioi 1, ENNReal.ofReal (K x u) := by
    filter_upwards [ae_sum_sq_pos_pi_gaussianReal (ι := ι) (by omega)] with x hx
    obtain ⟨hint, hval⟩ := integrableOn_and_integral_exp_eq_inv _ hx
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u => by positivity)]
  rw [lintegral_congr_ae step1]
  rw [lintegral_lintegral_swap (hK_cont.measurable.ennreal_ofReal.aemeasurable)]
  -- step 2: inner integral over x
  have step2 : ∀ u ∈ Ioi (1 : ℝ), ∫⁻ x, ENNReal.ofReal (K x u) ∂μ
      = ENNReal.ofReal (u ^ (-((d : ℝ) / 2)) / 2) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have hmeas : Measurable fun x => K x u :=
      (hK_cont.comp (Continuous.prodMk_left u)).measurable
    have hint : Integrable (fun x => K x u) μ := by
      refine (integrable_const (1 / 2 : ℝ)).mono' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hS : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      have : -((u - 1) / 2) * ∑ j, x j ^ 2 ≤ 0 := by
        have : 0 ≤ (u - 1) / 2 := by have := hu.out; linarith
        nlinarith
      have := Real.exp_le_one_iff.mpr this
      simp only [hK]; linarith
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1
    simp only [hK]
    rw [integral_div, integral_exp_neg_mul_sum_sq_pi_gaussianReal u hu0]
  rw [setLIntegral_congr_fun measurableSet_Ioi step2]
  -- step 3: the outer integral
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : -((d : ℝ) / 2) < -1 := by linarith
  have hint3 : IntegrableOn (fun u : ℝ => u ^ (-((d : ℝ) / 2)) / 2) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha one_pos).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint3]
  · congr 1
    rw [integral_div, integral_Ioi_rpow_of_lt ha one_pos, Real.one_rpow]
    have : (d : ℝ) - 2 ≠ 0 := by linarith
    have : -((d : ℝ) / 2) + 1 ≠ 0 := by linarith
    have : (2 : ℝ) - d ≠ 0 := by linarith
    field_simp
    linear_combination inv_mul_cancel₀ this
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    positivity

/-- **Inverse chi-square moment.** If `X` is a standard Gaussian vector indexed by a finite type
`ι` with `d = |ι| ≥ 3`, then `1/‖X‖²` is integrable and `E[1/‖X‖²] = E[1/χ²_d] = 1/(d - 2)`.

Tropp–Webber 2023, Lemma B.2 (scalar step); HMT 2011, proof of Prop 10.2 / Prop A.5
(`E[1/χ²_d] = 1/(d-2)`). Atlas: `inverse-chi-square-moment`. The source states it for
`ι = Fin d` (see `integrable_and_integral_inv_sum_sq_gaussianReal_fin`). Proof ported from the
Prove2me solution `Sol_GaussianMatrix_inv_chi_square_moment` (Laplace-transform representation
of `1/S`); moved here from `NLAlib.Gaussian.InverseMoments`. -/
theorem integrable_and_integral_inv_sum_sq_gaussianReal {ι : Type*} [Fintype ι]
    (hd : 3 ≤ Fintype.card ι) :
    Integrable (fun x : ι → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      = 1 / ((Fintype.card ι : ℝ) - 2) := by
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1]
      (fun x : ι → ℝ => (∑ j, x j ^ 2)⁻¹) :=
    Filter.Eventually.of_forall fun x =>
      inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hmeas : Measurable (fun x : ι → ℝ => (∑ j, x j ^ 2)⁻¹) := by fun_prop
  have hpos : (0 : ℝ) ≤ 1 / ((Fintype.card ι : ℝ) - 2) := by
    have : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
    apply div_nonneg zero_le_one; linarith
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, lintegral_inv_sum_sq_gaussianReal hd]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable,
      lintegral_inv_sum_sq_gaussianReal hd, ENNReal.toReal_ofReal hpos]

/-- **Inverse chi-square moment**, source form over `Fin d`: for `d ≥ 3`,
`E[1/χ²_d] = 1/(d - 2)`.

Tropp–Webber 2023, Lemma B.2 (scalar step); HMT 2011, proof of Prop 10.2.
Atlas: `inverse-chi-square-moment`. Ported from the Prove2me solution
`Sol_GaussianMatrix_inv_chi_square_moment`. -/
theorem integrable_and_integral_inv_sum_sq_gaussianReal_fin {d : ℕ} (hd : 3 ≤ d) :
    Integrable (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = 1 / ((d : ℝ) - 2) := by
  simpa using integrable_and_integral_inv_sum_sq_gaussianReal (ι := Fin d) (by simpa using hd)

end NLAlib
