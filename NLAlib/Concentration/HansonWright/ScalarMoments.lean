/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Ported from HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae,
HighDimProb/Concentration/HansonWright.lean, to Lean 4.33.1.
The original Apache-2.0 copyright notice is retained. Only the two used legacy
vocabulary definitions are supplied locally; there is no HighDimProb dependency.
-/
import NLAlib.Matrix.Norms
import NLAlib.Concentration.OrliczMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import NLAlib.Concentration.HansonWright.CutAverages

/-!
# Hanson–Wright proof: ScalarMoments

A focused leaf of the transported independent-coordinate proof.
Shared helper declarations live in `NLAlib.HansonWrightProof`; the canonical
public bounds are in `NLAlib.Concentration.HansonWright`.
Atlas: `hanson-wright`. Source: HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal Matrix.Norms.L2Operator

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib
namespace HansonWrightProof

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A self-contained bounded, centered MGF estimate.

This is the symmetric bounded-variable form of Hoeffding's lemma, proved locally
from the chord bound for `exp` and `cosh x ≤ exp (x² / 2)`. -/
lemma hasSubgaussianMGF_of_abs_le_of_integral_eq_zero {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {R : ℝ}
    (hY_meas : AEMeasurable Y μ) (hR : 0 ≤ R)
    (hY_bound : ∀ᵐ ω ∂μ, |Y ω| ≤ R) (hY_center : ∫ ω, Y ω ∂μ = 0) :
    HasSubgaussianMGF Y ⟨R ^ 2, sq_nonneg R⟩ μ := by
  have hY_range : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-R) R := by
    filter_upwards [hY_bound] with ω hω
    exact abs_le.mp hω
  have hY_int : Integrable Y μ := Integrable.of_mem_Icc (-R) R hY_meas hY_range
  refine ⟨?_, ?_⟩
  · intro t
    exact integrable_exp_mul_of_mem_Icc hY_meas hY_range
  · intro t
    by_cases hR0 : R = 0
    · have hY_zero : Y =ᵐ[μ] 0 := by
        filter_upwards [hY_bound] with ω hω
        rw [hR0] at hω
        exact abs_eq_zero.mp (le_antisymm hω (abs_nonneg _))
      have hmgf : mgf Y μ t = 1 := by
        unfold mgf
        calc ∫ ω, exp (t * Y ω) ∂μ
            = ∫ _ω, (1 : ℝ) ∂μ := by
                apply integral_congr_ae
                filter_upwards [hY_zero] with ω hω
                simp [hω]
          _ = 1 := by simp
      rw [hmgf, hR0]
      apply one_le_exp
      exact div_nonneg (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg t)) (by norm_num)
    · have hR_pos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
      let chord : Ω → ℝ := fun ω =>
        ((R - Y ω) / (2 * R)) * exp (t * (-R)) +
          ((Y ω + R) / (2 * R)) * exp (t * R)
      have hchord_int : Integrable chord μ := by
        dsimp [chord]
        exact ((((integrable_const R).sub hY_int).div_const (2 * R)).mul_const _).add
          (((hY_int.add (integrable_const R)).div_const (2 * R)).mul_const _)
      have hpoint : (fun ω => exp (t * Y ω)) ≤ᵐ[μ] chord := by
        filter_upwards [hY_range] with ω hω
        exact exp_le_chord hR_pos hω
      have hmono : mgf Y μ t ≤ ∫ ω, chord ω ∂μ := by
        unfold mgf
        exact integral_mono_ae (integrable_exp_mul_of_mem_Icc hY_meas hY_range)
          hchord_int hpoint
      have hleft_int :
          Integrable (fun ω => (R - Y ω) / (2 * R) * exp (t * (-R))) μ :=
        (((integrable_const R).sub hY_int).div_const (2 * R)).mul_const _
      have hright_int :
          Integrable (fun ω => (Y ω + R) / (2 * R) * exp (t * R)) μ :=
        ((hY_int.add (integrable_const R)).div_const (2 * R)).mul_const _
      have hchord_eq : ∫ ω, chord ω ∂μ = cosh (t * R) := by
        change ∫ ω, ((R - Y ω) / (2 * R) * exp (t * (-R)) +
          (Y ω + R) / (2 * R) * exp (t * R)) ∂μ = cosh (t * R)
        rw [integral_add hleft_int hright_int]
        rw [integral_mul_const, integral_mul_const]
        rw [integral_div, integral_div]
        rw [integral_sub (integrable_const R) hY_int,
          integral_add hY_int (integrable_const R)]
        simp [hY_center, Real.cosh_eq, mul_comm]
        field_simp [hR_pos.ne']
        ring
      calc mgf Y μ t
          ≤ ∫ ω, chord ω ∂μ := hmono
        _ = cosh (t * R) := hchord_eq
        _ ≤ exp ((t * R) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
        _ = exp ((R ^ 2) * t ^ 2 / 2) := by ring_nf

/-- A two-sided exponential consequence of a sub-Gaussian MGF bound. -/
lemma integral_cosh_mul_le_of_hasSubgaussianMGF {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) (t : ℝ) :
    ∫ ω, cosh (t * X ω) ∂μ ≤ exp ((c : ℝ) * t ^ 2 / 2) := by
  have hint_pos : Integrable (fun ω => exp (t * X ω)) μ :=
    h.integrable_exp_mul t
  have hint_neg : Integrable (fun ω => exp (-(t * X ω))) μ := by
    convert h.integrable_exp_mul (-t) using 1
    ext ω
    ring_nf
  have h_eq :
      ∫ ω, cosh (t * X ω) ∂μ =
        (mgf X μ t + mgf X μ (-t)) / 2 := by
    calc ∫ ω, cosh (t * X ω) ∂μ
        = ∫ ω, (exp (t * X ω) + exp (-(t * X ω))) / 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [Real.cosh_eq]
      _ = (∫ ω, exp (t * X ω) + exp (-(t * X ω)) ∂μ) / 2 := by
          rw [integral_div]
      _ = (mgf X μ t + mgf X μ (-t)) / 2 := by
          rw [integral_add hint_pos hint_neg]
          change (∫ ω, exp (t * X ω) ∂μ + ∫ ω, exp (-(t * X ω)) ∂μ) / 2 =
            (∫ ω, exp (t * X ω) ∂μ + ∫ ω, exp (-t * X ω) ∂μ) / 2
          simp only [neg_mul]
  rw [h_eq]
  have hpos_le : mgf X μ t ≤ exp ((c : ℝ) * t ^ 2 / 2) :=
    h.mgf_le t
  have hneg_le : mgf X μ (-t) ≤ exp ((c : ℝ) * t ^ 2 / 2) := by
    simpa [sq] using h.mgf_le (-t)
  nlinarith [hpos_le, hneg_le]

/-- Each nonnegative Taylor term of `cosh` is bounded by `cosh` itself. -/
lemma cosh_taylor_term_le (y : ℝ) (m : ℕ) :
    y ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ≤ cosh y := by
  rw [Real.cosh_eq_tsum]
  have hs := (Real.hasSum_cosh y).summable
  have hnonneg : ∀ n : ℕ, 0 ≤ y ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
    intro n
    exact div_nonneg (Even.pow_nonneg (even_two.mul_right n) y)
      (Nat.cast_nonneg (Nat.factorial (2 * n)))
  have hsingle :=
    hs.sum_le_tsum ({m} : Finset ℕ) (fun n _ => hnonneg n)
  simpa using hsingle

/-- Sub-Gaussian MGF control bounds every integrated even Taylor term. -/
lemma integral_even_taylor_term_le_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (t : ℝ) (m : ℕ) :
    ∫ ω, (t * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ∂μ
      ≤ exp ((c : ℝ) * t ^ 2 / 2) := by
  have hint_pos : Integrable (fun ω => exp (t * X ω)) μ :=
    h.integrable_exp_mul t
  have hint_neg : Integrable (fun ω => exp (-(t * X ω))) μ := by
    convert h.integrable_exp_mul (-t) using 1
    ext ω
    ring_nf
  have hterm_int :
      Integrable (fun ω => (t * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) μ := by
    have hpow :
        Integrable (fun ω => (t * X ω) ^ (2 * m)) μ := by
      exact integrable_pow_of_integrable_exp_mul
        (X := fun ω => t * X ω) (t := 1) one_ne_zero
        (by
          convert hint_pos using 1
          ext ω
          ring_nf)
        (by
          convert hint_neg using 1
          ext ω
          ring_nf)
        (2 * m)
    exact hpow.div_const _
  have hcosh_int : Integrable (fun ω => cosh (t * X ω)) μ := by
    have hsum : Integrable (fun ω => exp (t * X ω) + exp (-(t * X ω))) μ :=
      hint_pos.add hint_neg
    convert hsum.div_const 2 using 1
    ext ω
    rw [Real.cosh_eq]
  calc ∫ ω, (t * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ∂μ
      ≤ ∫ ω, cosh (t * X ω) ∂μ := by
        exact integral_mono_ae hterm_int hcosh_int
          (ae_of_all _ fun ω => cosh_taylor_term_le (t * X ω) m)
    _ ≤ exp ((c : ℝ) * t ^ 2 / 2) :=
        integral_cosh_mul_le_of_hasSubgaussianMGF h t

/-- Even moment bound obtained from sub-Gaussian MGF control at an arbitrary scale. -/
lemma integral_even_power_le_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {s : ℝ} (hs : 0 < s) (m : ℕ) :
    ∫ ω, X ω ^ (2 * m) ∂μ
      ≤ (Nat.factorial (2 * m) : ℝ) / s ^ (2 * m) *
        exp ((c : ℝ) * s ^ 2 / 2) := by
  have hle := integral_even_taylor_term_le_of_hasSubgaussianMGF h s m
  have hscale :
      ∫ ω, (s * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ∂μ =
        (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) *
          ∫ ω, X ω ^ (2 * m) ∂μ := by
    calc ∫ ω, (s * X ω) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ∂μ
        = ∫ ω, (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) *
            X ω ^ (2 * m) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [mul_pow]
          ring
      _ = (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) *
          ∫ ω, X ω ^ (2 * m) ∂μ := by
          rw [integral_const_mul]
  rw [hscale] at hle
  have hcoef_pos :
      0 < s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by
    positivity
  have hbound :
      ∫ ω, X ω ^ (2 * m) ∂μ
        ≤ exp ((c : ℝ) * s ^ 2 / 2) /
          (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) := by
    rw [le_div_iff₀ hcoef_pos]
    nlinarith [hle]
  calc ∫ ω, X ω ^ (2 * m) ∂μ
      ≤ exp ((c : ℝ) * s ^ 2 / 2) /
          (s ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) := hbound
    _ = (Nat.factorial (2 * m) : ℝ) / s ^ (2 * m) *
        exp ((c : ℝ) * s ^ 2 / 2) := by
        field_simp [ne_of_gt hs, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * m))]

/-- Pointwise power-series expansion of `exp (θ x²)`. -/
lemma exp_mul_sq_eq_tsum (θ x : ℝ) :
    exp (θ * x ^ 2) =
      ∑' m : ℕ, θ ^ m * x ^ (2 * m) / (Nat.factorial m : ℝ) := by
  rw [show exp (θ * x ^ 2) = ∑' m : ℕ, (θ * x ^ 2) ^ m / (Nat.factorial m : ℝ) by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]]
  congr with m
  rw [mul_pow, ← pow_mul]

/-- A factorial estimate used to sum the square-exponential moment series. -/
lemma factorial_two_mul_div_factorial_le_succ_pow (m : ℕ) :
    (Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ) ≤
      ((2 * m + 1 : ℕ) : ℝ) ^ m := by
  have hnat : Nat.factorial (2 * m) ≤ (2 * m + 1) ^ m * Nat.factorial m := by
    calc Nat.factorial (2 * m)
        ≤ (2 * m) ^ m * Nat.factorial m := Nat.factorial_two_mul_le m
      _ ≤ (2 * m + 1) ^ m * Nat.factorial m := by
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ _) m)
  have hfac_pos : 0 < (Nat.factorial m : ℝ) := by positivity
  rw [div_le_iff₀ hfac_pos]
  exact_mod_cast hnat

/-- A geometric bound for each integrated square-exponential Taylor term. -/
lemma integral_exp_sq_series_term_le_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ) (m : ℕ) :
    ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
      ≤ exp 1 * (θ * ((c : ℝ) + 1) * exp 1) ^ m := by
  let q : ℝ := ((2 * m + 1 : ℕ) : ℝ) / ((c : ℝ) + 1)
  let s : ℝ := sqrt q
  have hc1_pos : 0 < (c : ℝ) + 1 := by positivity
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have hs_pos : 0 < s := by
    dsimp [s]
    exact sqrt_pos.mpr hq_pos
  have hs_pow : s ^ (2 * m) = q ^ m := by
    dsimp [s]
    rw [pow_mul, sq_sqrt hq_nonneg]
  have hs_sq : s ^ 2 = q := by
    dsimp [s]
    rw [sq_sqrt hq_nonneg]
  have hmoment := integral_even_power_le_of_hasSubgaussianMGF h hs_pos m
  have hterm_eq :
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ =
        (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ := by
    calc ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
        = ∫ ω, (θ ^ m / (Nat.factorial m : ℝ)) * X ω ^ (2 * m) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
      _ = (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ := by
          rw [integral_const_mul]
  rw [hterm_eq]
  have hcoef_nonneg : 0 ≤ θ ^ m / (Nat.factorial m : ℝ) := by
    positivity
  calc (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ
      ≤ (θ ^ m / (Nat.factorial m : ℝ)) *
          ((Nat.factorial (2 * m) : ℝ) / s ^ (2 * m) *
            exp ((c : ℝ) * s ^ 2 / 2)) := by
        exact mul_le_mul_of_nonneg_left hmoment hcoef_nonneg
    _ = θ ^ m *
          (((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m) *
            exp ((c : ℝ) * q / 2) := by
        rw [hs_pow, hs_sq]
        field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
    _ ≤ θ ^ m * (((c : ℝ) + 1) ^ m) * exp (m + 1 : ℝ) := by
        have hfac := factorial_two_mul_div_factorial_le_succ_pow m
        have hratio :
            ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m
              ≤ ((c : ℝ) + 1) ^ m := by
          have hnum_pos : 0 < (((2 * m + 1 : ℕ) : ℝ) ^ m) := by positivity
          have hc1pow_nonneg : 0 ≤ ((c : ℝ) + 1) ^ m := by positivity
          calc
            ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m
                = ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) *
                  (((c : ℝ) + 1) ^ m / (((2 * m + 1 : ℕ) : ℝ) ^ m)) := by
                    dsimp [q]
                    rw [div_pow]
                    field_simp [hc1_pos.ne']
            _ ≤ (((2 * m + 1 : ℕ) : ℝ) ^ m) *
                  (((c : ℝ) + 1) ^ m / (((2 * m + 1 : ℕ) : ℝ) ^ m)) := by
                    exact mul_le_mul_of_nonneg_right hfac
                      (div_nonneg hc1pow_nonneg hnum_pos.le)
            _ = ((c : ℝ) + 1) ^ m := by
                    field_simp [ne_of_gt hnum_pos]
        have hexp_le : exp ((c : ℝ) * q / 2) ≤ exp (m + 1 : ℝ) := by
          apply exp_le_exp.mpr
          have hc_le : (c : ℝ) / ((c : ℝ) + 1) ≤ 1 := by
            rw [div_le_one hc1_pos]
            linarith
          have hnon : 0 ≤ ((2 * m + 1 : ℕ) : ℝ) / 2 := by positivity
          calc
            (c : ℝ) * q / 2 =
                ((c : ℝ) / ((c : ℝ) + 1)) * (((2 * m + 1 : ℕ) : ℝ) / 2) := by
                  dsimp [q]
                  field_simp [hc1_pos.ne']
            _ ≤ 1 * (((2 * m + 1 : ℕ) : ℝ) / 2) :=
                mul_le_mul_of_nonneg_right hc_le hnon
            _ ≤ (m + 1 : ℝ) := by
                norm_num
                nlinarith
        calc
          θ ^ m * (((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m) *
              exp ((c : ℝ) * q / 2)
              ≤ θ ^ m * ((c : ℝ) + 1) ^ m * exp ((c : ℝ) * q / 2) := by
                gcongr
          _ ≤ θ ^ m * ((c : ℝ) + 1) ^ m * exp (m + 1 : ℝ) := by
                gcongr
    _ = exp 1 * (θ * ((c : ℝ) + 1) * exp 1) ^ m := by
        rw [show (m + 1 : ℝ) = (m : ℝ) + 1 by norm_num, exp_add]
        rw [show exp (m : ℝ) = exp 1 ^ m by
          rw [show (m : ℝ) = (m : ℝ) * 1 by ring, Real.exp_nat_mul]]
        rw [mul_pow, mul_pow]
        ring

/-- A geometric Taylor-term bound using any positive real proxy above the sub-Gaussian parameter. -/
lemma integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0) (m : ℕ) :
    ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
      ≤ exp 1 * (θ * C0 * exp 1) ^ m := by
  let q : ℝ := ((2 * m + 1 : ℕ) : ℝ) / C0
  let s : ℝ := sqrt q
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hq_nonneg : 0 ≤ q := hq_pos.le
  have hs_pos : 0 < s := by
    dsimp [s]
    exact sqrt_pos.mpr hq_pos
  have hs_pow : s ^ (2 * m) = q ^ m := by
    dsimp [s]
    rw [pow_mul, sq_sqrt hq_nonneg]
  have hs_sq : s ^ 2 = q := by
    dsimp [s]
    rw [sq_sqrt hq_nonneg]
  have hmoment := integral_even_power_le_of_hasSubgaussianMGF h hs_pos m
  have hterm_eq :
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ =
        (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ := by
    calc ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
        = ∫ ω, (θ ^ m / (Nat.factorial m : ℝ)) * X ω ^ (2 * m) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
      _ = (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ := by
          rw [integral_const_mul]
  rw [hterm_eq]
  have hcoef_nonneg : 0 ≤ θ ^ m / (Nat.factorial m : ℝ) := by
    positivity
  calc (θ ^ m / (Nat.factorial m : ℝ)) * ∫ ω, X ω ^ (2 * m) ∂μ
      ≤ (θ ^ m / (Nat.factorial m : ℝ)) *
          ((Nat.factorial (2 * m) : ℝ) / s ^ (2 * m) *
            exp ((c : ℝ) * s ^ 2 / 2)) := by
        exact mul_le_mul_of_nonneg_left hmoment hcoef_nonneg
    _ = θ ^ m *
          (((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m) *
            exp ((c : ℝ) * q / 2) := by
        rw [hs_pow, hs_sq]
        field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
    _ ≤ θ ^ m * C0 ^ m * exp (m + 1 : ℝ) := by
        have hfac := factorial_two_mul_div_factorial_le_succ_pow m
        have hratio :
            ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m
              ≤ C0 ^ m := by
          have hnum_pos : 0 < (((2 * m + 1 : ℕ) : ℝ) ^ m) := by positivity
          have hC0pow_nonneg : 0 ≤ C0 ^ m := by positivity
          calc
            ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m
                = ((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) *
                  (C0 ^ m / (((2 * m + 1 : ℕ) : ℝ) ^ m)) := by
                    dsimp [q]
                    rw [div_pow]
                    field_simp [hC0.ne']
            _ ≤ (((2 * m + 1 : ℕ) : ℝ) ^ m) *
                  (C0 ^ m / (((2 * m + 1 : ℕ) : ℝ) ^ m)) := by
                    exact mul_le_mul_of_nonneg_right hfac
                      (div_nonneg hC0pow_nonneg hnum_pos.le)
            _ = C0 ^ m := by
                    field_simp [ne_of_gt hnum_pos]
        have hexp_le : exp ((c : ℝ) * q / 2) ≤ exp (m + 1 : ℝ) := by
          apply exp_le_exp.mpr
          have hc_div_le : (c : ℝ) / C0 ≤ 1 := by
            rw [div_le_one hC0]
            exact hc_le
          have hnon : 0 ≤ ((2 * m + 1 : ℕ) : ℝ) / 2 := by positivity
          calc
            (c : ℝ) * q / 2 =
                ((c : ℝ) / C0) * (((2 * m + 1 : ℕ) : ℝ) / 2) := by
                  dsimp [q]
                  field_simp [hC0.ne']
            _ ≤ 1 * (((2 * m + 1 : ℕ) : ℝ) / 2) :=
                mul_le_mul_of_nonneg_right hc_div_le hnon
            _ ≤ (m + 1 : ℝ) := by
                norm_num
                nlinarith
        calc
          θ ^ m * (((Nat.factorial (2 * m) : ℝ) / (Nat.factorial m : ℝ)) / q ^ m) *
              exp ((c : ℝ) * q / 2)
              ≤ θ ^ m * C0 ^ m * exp ((c : ℝ) * q / 2) := by
                gcongr
          _ ≤ θ ^ m * C0 ^ m * exp (m + 1 : ℝ) := by
                gcongr
    _ = exp 1 * (θ * C0 * exp 1) ^ m := by
        rw [show (m + 1 : ℝ) = (m : ℝ) + 1 by norm_num, exp_add]
        rw [show exp (m : ℝ) = exp 1 ^ m by
          rw [show (m : ℝ) = (m : ℝ) * 1 by ring, Real.exp_nat_mul]]
        rw [mul_pow, mul_pow]
        ring

end HansonWrightProof
end NLAlib
