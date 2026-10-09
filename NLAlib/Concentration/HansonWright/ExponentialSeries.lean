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
import NLAlib.Concentration.HansonWright.ScalarMoments

/-!
# Hanson–Wright proof: ExponentialSeries

A focused leaf of the transported independent-coordinate proof.
Shared helper declarations live in `NLAlib.HansonWrightProof`; the canonical
public bounds are in `NLAlib.Estimation.HansonWright`.
Atlas: `hanson-wright`. Source: HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal Matrix.Norms.L2Operator

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib
namespace HansonWrightProof

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The square-exponential Taylor integrals are summable below the explicit radius. -/
lemma summable_integral_exp_sq_series_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hθ_small : θ * ((c : ℝ) + 1) * exp 1 < 1) :
    Summable fun m : ℕ =>
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ := by
  set r : ℝ := θ * ((c : ℝ) + 1) * exp 1 with hr_def
  have hr_nonneg : 0 ≤ r := by
    rw [hr_def]
    positivity
  have hgeom : Summable fun m : ℕ => exp 1 * r ^ m :=
    (summable_geometric_of_lt_one hr_nonneg (by simpa only [hr_def] using hθ_small)).mul_left
      (exp 1)
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro m
    exact integral_nonneg_of_ae (ae_of_all _ fun ω => by
      exact div_nonneg
        (mul_nonneg (pow_nonneg hθ m) (Even.pow_nonneg (even_two.mul_right m) (X ω)))
        (Nat.cast_nonneg (Nat.factorial m)))
  · intro m
    simpa only [hr_def] using integral_exp_sq_series_term_le_of_hasSubgaussianMGF h hθ m

/-- Summability of square-exponential Taylor integrals using a positive proxy `C0 ≥ c`. -/
lemma summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    Summable fun m : ℕ =>
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  have hr_nonneg : 0 ≤ r := by
    rw [hr_def]
    positivity
  have hgeom : Summable fun m : ℕ => exp 1 * r ^ m :=
    (summable_geometric_of_lt_one hr_nonneg (by simpa only [hr_def] using hθ_small)).mul_left
      (exp 1)
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro m
    exact integral_nonneg_of_ae (ae_of_all _ fun ω => by
      exact div_nonneg
        (mul_nonneg (pow_nonneg hθ m) (Even.pow_nonneg (even_two.mul_right m) (X ω)))
        (Nat.cast_nonneg (Nat.factorial m)))
  · intro m
    simpa only [hr_def] using
      integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le m

/-- Integral form of the square-exponential Taylor expansion. -/
lemma integral_exp_mul_sq_eq_tsum_integrals {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsum : Summable fun m : ℕ =>
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ =
      ∑' m : ℕ, ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ := by
  let F : ℕ → Ω → ℝ :=
    fun m ω => θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ)
  have hF_nonneg : ∀ m : ℕ, 0 ≤ᵐ[μ] F m := by
    intro m
    exact ae_of_all _ fun ω => by
      dsimp [F]
      exact div_nonneg
        (mul_nonneg (pow_nonneg hθ m) (Even.pow_nonneg (even_two.mul_right m) (X ω)))
        (Nat.cast_nonneg (Nat.factorial m))
  have hF_int : ∀ m : ℕ, Integrable (F m) μ := by
    intro m
    have hpow : Integrable (fun ω => X ω ^ (2 * m)) μ := by
      exact integrable_pow_of_integrable_exp_mul
        (X := X) (t := 1) one_ne_zero
        (h.integrable_exp_mul 1)
        (h.integrable_exp_mul (-1))
        (2 * m)
    dsimp [F]
    exact (hpow.const_mul (θ ^ m)).div_const _
  have hF_sum_norm : Summable fun m : ℕ => ∫ ω, ‖F m ω‖ ∂μ := by
    convert hsum using 1
    ext m
    apply integral_congr_ae
    filter_upwards [hF_nonneg m] with ω hω
    rw [Real.norm_of_nonneg hω]
  have htsum := integral_tsum_of_summable_integral_norm hF_int hF_sum_norm
  change ∫ ω, exp (θ * X ω ^ 2) ∂μ = ∑' m : ℕ, ∫ ω, F m ω ∂μ
  rw [htsum]
  apply integral_congr_ae
  filter_upwards with ω
  dsimp [F]
  rw [exp_mul_sq_eq_tsum θ (X ω)]

/-- A quantitative square-exponential integral bound below the proxy radius. -/
lemma integral_exp_mul_sq_le_inv_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤ exp 1 * (1 - θ * C0 * exp 1)⁻¹ := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_lt : r < 1 := by simpa only [hr_def] using hθ_small
  have hsum :=
    summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le hθ_small
  have hgeom : Summable fun m : ℕ => exp 1 * r ^ m :=
    (summable_geometric_of_lt_one hr_nonneg hr_lt).mul_left (exp 1)
  rw [integral_exp_mul_sq_eq_tsum_integrals h hθ hsum]
  calc
    (∑' m : ℕ, ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ)
        ≤ ∑' m : ℕ, exp 1 * r ^ m := by
          refine Summable.tsum_le_tsum ?_ hsum hgeom
          intro m
          simpa only [hr_def] using
            integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le m
    _ = exp 1 * (1 - r)⁻¹ := by
          rw [tsum_mul_left]
          rw [tsum_geometric_of_lt_one hr_nonneg hr_lt]
    _ = exp 1 * (1 - θ * C0 * exp 1)⁻¹ := by rw [hr_def]

/-- A sharper square-exponential bound with the exact zeroth Taylor term isolated. -/
lemma integral_exp_mul_sq_le_one_add_tail_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤
      1 + exp 1 * ((θ * C0 * exp 1) * (1 - θ * C0 * exp 1)⁻¹) := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  let term : ℕ → ℝ :=
    fun m => ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_lt : r < 1 := by simpa only [hr_def] using hθ_small
  have hsum : Summable term := by
    simpa only [term] using
      summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le hθ_small
  have hterm0 : term 0 = 1 := by
    change (∫ ω : Ω, θ ^ (0 : ℕ) * X ω ^ (2 * 0) /
      (Nat.factorial 0 : ℝ) ∂μ) = 1
    have hfun :
        (fun ω : Ω => θ ^ 0 * X ω ^ (2 * 0) / (Nat.factorial 0 : ℝ)) =
          (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      norm_num
    rw [hfun]
    rw [integral_const, probReal_univ]
    norm_num
  have htail_sum : Summable fun n : ℕ => term (n + 1) := by
    exact (summable_nat_add_iff (f := term) 1).mpr hsum
  have hgeom_tail : Summable fun n : ℕ => exp 1 * r ^ (n + 1) := by
    have hgeom_base : Summable fun n : ℕ => r ^ n :=
      summable_geometric_of_lt_one hr_nonneg hr_lt
    have hgeom_shift : Summable fun n : ℕ => r ^ (n + 1) :=
      (summable_nat_add_iff (f := fun n : ℕ => r ^ n) 1).mpr hgeom_base
    exact hgeom_shift.mul_left (exp 1)
  rw [integral_exp_mul_sq_eq_tsum_integrals h hθ (by simpa only [term] using hsum)]
  change (∑' m : ℕ, term m) ≤ 1 + exp 1 * (r * (1 - r)⁻¹)
  rw [hsum.tsum_eq_zero_add, hterm0]
  gcongr
  calc
    (∑' n : ℕ, term (n + 1)) ≤ ∑' n : ℕ, exp 1 * r ^ (n + 1) := by
      refine Summable.tsum_le_tsum ?_ htail_sum hgeom_tail
      intro n
      simpa only [term, hr_def] using
        integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le (n + 1)
    _ = exp 1 * (r * (1 - r)⁻¹) := by
      rw [tsum_mul_left]
      rw [show (∑' n : ℕ, r ^ (n + 1)) = r * (1 - r)⁻¹ by
        have hgeom_base : Summable fun n : ℕ => r ^ n :=
          summable_geometric_of_lt_one hr_nonneg hr_lt
        have hsplit := hgeom_base.sum_add_tsum_nat_add 1
        rw [Finset.sum_range_one, tsum_geometric_of_lt_one hr_nonneg hr_lt] at hsplit
        have hshift : (∑' n : ℕ, r ^ (n + 1)) = (1 - r)⁻¹ - 1 := by
          linarith
        rw [hshift]
        have hden : 1 - r ≠ 0 := by linarith
        field_simp [hden]
        ring]

/-- A square-exponential bound with the zeroth and first Taylor terms isolated. -/
lemma integral_exp_mul_sq_le_one_add_linear_add_tail_of_hasSubgaussianMGF_of_le
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤
      1 + θ * ∫ ω, X ω ^ 2 ∂μ +
        exp 1 * (((θ * C0 * exp 1) ^ 2) * (1 - θ * C0 * exp 1)⁻¹) := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  let term : ℕ → ℝ :=
    fun m => ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_lt : r < 1 := by simpa only [hr_def] using hθ_small
  have hsum : Summable term := by
    simpa only [term] using
      summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le hθ_small
  have hterm0 : term 0 = 1 := by
    change (∫ ω : Ω, θ ^ (0 : ℕ) * X ω ^ (2 * 0) /
      (Nat.factorial 0 : ℝ) ∂μ) = 1
    have hfun :
        (fun ω : Ω => θ ^ 0 * X ω ^ (2 * 0) / (Nat.factorial 0 : ℝ)) =
          (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      norm_num
    rw [hfun]
    rw [integral_const, probReal_univ]
    norm_num
  have hterm1 : term 1 = θ * ∫ ω, X ω ^ 2 ∂μ := by
    change (∫ ω : Ω, θ ^ (1 : ℕ) * X ω ^ (2 * 1) /
      (Nat.factorial 1 : ℝ) ∂μ) = θ * ∫ ω, X ω ^ 2 ∂μ
    have hfun :
        (fun ω : Ω => θ ^ 1 * X ω ^ (2 * 1) / (Nat.factorial 1 : ℝ)) =
          (fun ω : Ω => θ * X ω ^ 2) := by
      funext ω
      norm_num
    rw [hfun, integral_const_mul]
  have htail_sum : Summable fun n : ℕ => term (n + 2) := by
    exact (summable_nat_add_iff (f := term) 2).mpr hsum
  have hgeom_tail : Summable fun n : ℕ => exp 1 * r ^ (n + 2) := by
    have hgeom_base : Summable fun n : ℕ => r ^ n :=
      summable_geometric_of_lt_one hr_nonneg hr_lt
    have hgeom_shift : Summable fun n : ℕ => r ^ (n + 2) :=
      (summable_nat_add_iff (f := fun n : ℕ => r ^ n) 2).mpr hgeom_base
    exact hgeom_shift.mul_left (exp 1)
  rw [integral_exp_mul_sq_eq_tsum_integrals h hθ (by simpa only [term] using hsum)]
  change (∑' m : ℕ, term m) ≤
    1 + θ * ∫ ω, X ω ^ 2 ∂μ + exp 1 * (r ^ 2 * (1 - r)⁻¹)
  have hsplit := hsum.sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_one, hterm0, hterm1] at hsplit
  rw [← hsplit]
  gcongr
  calc
    (∑' n : ℕ, term (n + 2)) ≤ ∑' n : ℕ, exp 1 * r ^ (n + 2) := by
      refine Summable.tsum_le_tsum ?_ htail_sum hgeom_tail
      intro n
      simpa only [term, hr_def] using
        integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le (n + 2)
    _ = exp 1 * (r ^ 2 * (1 - r)⁻¹) := by
      rw [tsum_mul_left]
      rw [show (∑' n : ℕ, r ^ (n + 2)) = r ^ 2 * (1 - r)⁻¹ by
        have hgeom_base : Summable fun n : ℕ => r ^ n :=
          summable_geometric_of_lt_one hr_nonneg hr_lt
        have hsplit2 := hgeom_base.sum_add_tsum_nat_add 2
        rw [Finset.sum_range_succ, Finset.sum_range_one,
          tsum_geometric_of_lt_one hr_nonneg hr_lt] at hsplit2
        have hshift : (∑' n : ℕ, r ^ (n + 2)) = (1 - r)⁻¹ - (1 + r) := by
          linarith
        rw [hshift]
        have hden : 1 - r ≠ 0 := by linarith
        field_simp [hden]
        ring]

/-- A linear-in-`θ` square-exponential bound at half the explicit radius. -/
lemma integral_exp_mul_sq_le_exp_linear_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_half : θ * C0 * exp 1 ≤ 1 / 2) :
    ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤ exp (2 * exp 1 * (θ * C0 * exp 1)) := by
  set r : ℝ := θ * C0 * exp 1 with hr_def
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_half : r ≤ 1 / 2 := by simpa only [hr_def] using hθ_half
  have hr_lt : r < 1 := by linarith
  have hbase :=
    integral_exp_mul_sq_le_one_add_tail_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le
      (by simpa only [hr_def] using hr_lt)
  have hden_pos : 0 < 1 - r := by linarith
  have hinv_le : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden_pos two_pos]
    linarith
  have htail :
      exp 1 * (r * (1 - r)⁻¹) ≤ 2 * exp 1 * r := by
    have hmul : r * (1 - r)⁻¹ ≤ r * 2 :=
      mul_le_mul_of_nonneg_left hinv_le hr_nonneg
    calc
      exp 1 * (r * (1 - r)⁻¹) ≤ exp 1 * (r * 2) :=
        mul_le_mul_of_nonneg_left hmul (exp_pos 1).le
      _ = 2 * exp 1 * r := by ring
  calc
    ∫ ω, exp (θ * X ω ^ 2) ∂μ
        ≤ 1 + exp 1 * (r * (1 - r)⁻¹) := by
          simpa only [hr_def] using hbase
    _ ≤ 1 + 2 * exp 1 * r := by linarith
    _ ≤ exp (2 * exp 1 * r) := by
          simpa [add_comm] using Real.add_one_le_exp (2 * exp 1 * r)
    _ = exp (2 * exp 1 * (θ * C0 * exp 1)) := by rw [hr_def]

/-- Gaussian square-form bound for a positive symmetric operator, proved by spectral
diagonalization and one-dimensional square-exponential estimates. -/
lemma integral_exp_quadratic_stdGaussian_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : E →L[ℝ] E) (hTpos : T.toLinearMap.IsPositive) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsmall : ∀ i : Fin (Module.finrank ℝ E),
      θ * hTpos.isSymmetric.eigenvalues rfl i * exp 1 ≤ 1 / 2) :
    ∫ x : E, exp (θ * inner ℝ (T x) x) ∂(stdGaussian E) ≤
      exp (2 * exp 1 ^ 2 * θ *
        (∑ i : Fin (Module.finrank ℝ E), hTpos.isSymmetric.eigenvalues rfl i)) := by
  let hsym := hTpos.isSymmetric
  let b := hsym.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let lam : Fin (Module.finrank ℝ E) → ℝ := fun i => hsym.eigenvalues rfl i
  have hnonneg : ∀ i : Fin (Module.finrank ℝ E), 0 ≤ lam i := by
    intro i
    simpa [lam, hsym] using hTpos.nonneg_eigenvalues
      (by rfl : Module.finrank ℝ E = Module.finrank ℝ E) i
  have hsynth_aemeas :
      AEMeasurable (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ i, z i • b i)
        (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) := by
    exact (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const).aemeasurable
  have hf_aesm :
      AEStronglyMeasurable (fun x : E => exp (θ * inner ℝ (T x) x))
        (Measure.map (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ i, z i • b i)
          (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)) := by
    fun_prop
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integral_map hsynth_aemeas hf_aesm]
  have hpoint : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      exp (θ * inner ℝ (T (∑ i, z i • b i)) (∑ i, z i • b i)) =
        ∏ i : Fin (Module.finrank ℝ E), exp ((θ * lam i) * z i ^ 2) := by
    intro z
    change exp (θ * inner ℝ (T.toLinearMap (∑ i, z i • b i)) (∑ i, z i • b i)) =
      ∏ i : Fin (Module.finrank ℝ E), exp ((θ * lam i) * z i ^ 2)
    have hquad :=
      symmetric_inner_apply_eq_sum_eigenvalues_repr T.toLinearMap hsym (∑ i, z i • b i)
    rw [hquad]
    have hsum_eq :
        (∑ i : Fin (Module.finrank ℝ E),
            hsym.eigenvalues rfl i * (hsym.eigenvectorBasis rfl).repr
              (∑ i, z i • b i) i ^ 2) =
          ∑ i : Fin (Module.finrank ℝ E), lam i * z i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have hcoord :
          (hsym.eigenvectorBasis rfl).repr (∑ i, z i • b i) i = z i := by
        change b.repr (∑ i, z i • b i) i = z i
        exact orthonormalBasis_repr_sum_smul b z i
      rw [hcoord]
    rw [hsum_eq]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    ∫ (x : Fin (Module.finrank ℝ E) → ℝ),
        exp (θ * inner ℝ (T (∑ i, x i • b i)) (∑ i, x i • b i))
        ∂Measure.pi (fun x => gaussianReal 0 1)
        = ∫ (x : Fin (Module.finrank ℝ E) → ℝ),
          ∏ i : Fin (Module.finrank ℝ E), exp ((θ * lam i) * x i ^ 2)
        ∂Measure.pi (fun x => gaussianReal 0 1) := by
          apply integral_congr_ae
          filter_upwards with z
          exact hpoint z
    _ = ∏ i : Fin (Module.finrank ℝ E),
          ∫ x : ℝ, exp ((θ * lam i) * x ^ 2) ∂gaussianReal 0 1 := by
          exact (integral_fintype_prod_eq_prod (𝕜 := ℝ)
            (ι := Fin (Module.finrank ℝ E)) (E := fun _ => ℝ)
            (f := fun i x => exp ((θ * lam i) * x ^ 2))
            (μ := fun _ => gaussianReal 0 1))
    _ ≤ ∏ i : Fin (Module.finrank ℝ E),
          exp (2 * exp 1 * ((θ * lam i) * 1 * exp 1)) := by
          apply Finset.prod_le_prod
          · intro i _
            exact integral_nonneg_of_ae (ae_of_all _ fun x => exp_nonneg _)
          · intro i _
            have hθi : 0 ≤ θ * lam i := mul_nonneg hθ (hnonneg i)
            have hle := integral_exp_mul_sq_le_exp_linear_of_hasSubgaussianMGF_of_le
              (μ := gaussianReal 0 1) hasSubgaussianMGF_id_gaussianReal_zero_one
              (θ := θ * lam i) (C0 := 1) hθi (by norm_num) (by norm_num) ?_
            · simpa only [id_eq] using hle
            · convert hsmall i using 1; ring
    _ = exp (2 * exp 1 ^ 2 * θ *
          (∑ i : Fin (Module.finrank ℝ E), lam i)) := by
          rw [← Real.exp_sum]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

/-- Source-transport helper `matrix_trace_conjTranspose_mul_self_eq_frobeniusNormSq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma matrix_trace_conjTranspose_mul_self_eq_frobeniusNormSq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.conjTranspose * A).trace = frobeniusNormSq A := by
  unfold Matrix.trace frobeniusNormSq Matrix.diag
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [star_trivial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Source-transport helper `toEuclideanCLM_adjoint` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma toEuclideanCLM_adjoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) A) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A.conjTranspose := by
  change LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A).adjoint =
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A.conjTranspose)
  congr 1
  exact (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm

/-- Source-transport helper `operatorNorm_conjTranspose` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma operatorNorm_conjTranspose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    deterministicOperatorNorm A.conjTranspose = deterministicOperatorNorm A := by
  unfold deterministicOperatorNorm
  exact Matrix.l2_opNorm_conjTranspose A

/-- Source-transport helper `frobeniusNormSq_conjTranspose` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma frobeniusNormSq_conjTranspose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusNormSq A.conjTranspose = frobeniusNormSq A := by
  unfold frobeniusNormSq
  simp only [Matrix.conjTranspose_apply, star_trivial]
  rw [Finset.sum_comm]

end HansonWrightProof
end NLAlib
