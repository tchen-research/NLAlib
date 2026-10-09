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
import NLAlib.Concentration.HansonWright.ExponentialSeries

/-!
# Hanson–Wright proof: CenteredSquareBounds

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

/-- Source-transport helper `frobeniusNorm_conjTranspose_sq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma frobeniusNorm_conjTranspose_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    deterministicFrobeniusNorm A.conjTranspose ^ 2 = deterministicFrobeniusNorm A ^ 2 := by
  rw [frobeniusNorm_sq, frobeniusNorm_sq, frobeniusNormSq_conjTranspose]

/-- Source-transport helper `trace_adjoint_comp_toEuclideanCLM_eq_frobeniusNormSq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma trace_adjoint_comp_toEuclideanCLM_eq_frobeniusNormSq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)))
      ((ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) A) ∘L
        Matrix.toEuclideanCLM (𝕜 := ℝ) A).toLinearMap) = frobeniusNormSq A := by
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.adjoint T ∘L T
  change (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))) S.toLinearMap = frobeniusNormSq A
  rw [LinearMap.trace_eq_sum_inner S.toLinearMap (EuclideanSpace.basisFun (Fin n) ℝ)]
  unfold frobeniusNormSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [S, T]
  have hbasis (i : Fin n) :
      (EuclideanSpace.basisFun (Fin n) ℝ j).ofLp i =
        if i = j then (1 : ℝ) else 0 := by
    simp [EuclideanSpace.basisFun_apply]
  rw [Matrix.toEuclideanCLM_toLp]
  rw [toEuclideanCLM_adjoint]
  rw [Matrix.toEuclideanCLM_toLp]
  rw [PiLp.inner_apply]
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.mulVec,
    dotProduct]
  have hsum_basis (k : Fin n) :
      (∑ x, A x k * ∑ x_1, A x x_1 *
        ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
        ∑ x, A x k * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg (fun z => A x k * z)
    apply Finset.sum_congr rfl
    intro x_1 _
    apply congrArg (fun z => A x x_1 * z)
    exact hbasis x_1
  rw [Finset.sum_eq_single j]
  · have hsum_step :
        inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j)
            (∑ x, A x j * ∑ x_1, A x x_1 *
              ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
          inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j)
            (∑ x, A x j * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
      congrArg (fun z => inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j) z)
        (hsum_basis j)
    calc
      inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j)
          (∑ x, A x j * ∑ x_1, A x x_1 *
            ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
          inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j)
          (∑ x, A x j * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
        hsum_step
      _ = inner ℝ (if j = j then (1 : ℝ) else 0)
            (∑ x, A x j * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
        congrArg (fun z => inner ℝ z
          (∑ x, A x j * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)))
          (hbasis j)
      _ = ∑ x, A x j ^ 2 := by
        simp
        ring_nf
  · intro i _ hij
    have hsum_step :
        inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i)
            (∑ x, A x i * ∑ x_1, A x x_1 *
              ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
          inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i)
            (∑ x, A x i * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
      congrArg (fun z => inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i) z)
        (hsum_basis i)
    calc
      inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i)
          (∑ x, A x i * ∑ x_1, A x x_1 *
            ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
          inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i)
          (∑ x, A x i * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
        hsum_step
      _ = inner ℝ (if i = j then (1 : ℝ) else 0)
            (∑ x, A x i * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
        congrArg (fun z => inner ℝ z
          (∑ x, A x i * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)))
          (hbasis i)
      _ = 0 := by simp [hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Source-transport helper `eigenvalue_adjoint_comp_le_opNorm_sq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma eigenvalue_adjoint_comp_le_opNorm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    let S : E →L[ℝ] E := ContinuousLinearMap.adjoint T ∘L T
    let hSpos : S.toLinearMap.IsPositive :=
      (ContinuousLinearMap.isPositive_adjoint_comp_self T).toLinearMap
    hSpos.isSymmetric.eigenvalues rfl i ≤ ‖T‖ ^ 2 := by
  intro S hSpos
  let hsym := hSpos.isSymmetric
  let b := hsym.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let e := b i
  let lam := hsym.eigenvalues rfl i
  have heig : S.toLinearMap e = lam • e := by
    exact hsym.apply_eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E) i
  have hinner : inner ℝ (S e) e = lam := by
    rw [show S e = S.toLinearMap e by rfl, heig]
    rw [inner_smul_left]
    rw [inner_self_eq_norm_sq_to_K]
    simp [e, b]
  have hnorm_sq : ‖T e‖ ^ 2 = inner ℝ (S e) e := by
    simpa [S] using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T e
  have hnorm_le : ‖T e‖ ≤ ‖T‖ := by
    have h := T.le_opNorm e
    simpa [e, b, OrthonormalBasis.norm_eq_one] using h
  have hnorm_nonneg : 0 ≤ ‖T e‖ := norm_nonneg _
  have hop_nonneg : 0 ≤ ‖T‖ := norm_nonneg _
  calc
    lam = ‖T e‖ ^ 2 := by rw [← hinner, ← hnorm_sq]
    _ ≤ ‖T‖ ^ 2 := by nlinarith

/-- A second-moment bound from the square-exponential Taylor-term estimate. -/
lemma integral_sq_le_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {C0 : ℝ}
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0) :
    ∫ ω, X ω ^ 2 ∂μ ≤ exp 1 * (C0 * exp 1) := by
  have hterm :=
    integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h
      (θ := 1) (C0 := C0) (by norm_num) hC0 hc_le 1
  convert hterm using 1 <;> ring_nf

/-- A fourth-moment bound from the square-exponential Taylor-term estimate. -/
lemma integral_fourth_le_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {C0 : ℝ}
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0) :
    ∫ ω, X ω ^ 4 ∂μ ≤ 2 * exp 1 * (C0 * exp 1) ^ 2 := by
  have hterm :=
    integral_exp_sq_series_term_le_of_hasSubgaussianMGF_of_le h
      (θ := 1) (C0 := C0) (by norm_num) hC0 hc_le 2
  have hfac : (Nat.factorial 2 : ℝ) = 2 := by norm_num
  have hterm' : ∫ ω, X ω ^ 4 / 2 ∂μ ≤ exp 1 * (C0 * exp 1) ^ 2 := by
    have hfun :
        (fun ω : Ω => (1 : ℝ) ^ 2 * X ω ^ (2 * 2) /
          (Nat.factorial 2 : ℝ)) =
          (fun ω : Ω => X ω ^ 4 / 2) := by
      funext ω
      norm_num [hfac]
    rw [hfun] at hterm
    simpa only [one_mul] using hterm
  have hscale : ∫ ω, X ω ^ 4 / 2 ∂μ = (1 / 2 : ℝ) * ∫ ω, X ω ^ 4 ∂μ := by
    calc
      ∫ ω, X ω ^ 4 / 2 ∂μ = ∫ ω, (1 / 2 : ℝ) * X ω ^ 4 ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ = (1 / 2 : ℝ) * ∫ ω, X ω ^ 4 ∂μ := by rw [integral_const_mul]
  rw [hscale] at hterm'
  nlinarith

/-- A global quadratic upper bound for the negative exponential on the nonnegative half-line. -/
lemma exp_neg_le_one_sub_add_sq {u : ℝ} (hu : 0 ≤ u) :
    exp (-u) ≤ 1 - u + u ^ 2 := by
  have hden_pos : 0 < 1 + u := by linarith
  have hpoly_pos : 0 < 1 - u + u ^ 2 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have h_exp_ge : 1 + u ≤ exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  have hinv : (exp u)⁻¹ ≤ (1 + u)⁻¹ :=
    (inv_le_inv₀ (exp_pos u) hden_pos).2 h_exp_ge
  have hrat : (1 + u)⁻¹ ≤ 1 - u + u ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hden_pos]
    ring_nf
    nlinarith [pow_nonneg hu 3]
  calc
    exp (-u) = (exp u)⁻¹ := by rw [exp_neg]
    _ ≤ (1 + u)⁻¹ := hinv
    _ ≤ 1 - u + u ^ 2 := hrat

/-- The linear Taylor term cancels after multiplying by `exp (-u)`. -/
lemma exp_neg_mul_one_add_le_one (u : ℝ) :
    exp (-u) * (1 + u) ≤ 1 := by
  have h_exp_ge : 1 + u ≤ exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  calc
    exp (-u) * (1 + u) ≤ exp (-u) * exp u := by
      exact mul_le_mul_of_nonneg_left h_exp_ge (exp_nonneg _)
    _ = 1 := by
      rw [← exp_add]
      ring_nf
      simp

/-- Positive-parameter MGF bound for a centered square of a sub-Gaussian variable. -/
lemma integral_exp_centered_sq_le_exp_quadratic_nonneg {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_half : θ * C0 * exp 1 ≤ 1 / 2) :
    ∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ ≤
      exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2) := by
  set m : ℝ := ∫ ω, X ω ^ 2 ∂μ with hm_def
  set r : ℝ := θ * C0 * exp 1 with hr_def
  have hm_nonneg : 0 ≤ m := by
    rw [hm_def]
    exact integral_nonneg_of_ae (ae_of_all _ fun ω => sq_nonneg (X ω))
  have hr_nonneg : 0 ≤ r := by rw [hr_def]; positivity
  have hr_half : r ≤ 1 / 2 := by simpa only [hr_def] using hθ_half
  have hr_lt : r < 1 := by linarith
  have hsmall : θ * C0 * exp 1 < 1 := by simpa only [hr_def] using hr_lt
  have hbase :=
    integral_exp_mul_sq_le_one_add_linear_add_tail_of_hasSubgaussianMGF_of_le h hθ
      hC0 hc_le hsmall
  have hcenter :
      ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ =
        exp (-θ * m) * ∫ ω, exp (θ * X ω ^ 2) ∂μ := by
    calc
      ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ
          = ∫ ω, exp (-θ * m) * exp (θ * X ω ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            rw [← exp_add]
            congr 1
            ring
      _ = exp (-θ * m) * ∫ ω, exp (θ * X ω ^ 2) ∂μ := by
            rw [integral_const_mul]
  have htail_nonneg :
      0 ≤ exp 1 * (r ^ 2 * (1 - r)⁻¹) := by
    have hden_pos : 0 < 1 - r := by linarith
    positivity
  have hmul_base :
      exp (-θ * m) * ∫ ω, exp (θ * X ω ^ 2) ∂μ ≤
        exp (-θ * m) *
          (1 + θ * m + exp 1 * (r ^ 2 * (1 - r)⁻¹)) := by
    rw [← hm_def] at hbase
    exact mul_le_mul_of_nonneg_left hbase (exp_nonneg _)
  have hmain :
      exp (-θ * m) *
          (1 + θ * m + exp 1 * (r ^ 2 * (1 - r)⁻¹))
        ≤ 1 + exp 1 * (r ^ 2 * (1 - r)⁻¹) := by
    have hexp_le_one : exp (-θ * m) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hθ, hm_nonneg]
    have htail_mul :
        exp (-θ * m) * (exp 1 * (r ^ 2 * (1 - r)⁻¹)) ≤
          exp 1 * (r ^ 2 * (1 - r)⁻¹) := by
      calc
        exp (-θ * m) * (exp 1 * (r ^ 2 * (1 - r)⁻¹))
            ≤ 1 * (exp 1 * (r ^ 2 * (1 - r)⁻¹)) := by
              exact mul_le_mul_of_nonneg_right hexp_le_one htail_nonneg
        _ = exp 1 * (r ^ 2 * (1 - r)⁻¹) := by ring
    calc
      exp (-θ * m) *
          (1 + θ * m + exp 1 * (r ^ 2 * (1 - r)⁻¹))
          = exp (-(θ * m)) * (1 + θ * m) +
              exp (-θ * m) * (exp 1 * (r ^ 2 * (1 - r)⁻¹)) := by ring_nf
      _ ≤ 1 + exp 1 * (r ^ 2 * (1 - r)⁻¹) :=
          add_le_add (exp_neg_mul_one_add_le_one (θ * m)) htail_mul
  have htail_le :
      exp 1 * (r ^ 2 * (1 - r)⁻¹) ≤ 2 * exp 1 * r ^ 2 := by
    have hden_pos : 0 < 1 - r := by linarith
    have hinv_le : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hden_pos two_pos]
      linarith
    have hmul : r ^ 2 * (1 - r)⁻¹ ≤ r ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hinv_le (sq_nonneg r)
    calc
      exp 1 * (r ^ 2 * (1 - r)⁻¹) ≤ exp 1 * (r ^ 2 * 2) :=
        mul_le_mul_of_nonneg_left hmul (exp_pos 1).le
      _ = 2 * exp 1 * r ^ 2 := by ring
  calc
    ∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ
        = ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ := by rw [hm_def]
    _ = exp (-θ * m) * ∫ ω, exp (θ * X ω ^ 2) ∂μ := hcenter
    _ ≤ exp (-θ * m) *
          (1 + θ * m + exp 1 * (r ^ 2 * (1 - r)⁻¹)) := hmul_base
    _ ≤ 1 + exp 1 * (r ^ 2 * (1 - r)⁻¹) := hmain
    _ ≤ 1 + 2 * exp 1 * r ^ 2 := by linarith
    _ ≤ exp (2 * exp 1 * r ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * exp 1 * r ^ 2)
    _ = exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2) := by rw [hr_def]

/-- Negative-parameter MGF bound for a centered square of a sub-Gaussian variable. -/
lemma integral_exp_centered_sq_le_exp_quadratic_nonpos {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : θ ≤ 0)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0) :
    ∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ ≤
      exp (2 * exp 1 * ((-θ) * C0 * exp 1) ^ 2) := by
  set a : ℝ := -θ with ha_def
  set m : ℝ := ∫ ω, X ω ^ 2 ∂μ with hm_def
  set M4 : ℝ := ∫ ω, X ω ^ 4 ∂μ with hM4_def
  have ha_nonneg : 0 ≤ a := by rw [ha_def]; linarith
  have hX2_int : Integrable (fun ω => X ω ^ 2) μ := by
    exact integrable_pow_of_integrable_exp_mul
      (X := X) (t := 1) one_ne_zero
      (h.integrable_exp_mul 1)
      (h.integrable_exp_mul (-1)) 2
  have hX4_int : Integrable (fun ω => X ω ^ 4) μ := by
    exact integrable_pow_of_integrable_exp_mul
      (X := X) (t := 1) one_ne_zero
      (h.integrable_exp_mul 1)
      (h.integrable_exp_mul (-1)) 4
  have hneg_int : Integrable (fun ω => exp (-a * X ω ^ 2)) μ := by
    exact Integrable.of_bound
      ((hX2_int.aemeasurable.const_mul (-a)).exp.aestronglyMeasurable) 1 (by
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha_nonneg) (sq_nonneg (X ω)))
  have hpoly_int :
      Integrable (fun ω => 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4) μ :=
    ((integrable_const 1).sub (hX2_int.const_mul a)).add (hX4_int.const_mul (a ^ 2))
  have hneg_bound :
      ∫ ω, exp (-a * X ω ^ 2) ∂μ ≤ 1 - a * m + a ^ 2 * M4 := by
    have hpoint :
        (fun ω => exp (-a * X ω ^ 2)) ≤ᵐ[μ]
          fun ω => 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4 := by
      filter_upwards with ω
      have hbasic := exp_neg_le_one_sub_add_sq
        (mul_nonneg ha_nonneg (sq_nonneg (X ω)))
      calc
        exp (-a * X ω ^ 2) = exp (-(a * X ω ^ 2)) := by ring_nf
        _ ≤ 1 - (a * X ω ^ 2) + (a * X ω ^ 2) ^ 2 := hbasic
        _ = 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4 := by ring_nf
    calc
      ∫ ω, exp (-a * X ω ^ 2) ∂μ
          ≤ ∫ ω, 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4 ∂μ :=
            integral_mono_ae hneg_int hpoly_int hpoint
      _ = 1 - a * m + a ^ 2 * M4 := by
        calc
          ∫ ω, 1 - a * X ω ^ 2 + a ^ 2 * X ω ^ 4 ∂μ
              = ∫ ω, (1 - a * X ω ^ 2) + a ^ 2 * X ω ^ 4 ∂μ := by rfl
          _ = ∫ ω, 1 - a * X ω ^ 2 ∂μ + ∫ ω, a ^ 2 * X ω ^ 4 ∂μ := by
              rw [show (fun ω => (1 - a * X ω ^ 2) + a ^ 2 * X ω ^ 4) =
                (fun ω => 1 - a * X ω ^ 2) + (fun ω => a ^ 2 * X ω ^ 4) by
                rfl]
              exact integral_add ((integrable_const 1).sub (hX2_int.const_mul a))
                (hX4_int.const_mul (a ^ 2))
          _ = (1 - a * m) + a ^ 2 * M4 := by
              rw [integral_sub (integrable_const 1) (hX2_int.const_mul a)]
              rw [integral_const_mul, integral_const_mul]
              rw [hm_def, hM4_def]
              simp only [integral_const, probReal_univ, one_smul]
          _ = 1 - a * m + a ^ 2 * M4 := by ring_nf
  have hcenter :
      ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ =
        exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ := by
    calc
      ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ
          = ∫ ω, exp (a * m) * exp (-a * X ω ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            rw [← exp_add]
            congr 1
            rw [ha_def]
            ring_nf
      _ = exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ := by
            rw [integral_const_mul]
  have hM4_bound : M4 ≤ 2 * exp 1 * (C0 * exp 1) ^ 2 := by
    rw [hM4_def]
    exact integral_fourth_le_of_hasSubgaussianMGF_of_le h hC0 hc_le
  have hmgf_le_exp_M4 :
      exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ ≤ exp (a ^ 2 * M4) := by
    calc
      exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ
          ≤ exp (a * m) * (1 - a * m + a ^ 2 * M4) := by
            exact mul_le_mul_of_nonneg_left hneg_bound (exp_nonneg _)
      _ ≤ exp (a * m) * exp (-a * m + a ^ 2 * M4) := by
            exact mul_le_mul_of_nonneg_left
              (by linarith [Real.add_one_le_exp (-a * m + a ^ 2 * M4)])
              (exp_nonneg _)
      _ = exp (a ^ 2 * M4) := by
            rw [← exp_add]
            ring_nf
  have hquad_le :
      a ^ 2 * M4 ≤ a ^ 2 * (2 * exp 1 * (C0 * exp 1) ^ 2) :=
    mul_le_mul_of_nonneg_left hM4_bound (sq_nonneg a)
  calc
    ∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ
        = ∫ ω, exp (θ * (X ω ^ 2 - m)) ∂μ := by rw [hm_def]
    _ = exp (a * m) * ∫ ω, exp (-a * X ω ^ 2) ∂μ := hcenter
    _ ≤ exp (a ^ 2 * M4) := hmgf_le_exp_M4
    _ ≤ exp (a ^ 2 * (2 * exp 1 * (C0 * exp 1) ^ 2)) :=
        exp_le_exp.mpr hquad_le
    _ = exp (2 * exp 1 * ((-θ) * C0 * exp 1) ^ 2) := by
        rw [ha_def]
        ring_nf

end HansonWrightProof
end NLAlib
