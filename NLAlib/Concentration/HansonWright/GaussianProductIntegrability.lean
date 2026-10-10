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
import NLAlib.Concentration.HansonWright.CenteredSquareBounds

/-!
# Hanson–Wright proof: GaussianProductIntegrability

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

/-- Square-exponential integrability from summability of the nonnegative moment series. -/
lemma integrable_exp_mul_sq_of_summable_integrals {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsum : Summable fun m : ℕ =>
      ∫ ω, θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ) ∂μ) :
    Integrable (fun ω => exp (θ * X ω ^ 2)) μ := by
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
  have hF_integral_nonneg : ∀ m : ℕ, 0 ≤ ∫ ω, F m ω ∂μ := by
    intro m
    exact integral_nonneg_of_ae (hF_nonneg m)
  have hF_lintegral_eq :
      (∑' m : ℕ, ∫⁻ ω, ENNReal.ofReal (F m ω) ∂μ) =
        ENNReal.ofReal (∑' m : ℕ, ∫ ω, F m ω ∂μ) := by
    calc (∑' m : ℕ, ∫⁻ ω, ENNReal.ofReal (F m ω) ∂μ)
        = ∑' m : ℕ, ENNReal.ofReal (∫ ω, F m ω ∂μ) := by
          congr with m
          exact (ofReal_integral_eq_lintegral_ofReal (hF_int m) (hF_nonneg m)).symm
      _ = ENNReal.ofReal (∑' m : ℕ, ∫ ω, F m ω ∂μ) := by
          exact (ENNReal.ofReal_tsum_of_nonneg hF_integral_nonneg hsum).symm
  have h_exp_lintegral_eq :
      ∫⁻ ω, ENNReal.ofReal (exp (θ * X ω ^ 2)) ∂μ =
        ∑' m : ℕ, ∫⁻ ω, ENNReal.ofReal (F m ω) ∂μ := by
    calc ∫⁻ ω, ENNReal.ofReal (exp (θ * X ω ^ 2)) ∂μ
        = ∫⁻ ω, ∑' m : ℕ, ENNReal.ofReal (F m ω) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards with ω
          have hsummable :
              Summable fun m : ℕ => F m ω := by
            convert Real.summable_pow_div_factorial (θ * X ω ^ 2) using 1
            ext m
            dsimp [F]
            rw [mul_pow, ← pow_mul]
          rw [exp_mul_sq_eq_tsum θ (X ω)]
          exact ENNReal.ofReal_tsum_of_nonneg
            (fun m => by
              show 0 ≤ θ ^ m * X ω ^ (2 * m) / (Nat.factorial m : ℝ)
              exact div_nonneg
                (mul_nonneg (pow_nonneg hθ m)
                  (Even.pow_nonneg (even_two.mul_right m) (X ω)))
                (Nat.cast_nonneg (Nat.factorial m))) hsummable
      _ = ∑' m : ℕ, ∫⁻ ω, ENNReal.ofReal (F m ω) ∂μ := by
          rw [lintegral_tsum]
          intro m
          exact (hF_int m).aemeasurable.ennreal_ofReal
  have h_exp_lintegral_ne_top :
      ∫⁻ ω, ENNReal.ofReal (exp (θ * X ω ^ 2)) ∂μ ≠ ⊤ := by
    rw [h_exp_lintegral_eq, hF_lintegral_eq]
    exact ENNReal.ofReal_ne_top
  exact (lintegral_ofReal_ne_top_iff_integrable
    ((h.aemeasurable.pow_const 2).const_mul θ).exp.aestronglyMeasurable
    (ae_of_all _ fun ω => (exp_pos _).le)).mp h_exp_lintegral_ne_top

/-- Square-exponential integrability for a sub-Gaussian variable at small positive parameter. -/
lemma integrable_exp_mul_sq_of_hasSubgaussianMGF {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hθ_small : θ * ((c : ℝ) + 1) * exp 1 < 1) :
    Integrable (fun ω => exp (θ * X ω ^ 2)) μ :=
  integrable_exp_mul_sq_of_summable_integrals h hθ
    (summable_integral_exp_sq_series_of_hasSubgaussianMGF h hθ hθ_small)

/-- Small-parameter square-exponential integrability using a positive proxy `C0 ≥ c`. -/
lemma integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ} (hθ : 0 ≤ θ)
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_small : θ * C0 * exp 1 < 1) :
    Integrable (fun ω => exp (θ * X ω ^ 2)) μ :=
  integrable_exp_mul_sq_of_summable_integrals h hθ
    (summable_integral_exp_sq_series_of_hasSubgaussianMGF_of_le h hθ hC0 hc_le hθ_small)

/-- Gaussian square-form integrability for a positive symmetric operator, under the
strict version of the same coordinate smallness condition. -/
lemma integrable_exp_quadratic_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : E →L[ℝ] E) (hTpos : T.toLinearMap.IsPositive) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsmall : ∀ i : Fin (Module.finrank ℝ E),
      θ * hTpos.isSymmetric.eigenvalues rfl i * exp 1 < 1) :
    Integrable (fun x : E => exp (θ * inner ℝ (T x) x)) (stdGaussian E) := by
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
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integrable_map_measure hf_aesm hsynth_aemeas]
  refine (MeasureTheory.Integrable.fintype_prod (𝕜 := ℝ)
    (ι := Fin (Module.finrank ℝ E)) (E := ℝ)
    (f := fun i x => exp ((θ * lam i) * x ^ 2))
    (μ := fun _ => gaussianReal 0 1) ?_).congr ?_
  · intro i
    have hθi : 0 ≤ θ * lam i := mul_nonneg hθ (hnonneg i)
    exact integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le
      (μ := gaussianReal 0 1) hasSubgaussianMGF_id_gaussianReal_zero_one
      (θ := θ * lam i) (C0 := 1) hθi (by norm_num) (by norm_num) (by
        simpa [mul_assoc] using hsmall i)
  · filter_upwards with z
    exact (hpoint z).symm

/-- Integrability of the exponential of a Gaussian bilinear form. -/
lemma integrable_exp_inner_toEuclideanCLM_prod_stdGaussian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {l : ℝ}
    (hsmall : (l ^ 2 / 2) * deterministicOperatorNorm A ^ 2 * exp 1 < 1) :
    Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        exp (l * inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A p.1) p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ : Measure E := stdGaussian E
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let S : E →L[ℝ] E := ContinuousLinearMap.adjoint T ∘L T
  let hSpos : S.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self T).toLinearMap
  let f : E × E → ℝ := fun p => exp (l * inner ℝ (T p.1) p.2)
  have hf_aesm : AEStronglyMeasurable f (γ.prod γ) := by
    dsimp [f]
    fun_prop
  have hθ_nonneg : 0 ≤ l ^ 2 / 2 := by positivity
  have hsmall_eig :
      ∀ i : Fin (Module.finrank ℝ E),
        (l ^ 2 / 2) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 < 1 := by
    intro i
    have heig_le : hSpos.isSymmetric.eigenvalues rfl i ≤ ‖T‖ ^ 2 := by
      simpa only [S, hSpos] using eigenvalue_adjoint_comp_le_opNorm_sq T i
    have hcoef_nonneg : 0 ≤ l ^ 2 / 2 := by positivity
    have hstep :
        (l ^ 2 / 2) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 ≤
          (l ^ 2 / 2) * ‖T‖ ^ 2 * exp 1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heig_le hcoef_nonneg) (exp_nonneg 1)
    have hnorm : ‖T‖ = deterministicOperatorNorm A := (Matrix.cstar_norm_def A).symm
    rw [hnorm] at hstep
    exact lt_of_le_of_lt hstep hsmall
  have hquad_int :
      Integrable (fun y : E => exp ((l ^ 2 / 2) * inner ℝ (S y) y)) γ :=
    integrable_exp_quadratic_stdGaussian S hSpos hθ_nonneg hsmall_eig
  rw [integrable_prod_iff hf_aesm]
  constructor
  · filter_upwards with y
    change Integrable (fun x : E => exp (l * inner ℝ (T y) x)) γ
    exact integrable_exp_innerSL_stdGaussian (E := E) (T y) l
  · have houter_eq :
        (fun y : E => ∫ x : E, ‖f (y, x)‖ ∂γ) =ᵐ[γ]
          fun y : E => exp ((l ^ 2 / 2) * inner ℝ (S y) y) := by
      filter_upwards with y
      have hinner :
          ∫ x : E, ‖f (y, x)‖ ∂γ =
            ∫ x : E, exp (l * inner ℝ (T y) x) ∂γ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [f]
        rw [abs_of_nonneg (exp_nonneg _)]
      rw [hinner, integral_exp_innerSL_stdGaussian (E := E) (T y) l]
      have hnorm_sq : ‖T y‖ ^ 2 = inner ℝ (S y) y := by
        simpa [S] using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T y
      rw [hnorm_sq]
      ring_nf
    exact hquad_int.congr houter_eq.symm

/-- A Frobenius-scale bound for the exponential moment of a Gaussian bilinear form. -/
lemma integral_exp_inner_toEuclideanCLM_prod_stdGaussian_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {l : ℝ}
    (hsmall : (l ^ 2 / 2) * deterministicOperatorNorm A ^ 2 * exp 1 ≤ 1 / 2) :
    ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        exp (l * inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A p.1) p.2)
      ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) ≤
      exp (exp 1 ^ 2 * l ^ 2 * deterministicFrobeniusNorm A ^ 2) := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ : Measure E := stdGaussian E
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let S : E →L[ℝ] E := ContinuousLinearMap.adjoint T ∘L T
  let hSpos : S.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self T).toLinearMap
  let f : E × E → ℝ := fun p => exp (l * inner ℝ (T p.1) p.2)
  have hf_int : Integrable f (γ.prod γ) :=
    integrable_exp_inner_toEuclideanCLM_prod_stdGaussian A (by
      exact lt_of_le_of_lt hsmall (by norm_num))
  have hθ_nonneg : 0 ≤ l ^ 2 / 2 := by positivity
  have hsmall_eig :
      ∀ i : Fin (Module.finrank ℝ E),
        (l ^ 2 / 2) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 ≤ 1 / 2 := by
    intro i
    have heig_le : hSpos.isSymmetric.eigenvalues rfl i ≤ ‖T‖ ^ 2 := by
      simpa only [S, hSpos] using eigenvalue_adjoint_comp_le_opNorm_sq T i
    have hcoef_nonneg : 0 ≤ l ^ 2 / 2 := by positivity
    have hstep :
        (l ^ 2 / 2) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 ≤
          (l ^ 2 / 2) * ‖T‖ ^ 2 * exp 1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heig_le hcoef_nonneg) (exp_nonneg 1)
    have hnorm : ‖T‖ = deterministicOperatorNorm A := (Matrix.cstar_norm_def A).symm
    rw [hnorm] at hstep
    exact hstep.trans hsmall
  have hsum_eq :
      (∑ i : Fin (Module.finrank ℝ E), hSpos.isSymmetric.eigenvalues rfl i) =
        frobeniusNormSq A := by
    have htrace_eigs :
        (LinearMap.trace ℝ E) S.toLinearMap =
          ∑ i : Fin (Module.finrank ℝ E), hSpos.isSymmetric.eigenvalues rfl i := by
      simpa using hSpos.isSymmetric.trace_eq_sum_eigenvalues
        (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
    have htrace_frob :
        (LinearMap.trace ℝ E) S.toLinearMap = frobeniusNormSq A := by
      simpa [E, S, T] using trace_adjoint_comp_toEuclideanCLM_eq_frobeniusNormSq A
    exact htrace_eigs.symm.trans htrace_frob
  have hinner_eq :
      (fun y : E => ∫ x : E, f (y, x) ∂γ) =ᵐ[γ]
        fun y : E => exp ((l ^ 2 / 2) * inner ℝ (S y) y) := by
    filter_upwards with y
    rw [integral_exp_innerSL_stdGaussian (E := E) (T y) l]
    have hnorm_sq : ‖T y‖ ^ 2 = inner ℝ (S y) y := by
      simpa [S] using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T y
    rw [hnorm_sq]
    ring_nf
  calc
    ∫ p : E × E, f p ∂(γ.prod γ)
        = ∫ y : E, ∫ x : E, f (y, x) ∂γ ∂γ := by
          rw [integral_prod f hf_int]
    _ = ∫ y : E, exp ((l ^ 2 / 2) * inner ℝ (S y) y) ∂γ := by
          exact integral_congr_ae hinner_eq
    _ ≤ exp (2 * exp 1 ^ 2 * (l ^ 2 / 2) *
          (∑ i : Fin (Module.finrank ℝ E), hSpos.isSymmetric.eigenvalues rfl i)) :=
          integral_exp_quadratic_stdGaussian_le S hSpos hθ_nonneg hsmall_eig
    _ = exp (exp 1 ^ 2 * l ^ 2 * deterministicFrobeniusNorm A ^ 2) := by
          rw [hsum_eq, frobeniusNorm_sq]
          congr 1
          ring

/-- Local exponential integrability for centered squares of sub-Gaussian variables. -/
lemma integrable_exp_centered_sq_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ}
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_abs : |θ| * C0 * exp 1 < 1) :
    Integrable (fun ω => exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ))) μ := by
  set m : ℝ := ∫ ω, X ω ^ 2 ∂μ with hm_def
  rcases le_total 0 θ with hθ_nonneg | hθ_nonpos
  · have hsmall : θ * C0 * exp 1 < 1 := by
      simpa [abs_of_nonneg hθ_nonneg] using hθ_abs
    have hsq_int :=
      integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le h hθ_nonneg hC0 hc_le hsmall
    convert hsq_int.const_mul (exp (-θ * m)) using 1
    ext ω
    rw [← exp_add]
    rw [hm_def]
    ring_nf
  · set a : ℝ := -θ with ha_def
    have ha_nonneg : 0 ≤ a := by rw [ha_def]; linarith
    have hX2_int : Integrable (fun ω => X ω ^ 2) μ := by
      exact integrable_pow_of_integrable_exp_mul
        (X := X) (t := 1) one_ne_zero
        (h.integrable_exp_mul 1)
        (h.integrable_exp_mul (-1)) 2
    have hneg_int : Integrable (fun ω => exp (-a * X ω ^ 2)) μ := by
      exact Integrable.of_bound
        ((hX2_int.aemeasurable.const_mul (-a)).exp.aestronglyMeasurable) 1 (by
          filter_upwards with ω
          rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha_nonneg) (sq_nonneg (X ω)))
    convert hneg_int.const_mul (exp (a * m)) using 1
    ext ω
    rw [← exp_add]
    rw [hm_def, ha_def]
    ring_nf

/-- The MGF of the identity under a push-forward law is the MGF of the original variable. -/
lemma mgf_id_map_eq {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (t : ℝ) :
    mgf id (μ.map X) t = mgf X μ t := by
  change (∫ x : ℝ, exp (t * id x) ∂(μ.map X)) =
    ∫ ω, exp (t * X ω) ∂μ
  exact integral_map hX ((measurable_id'.const_mul t).exp.aestronglyMeasurable)

/-- Source-transport helper `integrable_exp_mul_id_map` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integrable_exp_mul_id_map {μ : Measure Ω} {X : Ω → ℝ}
    {t : ℝ} (hX : AEMeasurable X μ) (h : Integrable (fun ω => exp (t * X ω)) μ) :
    Integrable (fun x : ℝ => exp (t * id x)) (μ.map X) := by
  rw [integrable_map_measure]
  · simpa only [Function.comp_def, id_eq] using h
  · fun_prop
  · exact hX

/-- Source-transport helper `hasSubgaussianMGF_id_map` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma hasSubgaussianMGF_id_map {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) :
    HasSubgaussianMGF id c (μ.map X) where
  integrable_exp_mul t := integrable_exp_mul_id_map h.aemeasurable (h.integrable_exp_mul t)
  mgf_le t := by
    rw [mgf_id_map_eq h.aemeasurable t]
    exact h.mgf_le t

/-- Source-transport helper `integrable_exp_mul_snd_fst_prod_of_hasSubgaussianMGF_of_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integrable_exp_mul_snd_fst_prod_of_hasSubgaussianMGF_of_le
    {νX νY : Measure ℝ} [IsProbabilityMeasure νX] [IsProbabilityMeasure νY]
    {cX cY : ℝ≥0} (hX : HasSubgaussianMGF id cX νX)
    (hY : HasSubgaussianMGF id cY νY) {C0 θ : ℝ}
    (hC0 : 0 < C0) (hcX : (cX : ℝ) ≤ C0) (hcY : (cY : ℝ) ≤ C0)
    (hθ_half : (C0 * θ ^ 2 / 2) * C0 * exp 1 ≤ 1 / 2) :
    Integrable (fun p : ℝ × ℝ => exp (θ * p.2 * p.1)) (νY.prod νX) := by
  let f : ℝ × ℝ → ℝ := fun p => exp (θ * p.2 * p.1)
  have hf_aesm : AEStronglyMeasurable f (νY.prod νX) := by
    dsimp [f]
    fun_prop
  rw [integrable_prod_iff hf_aesm]
  constructor
  · filter_upwards with y
    have hinner := hX.integrable_exp_mul (θ * y)
    convert hinner using 1
    ext x
    dsimp [f]
    ring_nf
  · have hθ2_nonneg : 0 ≤ C0 * θ ^ 2 / 2 := by positivity
    have hbound_int :
        Integrable (fun y : ℝ => exp ((C0 * θ ^ 2 / 2) * y ^ 2)) νY :=
      integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le hY hθ2_nonneg hC0 hcY (by
        linarith [hθ_half])
    refine Integrable.mono' hbound_int ?_ ?_
    · exact hf_aesm.norm.integral_prod_right'
    · filter_upwards with y
      have hinner_eq :
          ∫ x, ‖f (y, x)‖ ∂νX = mgf id νX (θ * y) := by
        unfold mgf
        apply integral_congr_ae
        filter_upwards with x
        dsimp [f]
        rw [abs_of_nonneg (exp_nonneg _)]
        ring_nf
      have hmgf := hX.mgf_le (θ * y)
      have hquad_le :
          (cX : ℝ) * (θ * y) ^ 2 / 2 ≤ C0 * θ ^ 2 * y ^ 2 / 2 := by
        have hnonneg : 0 ≤ (θ * y) ^ 2 / 2 := by positivity
        calc
          (cX : ℝ) * (θ * y) ^ 2 / 2 =
              (cX : ℝ) * ((θ * y) ^ 2 / 2) := by ring_nf
          _ ≤ C0 * ((θ * y) ^ 2 / 2) := mul_le_mul_of_nonneg_right hcX hnonneg
          _ = C0 * θ ^ 2 * y ^ 2 / 2 := by ring_nf
      have hle :
          ∫ x, ‖f (y, x)‖ ∂νX ≤ exp ((C0 * θ ^ 2 / 2) * y ^ 2) := by
        rw [hinner_eq]
        calc
          mgf id νX (θ * y) ≤ exp ((cX : ℝ) * (θ * y) ^ 2 / 2) := hmgf
          _ ≤ exp (C0 * θ ^ 2 * y ^ 2 / 2) := exp_le_exp.mpr hquad_le
          _ = exp ((C0 * θ ^ 2 / 2) * y ^ 2) := by ring_nf
      rw [Real.norm_eq_abs, abs_of_nonneg ?_]
      · exact hle
      · exact integral_nonneg fun x => norm_nonneg _

end HansonWrightProof
end NLAlib
