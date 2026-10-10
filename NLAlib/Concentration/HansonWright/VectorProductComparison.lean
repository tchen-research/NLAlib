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
import NLAlib.Concentration.HansonWright.LinearFormComparison

/-!
# Hanson–Wright proof: VectorProductComparison

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

/-- Source-transport helper `integrable_exp_norm_toEuclideanCLM_randomVector_sq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integrable_exp_norm_toEuclideanCLM_randomVector_sq {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {K θ : ℝ} (hθ : 0 ≤ θ)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hsmall : θ * K ^ 2 * deterministicOperatorNorm A ^ 2 * exp 1 < 1) :
    Integrable (fun ω =>
      exp (θ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (randomVector X ω)‖ ^ 2)) μ := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ : Measure E := stdGaussian E
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let U : E →L[ℝ] E := ContinuousLinearMap.adjoint T
  let S : E →L[ℝ] E := ContinuousLinearMap.adjoint U ∘L U
  let hSpos : S.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self U).toLinearMap
  let s : ℝ := sqrt (2 * θ)
  let f : E × Ω → ℝ := fun p => exp (s * inner ℝ (U p.1) (randomVector X p.2))
  have hs_sq : s ^ 2 = 2 * θ := by
    dsimp [s]
    rw [sq_sqrt]
    nlinarith
  have hKθ_nonneg : 0 ≤ K ^ 2 * θ := mul_nonneg (sq_nonneg K) hθ
  have hUnorm : ‖U‖ = deterministicOperatorNorm A := by
    dsimp [U, T, deterministicOperatorNorm]
    exact ContinuousLinearMap.adjoint.norm_map _
  have hsmall_eig_lt :
      ∀ i : Fin (Module.finrank ℝ E),
        (K ^ 2 * θ) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 < 1 := by
    intro i
    have heig_le : hSpos.isSymmetric.eigenvalues rfl i ≤ ‖U‖ ^ 2 := by
      simpa only [S, hSpos] using eigenvalue_adjoint_comp_le_opNorm_sq U i
    have hstep :
        (K ^ 2 * θ) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 ≤
          (K ^ 2 * θ) * ‖U‖ ^ 2 * exp 1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heig_le hKθ_nonneg) (exp_nonneg 1)
    exact lt_of_le_of_lt hstep (by
      rw [hUnorm]
      nlinarith [hsmall])
  have hquad_int :
      Integrable (fun g : E => exp ((K ^ 2 * θ) * inner ℝ (S g) g)) γ :=
    integrable_exp_quadratic_stdGaussian S hSpos hKθ_nonneg hsmall_eig_lt
  have hf_aesm : AEStronglyMeasurable f (γ.prod μ) := by
    have hX_aemeas : AEMeasurable (randomVector X) μ :=
      randomVector_aemeasurable fun i => (hX_subG i).aemeasurable
    have hU_aemeas :
        AEMeasurable (fun p : E × Ω => U p.1) (γ.prod μ) :=
      AEMeasurable.comp_fst (μ := γ) (ν := μ) U.continuous.aemeasurable
    have hX_prod :
        AEMeasurable (fun p : E × Ω => randomVector X p.2) (γ.prod μ) :=
      AEMeasurable.comp_snd (μ := γ) (ν := μ) hX_aemeas
    have hinner :
        AEMeasurable
          (fun p : E × Ω => inner ℝ (U p.1) (randomVector X p.2)) (γ.prod μ) := by
      exact AEMeasurable.inner hU_aemeas hX_prod
    exact ((hinner.const_mul s).exp).aestronglyMeasurable
  have hinner_bound : (fun g : E => ∫ ω, f (g, ω) ∂μ) ≤ᵐ[γ]
      fun g : E => exp ((K ^ 2 * θ) * inner ℝ (S g) g) := by
    filter_upwards with g
    have hlin := inner_randomVector_hasSubgaussianMGF_of_iIndepFun h_indep hX_subG (U g)
    have hmgf := hlin.mgf_le s
    have hnorm_sq : ‖U g‖ ^ 2 = inner ℝ (S g) g := by
      simpa [S] using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left U g
    calc
      ∫ ω, f (g, ω) ∂μ
          = mgf (fun ω => inner ℝ (U g) (randomVector X ω)) μ s := by
            rfl
      _ ≤ exp ((K ^ 2 * ‖U g‖ ^ 2) * s ^ 2 / 2) := hmgf
      _ = exp ((K ^ 2 * θ) * inner ℝ (S g) g) := by
            rw [hs_sq, hnorm_sq]
            congr 1
            ring
  have hnorm_inner_bound : (fun g : E => ∫ ω, ‖f (g, ω)‖ ∂μ) ≤ᵐ[γ]
      fun g : E => exp ((K ^ 2 * θ) * inner ℝ (S g) g) := by
    filter_upwards [hinner_bound] with g hg
    have hnorm_eq : ∫ ω, ‖f (g, ω)‖ ∂μ = ∫ ω, f (g, ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      dsimp [f]
      rw [abs_of_nonneg (exp_nonneg _)]
    rwa [hnorm_eq]
  have hf_int : Integrable f (γ.prod μ) := by
    rw [integrable_prod_iff hf_aesm]
    constructor
    · filter_upwards with g
      exact
        (inner_randomVector_hasSubgaussianMGF_of_iIndepFun h_indep hX_subG (U g)).integrable_exp_mul s
    · have hnorm_outer_bound :
          (fun g : E => ‖∫ ω, ‖f (g, ω)‖ ∂μ‖) ≤ᵐ[γ]
            fun g : E => exp ((K ^ 2 * θ) * inner ℝ (S g) g) := by
        filter_upwards [hnorm_inner_bound] with g hg
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact hg
        · exact integral_nonneg fun ω => norm_nonneg _
      exact Integrable.mono' hquad_int hf_aesm.norm.integral_prod_right' hnorm_outer_bound
  have hleft_eq :
      (fun ω => exp (θ * ‖T (randomVector X ω)‖ ^ 2)) =
        fun ω => ∫ g : E, f (g, ω) ∂γ := by
    ext ω
    have hfg : (fun g : E => f (g, ω)) =
        fun g : E => exp (s * inner ℝ (T (randomVector X ω)) g) := by
      ext g
      dsimp [f, U]
      rw [ContinuousLinearMap.adjoint_inner_left T (randomVector X ω) g]
      rw [real_inner_comm]
    rw [hfg, integral_exp_innerSL_stdGaussian (E := E) (T (randomVector X ω)) s]
    rw [hs_sq]
    congr 1
    ring
  have hprod_inner_int :
      Integrable (fun ω => ∫ g : E, f (g, ω) ∂γ) μ :=
    (hf_int.swap).integral_prod_left
  rw [hleft_eq]
  exact hprod_inner_int

/-- Source-transport helper `integrable_exp_inner_toEuclideanCLM_randomVector_prod` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integrable_exp_inner_toEuclideanCLM_randomVector_prod {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {K l : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hsmall : (K ^ 2 * l ^ 2 / 2) * K ^ 2 * deterministicOperatorNorm A ^ 2 * exp 1 < 1) :
    Integrable
      (fun p : Ω × Ω =>
        exp (l * inner ℝ
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A (randomVector X p.1))
          (randomVector X p.2))) (μ.prod μ) := by
  let E := EuclideanSpace ℝ (Fin n)
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let θ : ℝ := K ^ 2 * l ^ 2 / 2
  let f : Ω × Ω → ℝ :=
    fun p => exp (l * inner ℝ (T (randomVector X p.1)) (randomVector X p.2))
  have hX_aemeas : AEMeasurable (randomVector X) μ :=
    randomVector_aemeasurable fun i => (hX_subG i).aemeasurable
  have hf_aesm : AEStronglyMeasurable f (μ.prod μ) := by
    have hleft :
        AEMeasurable (fun p : Ω × Ω => T (randomVector X p.1)) (μ.prod μ) :=
      T.continuous.aemeasurable.comp_aemeasurable
        (AEMeasurable.comp_fst (μ := μ) (ν := μ) hX_aemeas)
    have hright :
        AEMeasurable (fun p : Ω × Ω => randomVector X p.2) (μ.prod μ) :=
      AEMeasurable.comp_snd (μ := μ) (ν := μ) hX_aemeas
    have hinner :
        AEMeasurable
          (fun p : Ω × Ω => inner ℝ (T (randomVector X p.1)) (randomVector X p.2))
          (μ.prod μ) :=
      AEMeasurable.inner hleft hright
    exact ((hinner.const_mul l).exp).aestronglyMeasurable
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    positivity
  have hsquare_int :
      Integrable (fun ω =>
        exp (θ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (randomVector X ω)‖ ^ 2)) μ :=
    integrable_exp_norm_toEuclideanCLM_randomVector_sq A hθ_nonneg
      h_indep hX_subG (by simpa [θ, T] using hsmall)
  rw [integrable_prod_iff hf_aesm]
  constructor
  · filter_upwards with ω₁
    exact
      (inner_randomVector_hasSubgaussianMGF_of_iIndepFun h_indep hX_subG
        (T (randomVector X ω₁))).integrable_exp_mul l
  · have hinner_norm_bound :
        (fun ω₁ => ∫ ω₂, ‖f (ω₁, ω₂)‖ ∂μ) ≤ᵐ[μ]
          fun ω₁ => exp (θ * ‖T (randomVector X ω₁)‖ ^ 2) := by
      filter_upwards with ω₁
      have hnorm_eq :
          ∫ ω₂, ‖f (ω₁, ω₂)‖ ∂μ = ∫ ω₂, f (ω₁, ω₂) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω₂
        dsimp [f]
        rw [abs_of_nonneg (exp_nonneg _)]
      have hlin :=
        inner_randomVector_hasSubgaussianMGF_of_iIndepFun h_indep hX_subG
          (T (randomVector X ω₁))
      have hmgf := hlin.mgf_le l
      rw [hnorm_eq]
      calc
        ∫ ω₂, f (ω₁, ω₂) ∂μ
            = mgf (fun ω₂ => inner ℝ (T (randomVector X ω₁)) (randomVector X ω₂)) μ l := by
              rfl
        _ ≤ exp ((K ^ 2 * ‖T (randomVector X ω₁)‖ ^ 2) * l ^ 2 / 2) := hmgf
        _ = exp (θ * ‖T (randomVector X ω₁)‖ ^ 2) := by
              congr 1
              dsimp [θ]
              ring
    have houter_bound :
        (fun ω₁ => ‖∫ ω₂, ‖f (ω₁, ω₂)‖ ∂μ‖) ≤ᵐ[μ]
          fun ω₁ => exp (θ * ‖T (randomVector X ω₁)‖ ^ 2) := by
      filter_upwards [hinner_norm_bound] with ω₁ hω₁
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hω₁
      · exact integral_nonneg fun ω₂ => norm_nonneg _
    have hsquare_int' :
        Integrable
          (fun ω => exp (θ *
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (randomVector X ω)‖ ^ 2)) μ := by
      change Integrable (fun ω => exp (θ * ‖T (randomVector X ω)‖ ^ 2)) μ
      exact hsquare_int
    exact Integrable.mono' hsquare_int'
      hf_aesm.norm.integral_prod_right' houter_bound

/-- Source-transport helper `integral_exp_inner_toEuclideanCLM_randomVector_prod_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integral_exp_inner_toEuclideanCLM_randomVector_prod_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {K l : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hsmall : (K ^ 2 * l ^ 2 / 2) * K ^ 2 * deterministicOperatorNorm A ^ 2 * exp 1 ≤ 1 / 2) :
    ∫ p : Ω × Ω,
        exp (l * inner ℝ
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A (randomVector X p.1))
          (randomVector X p.2)) ∂(μ.prod μ) ≤
      exp (exp 1 ^ 2 * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2) := by
  let E := EuclideanSpace ℝ (Fin n)
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let θ : ℝ := K ^ 2 * l ^ 2 / 2
  let f : Ω × Ω → ℝ :=
    fun p => exp (l * inner ℝ (T (randomVector X p.1)) (randomVector X p.2))
  have hf_int : Integrable f (μ.prod μ) :=
    integrable_exp_inner_toEuclideanCLM_randomVector_prod A h_indep hX_subG (by
      exact lt_of_le_of_lt hsmall (by norm_num))
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    positivity
  have hsquare_bound :
      ∫ ω,
          exp (θ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (randomVector X ω)‖ ^ 2) ∂μ ≤
        exp (2 * exp 1 ^ 2 * θ * K ^ 2 * deterministicFrobeniusNorm A ^ 2) :=
    integral_exp_norm_toEuclideanCLM_randomVector_sq_le A hθ_nonneg
      h_indep hX_subG (by simpa [θ, T] using hsmall)
  have hsquare_int :
      Integrable (fun ω =>
        exp (θ * ‖T (randomVector X ω)‖ ^ 2)) μ := by
    change Integrable (fun ω =>
      exp (θ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (randomVector X ω)‖ ^ 2)) μ
    exact integrable_exp_norm_toEuclideanCLM_randomVector_sq
      (μ := μ) (A := A) (X := X) (K := K) (θ := θ)
      hθ_nonneg h_indep hX_subG (by
        exact lt_of_le_of_lt hsmall (by norm_num))
  have hinner_bound :
      (fun ω₁ => ∫ ω₂, f (ω₁, ω₂) ∂μ) ≤ᵐ[μ]
        fun ω₁ => exp (θ * ‖T (randomVector X ω₁)‖ ^ 2) := by
    filter_upwards with ω₁
    have hlin :=
      inner_randomVector_hasSubgaussianMGF_of_iIndepFun h_indep hX_subG
        (T (randomVector X ω₁))
    have hmgf := hlin.mgf_le l
    calc
      ∫ ω₂, f (ω₁, ω₂) ∂μ
          = mgf (fun ω₂ => inner ℝ (T (randomVector X ω₁)) (randomVector X ω₂)) μ l := by
            rfl
      _ ≤ exp ((K ^ 2 * ‖T (randomVector X ω₁)‖ ^ 2) * l ^ 2 / 2) := hmgf
      _ = exp (θ * ‖T (randomVector X ω₁)‖ ^ 2) := by
            congr 1
            dsimp [θ]
            ring
  calc
    ∫ p : Ω × Ω, f p ∂(μ.prod μ)
        = ∫ ω₁, ∫ ω₂, f (ω₁, ω₂) ∂μ ∂μ := by
            rw [integral_prod f hf_int]
    _ ≤ ∫ ω₁, exp (θ * ‖T (randomVector X ω₁)‖ ^ 2) ∂μ := by
            exact integral_mono_ae hf_int.integral_prod_left
              hsquare_int
              hinner_bound
    _ ≤ exp (2 * exp 1 ^ 2 * θ * K ^ 2 * deterministicFrobeniusNorm A ^ 2) := by
            exact hsquare_bound
    _ = exp (exp 1 ^ 2 * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2) := by
            congr 1
            dsimp [θ]
            ring

/-- Source-transport helper `integral_exp_quadraticForm_cutMatrix_eq_prod` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integral_exp_quadraticForm_cutMatrix_eq_prod {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) {X : Fin n → Ω → ℝ} {l : ℝ}
    (h_indep : iIndepFun X μ) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (hprod_int :
      Integrable
        (fun p : Ω × Ω =>
          exp (l * inner ℝ
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (cutMatrix A s) (randomVector X p.1))
            (randomVector X p.2))) (μ.prod μ)) :
    ∫ ω, exp (l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω)) ∂μ =
      ∫ p : Ω × Ω,
        exp (l * inner ℝ
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (cutMatrix A s) (randomVector X p.1))
          (randomVector X p.2)) ∂(μ.prod μ) := by
  let E := EuclideanSpace ℝ (Fin n)
  let U : Ω → E :=
    fun ω => coordinateMask ((Finset.univ : Finset (Fin n)) \ s) (randomVector X ω)
  let V : Ω → E := fun ω => coordinateMask s (randomVector X ω)
  let φ : Ω × Ω → E × E := fun p => (U p.1, V p.2)
  let ψ : Ω → E × E := fun ω => (U ω, V ω)
  let g : E × E → ℝ :=
    fun p => exp (l * inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A p.1) p.2)
  let F : Ω × Ω → ℝ :=
    fun p => exp (l * inner ℝ
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (cutMatrix A s) (randomVector X p.1))
      (randomVector X p.2))
  let H : Ω → ℝ :=
    fun ω => exp (l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω))
  have hU_meas : AEMeasurable U μ := by
    dsimp [U]
    exact coordinateMask_aemeasurable _ hX_meas
  have hV_meas : AEMeasurable V μ := by
    dsimp [V]
    exact coordinateMask_aemeasurable _ hX_meas
  have hψ_meas : AEMeasurable ψ μ := hU_meas.prodMk hV_meas
  have hφ_meas : AEMeasurable φ (μ.prod μ) :=
    (AEMeasurable.comp_fst (μ := μ) (ν := μ) hU_meas).prodMk
      (AEMeasurable.comp_snd (μ := μ) (ν := μ) hV_meas)
  have hUV_indep : U ⟂ᵢ[μ] V := by
    dsimp [U, V]
    exact coordinateMask_indepFun_compl h_indep hX_meas s
  have hmap_same : μ.map ψ = (μ.map U).prod (μ.map V) := by
    simpa [ψ] using
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hU_meas hV_meas).mp hUV_indep
  have hmap_prod : (μ.map U).prod (μ.map V) = (μ.prod μ).map φ := by
    simpa [φ] using measure_map_prod_map_of_aemeasurable (μ := μ) (ν := μ) hU_meas hV_meas
  have hg_aesm : AEStronglyMeasurable g ((μ.map U).prod (μ.map V)) := by
    dsimp [g]
    fun_prop
  have hg_aesm_prod : AEStronglyMeasurable g ((μ.prod μ).map φ) := by
    rwa [← hmap_prod]
  have hF_eq : F = g ∘ φ := by
    ext p
    dsimp [F, g, φ, U, V]
    rw [inner_toEuclideanCLM_cutMatrix_eq_inner_masks]
  have hcomp_int : Integrable (g ∘ φ) (μ.prod μ) := by
    rw [← hF_eq]
    exact hprod_int
  have hg_int_prod : Integrable g ((μ.prod μ).map φ) :=
    (integrable_map_measure hg_aesm_prod hφ_meas).2 hcomp_int
  have hg_int_same : Integrable g (μ.map ψ) := by
    rw [hmap_same, hmap_prod]
    exact hg_int_prod
  have hg_aesm_same : AEStronglyMeasurable g (μ.map ψ) := by
    rw [hmap_same]
    exact hg_aesm
  have hH_eq : H = g ∘ ψ := by
    ext ω
    change exp (l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω)) =
      exp (l * inner ℝ
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A
          (coordinateMask ((Finset.univ : Finset (Fin n)) \ s) (randomVector X ω)))
        (coordinateMask s (randomVector X ω)))
    rw [quadraticForm_eq_inner_toEuclideanCLM]
    rw [inner_toEuclideanCLM_cutMatrix_eq_inner_masks]
    rfl
  calc
    ∫ ω, exp (l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω)) ∂μ
        = ∫ ω, H ω ∂μ := by rfl
    _ = ∫ ω, (g ∘ ψ) ω ∂μ := by rw [hH_eq]
    _ = ∫ ω, g (ψ ω) ∂μ := by rfl
    _ = ∫ q, g q ∂(μ.map ψ) := by
        rw [integral_map hψ_meas hg_aesm_same]
    _ = ∫ q, g q ∂((μ.prod μ).map φ) := by
        rw [hmap_same, hmap_prod]
    _ = ∫ p : Ω × Ω, g (φ p) ∂(μ.prod μ) := by
        rw [integral_map hφ_meas hg_aesm_prod]
    _ = ∫ p : Ω × Ω, (g ∘ φ) p ∂(μ.prod μ) := by rfl
    _ = ∫ p : Ω × Ω, F p ∂(μ.prod μ) := by rw [hF_eq]

end HansonWrightProof
end NLAlib
