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
import NLAlib.Concentration.HansonWright.GaussianProductIntegrability

/-!
# Hanson–Wright proof: DiagonalCGF

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

/-- Source-transport helper `integral_exp_mul_snd_fst_prod_le_of_hasSubgaussianMGF_of_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integral_exp_mul_snd_fst_prod_le_of_hasSubgaussianMGF_of_le
    {νX νY : Measure ℝ} [IsProbabilityMeasure νX] [IsProbabilityMeasure νY]
    {cX cY : ℝ≥0} (hX : HasSubgaussianMGF id cX νX)
    (hY : HasSubgaussianMGF id cY νY) {C0 θ : ℝ}
    (hC0 : 0 < C0) (hcX : (cX : ℝ) ≤ C0) (hcY : (cY : ℝ) ≤ C0)
    (hθ_half : (C0 * θ ^ 2 / 2) * C0 * exp 1 ≤ 1 / 2) :
    ∫ p : ℝ × ℝ, exp (θ * p.2 * p.1) ∂(νY.prod νX) ≤
      exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) := by
  let f : ℝ × ℝ → ℝ := fun p => exp (θ * p.2 * p.1)
  have hf_int :
      Integrable f (νY.prod νX) :=
    integrable_exp_mul_snd_fst_prod_of_hasSubgaussianMGF_of_le
      hX hY hC0 hcX hcY hθ_half
  have hθ2_nonneg : 0 ≤ C0 * θ ^ 2 / 2 := by positivity
  have hbound_int :
      Integrable (fun y : ℝ => exp ((C0 * θ ^ 2 / 2) * y ^ 2)) νY :=
    integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le hY hθ2_nonneg hC0 hcY (by
      linarith [hθ_half])
  have houter_bound :
      (fun y : ℝ => ∫ x, f (y, x) ∂νX) ≤ᵐ[νY]
        fun y : ℝ => exp ((C0 * θ ^ 2 / 2) * y ^ 2) := by
    filter_upwards with y
    have hinner_eq :
        ∫ x, f (y, x) ∂νX = mgf id νX (θ * y) := by
      unfold mgf
      apply integral_congr_ae
      filter_upwards with x
      dsimp [f]
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
    rw [hinner_eq]
    calc
      mgf id νX (θ * y) ≤ exp ((cX : ℝ) * (θ * y) ^ 2 / 2) := hmgf
      _ ≤ exp (C0 * θ ^ 2 * y ^ 2 / 2) := exp_le_exp.mpr hquad_le
      _ = exp ((C0 * θ ^ 2 / 2) * y ^ 2) := by ring_nf
  calc
    ∫ p : ℝ × ℝ, exp (θ * p.2 * p.1) ∂(νY.prod νX)
        = ∫ y, ∫ x, f (y, x) ∂νX ∂νY := by
          rw [integral_prod f hf_int]
    _ ≤ ∫ y, exp ((C0 * θ ^ 2 / 2) * y ^ 2) ∂νY := by
          exact integral_mono_ae hf_int.integral_prod_left hbound_int houter_bound
    _ ≤ exp (2 * exp 1 * ((C0 * θ ^ 2 / 2) * C0 * exp 1)) :=
          integral_exp_mul_sq_le_exp_linear_of_hasSubgaussianMGF_of_le
            hY hθ2_nonneg hC0 hcY hθ_half
    _ = exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) := by
          congr 1
          ring_nf

/-- Source-transport helper `integrable_exp_mul_prod_of_indepFun_hasSubgaussianMGF_of_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integrable_exp_mul_prod_of_indepFun_hasSubgaussianMGF_of_le
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (h_indep : X ⟂ᵢ[μ] Y)
    {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) {C0 θ : ℝ}
    (hC0 : 0 < C0) (hcX : (cX : ℝ) ≤ C0) (hcY : (cY : ℝ) ≤ C0)
    (hθ_half : (C0 * θ ^ 2 / 2) * C0 * exp 1 ≤ 1 / 2) :
    Integrable (fun ω => exp (θ * X ω * Y ω)) μ := by
  let φ : Ω → ℝ × ℝ := fun ω => (Y ω, X ω)
  let g : ℝ × ℝ → ℝ := fun p => exp (θ * p.2 * p.1)
  have hφ : AEMeasurable φ μ :=
    (hY.aestronglyMeasurable.prodMk hX.aestronglyMeasurable).aemeasurable
  have hg : AEStronglyMeasurable g (μ.map φ) := by
    dsimp [g]
    fun_prop
  have : IsProbabilityMeasure (μ.map X) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map Y) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hY.aemeasurable
  have hprod_int :
      Integrable g ((μ.map Y).prod (μ.map X)) :=
    integrable_exp_mul_snd_fst_prod_of_hasSubgaussianMGF_of_le
      (νX := μ.map X) (νY := μ.map Y)
      (hasSubgaussianMGF_id_map hX) (hasSubgaussianMGF_id_map hY)
      hC0 hcX hcY hθ_half
  have hmap_eq :
      μ.map φ = (μ.map Y).prod (μ.map X) := by
    simpa [φ] using
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hY.aemeasurable hX.aemeasurable).mp h_indep.symm
  have hmap_int : Integrable g (μ.map φ) := by
    rwa [hmap_eq]
  have hcomp := (integrable_map_measure hg hφ).1 hmap_int
  convert hcomp using 1
  rfl

/-- Source-transport helper `integral_exp_mul_prod_le_of_indepFun_hasSubgaussianMGF_of_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integral_exp_mul_prod_le_of_indepFun_hasSubgaussianMGF_of_le
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (h_indep : X ⟂ᵢ[μ] Y)
    {cX cY : ℝ≥0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) {C0 θ : ℝ}
    (hC0 : 0 < C0) (hcX : (cX : ℝ) ≤ C0) (hcY : (cY : ℝ) ≤ C0)
    (hθ_half : (C0 * θ ^ 2 / 2) * C0 * exp 1 ≤ 1 / 2) :
    ∫ ω, exp (θ * X ω * Y ω) ∂μ ≤ exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) := by
  let φ : Ω → ℝ × ℝ := fun ω => (Y ω, X ω)
  let g : ℝ × ℝ → ℝ := fun p => exp (θ * p.2 * p.1)
  have hφ : AEMeasurable φ μ :=
    (hY.aestronglyMeasurable.prodMk hX.aestronglyMeasurable).aemeasurable
  have hg : AEStronglyMeasurable g (μ.map φ) := by
    dsimp [g]
    fun_prop
  have : IsProbabilityMeasure (μ.map X) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map Y) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmap_eq :
      μ.map φ = (μ.map Y).prod (μ.map X) := by
    simpa [φ] using
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hY.aemeasurable hX.aemeasurable).mp h_indep.symm
  have hprod_bound :
      ∫ p : ℝ × ℝ, g p ∂((μ.map Y).prod (μ.map X)) ≤
        exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) :=
    integral_exp_mul_snd_fst_prod_le_of_hasSubgaussianMGF_of_le
      (νX := μ.map X) (νY := μ.map Y)
      (hasSubgaussianMGF_id_map hX) (hasSubgaussianMGF_id_map hY)
      hC0 hcX hcY hθ_half
  calc
    ∫ ω, exp (θ * X ω * Y ω) ∂μ
        = ∫ p : ℝ × ℝ, g p ∂(μ.map φ) := by
          rw [integral_map hφ hg]
    _ = ∫ p : ℝ × ℝ, g p ∂((μ.map Y).prod (μ.map X)) := by rw [hmap_eq]
    _ ≤ exp (exp 1 ^ 2 * C0 ^ 2 * θ ^ 2) := hprod_bound

/-- CGF bound for a centered square of a sub-Gaussian variable. -/
lemma centered_sq_cgf_le_of_hasSubgaussianMGF_of_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {θ C0 : ℝ}
    (hC0 : 0 < C0) (hc_le : (c : ℝ) ≤ C0)
    (hθ_abs : |θ| * C0 * exp 1 ≤ 1 / 2) :
    cgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ ≤
      2 * exp 1 * (θ * C0 * exp 1) ^ 2 := by
  have hθ_abs_lt : |θ| * C0 * exp 1 < 1 := by
    linarith
  have hint := integrable_exp_centered_sq_of_hasSubgaussianMGF_of_le h hC0 hc_le hθ_abs_lt
  have hmgf_pos :
      0 < mgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ :=
    mgf_pos hint
  have hmgf_le :
      mgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ ≤
        exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2) := by
    rcases le_total 0 θ with hθ_nonneg | hθ_nonpos
    · have hhalf : θ * C0 * exp 1 ≤ 1 / 2 := by
        rw [abs_of_nonneg hθ_nonneg] at hθ_abs
        exact hθ_abs
      change (∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ) ≤ _
      exact integral_exp_centered_sq_le_exp_quadratic_nonneg h hθ_nonneg hC0 hc_le hhalf
    · have hbound :=
        integral_exp_centered_sq_le_exp_quadratic_nonpos h hθ_nonpos hC0 hc_le
      calc
        mgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ
            ≤ exp (2 * exp 1 * ((-θ) * C0 * exp 1) ^ 2) := by
              change (∫ ω, exp (θ * (X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ)) ∂μ) ≤ _
              exact hbound
        _ = exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2) := by ring_nf
  calc
    cgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ
        = log (mgf (fun ω => X ω ^ 2 - ∫ ω, X ω ^ 2 ∂μ) μ θ) := rfl
    _ ≤ log (exp (2 * exp 1 * (θ * C0 * exp 1) ^ 2)) :=
        log_le_log hmgf_pos hmgf_le
    _ = 2 * exp 1 * (θ * C0 * exp 1) ^ 2 := by rw [log_exp]

/-- The centered diagonal part of a quadratic form. -/
def diagonalCenteredQuadraticForm {n : ℕ} (μ : Measure Ω)
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, A i i * (X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂μ)

/-- Source-transport helper `cgf_const_mul` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma cgf_const_mul {μ : Measure Ω} {Y : Ω → ℝ} (a θ : ℝ) :
    cgf (fun ω => a * Y ω) μ θ = cgf Y μ (a * θ) := by
  rw [cgf, cgf, mgf_const_mul]

/-- Source-transport helper `iIndepFun_centered_sq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma iIndepFun_centered_sq {μ : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ}
    (h_indep : iIndepFun X μ) :
    iIndepFun (fun i => fun ω => X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂μ) μ := by
  simpa only [Function.comp_def] using
    h_indep.comp
      (fun i x => x ^ 2 - ∫ ω, X i ω ^ 2 ∂μ)
      (fun _ => by fun_prop)

/-- Source-transport helper `iIndepFun.integrable_exp_mul_sum₀` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma iIndepFun.integrable_exp_mul_sum₀ {ι : Type*} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, AEMeasurable (X i) μ)
    {s : Finset ι} {t : ℝ}
    (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    Integrable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi_notin_s h_rec =>
      have h_int_s : ∀ j ∈ s, Integrable (fun ω : Ω => exp (t * X j ω)) μ :=
        fun j hj => h_int j (Finset.mem_insert_of_mem hj)
      specialize h_rec h_int_s
      rw [Finset.sum_insert hi_notin_s]
      refine IndepFun.integrable_exp_mul_add ?_ (h_int i (Finset.mem_insert_self _ _)) h_rec
      exact (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi_notin_s).symm

/-- Source-transport helper `diagonalCenteredQuadraticForm_cgf_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma diagonalCenteredQuadraticForm_cgf_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C θ : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hC_domain : exp 1 ≤ C) (hC_quad : 2 * exp 1 ^ 3 ≤ C)
    (hOp : 0 < deterministicOperatorNorm A)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hθ : |θ| ≤ (2 * C * K ^ 2 * deterministicOperatorNorm A)⁻¹) :
    cgf (diagonalCenteredQuadraticForm μ A X) μ θ ≤
      C * θ ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by
  let Y : Fin n → Ω → ℝ :=
    fun i ω => X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂μ
  let Z : Fin n → Ω → ℝ := fun i ω => A i i * Y i ω
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hK
  have hKsq_nonneg : 0 ≤ K ^ 2 := hKsq_pos.le
  have hC0_le : ((⟨K ^ 2, sq_nonneg K⟩ : ℝ≥0) : ℝ) ≤ K ^ 2 := by simp
  have hscale :
      |θ| * K ^ 2 * deterministicOperatorNorm A ≤ 1 / (2 * C) := by
    have hfactor_nonneg : 0 ≤ K ^ 2 * deterministicOperatorNorm A :=
      mul_nonneg hKsq_nonneg (operatorNorm_nonneg A)
    calc
      |θ| * K ^ 2 * deterministicOperatorNorm A
          = |θ| * (K ^ 2 * deterministicOperatorNorm A) := by ring_nf
      _ ≤ (2 * C * K ^ 2 * deterministicOperatorNorm A)⁻¹ * (K ^ 2 * deterministicOperatorNorm A) :=
          mul_le_mul_of_nonneg_right hθ hfactor_nonneg
      _ = 1 / (2 * C) := by
          field_simp [hC.ne', hKsq_pos.ne', hOp.ne']
  have hhalf_i : ∀ i, |A i i * θ| * K ^ 2 * exp 1 ≤ 1 / 2 := by
    intro i
    have hdiag := abs_diag_le_operatorNorm A i
    have hθ_abs_nonneg : 0 ≤ |θ| := abs_nonneg θ
    have hle_op :
        |θ| * |A i i| * K ^ 2 ≤ |θ| * deterministicOperatorNorm A * K ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiag hθ_abs_nonneg) hKsq_nonneg
    calc
      |A i i * θ| * K ^ 2 * exp 1
          = (|θ| * |A i i| * K ^ 2) * exp 1 := by
              rw [abs_mul]
              ring_nf
      _ ≤ (|θ| * deterministicOperatorNorm A * K ^ 2) * exp 1 :=
          mul_le_mul_of_nonneg_right hle_op (exp_nonneg 1)
      _ = (|θ| * K ^ 2 * deterministicOperatorNorm A) * exp 1 := by ring_nf
      _ ≤ (1 / (2 * C)) * exp 1 :=
          mul_le_mul_of_nonneg_right hscale (exp_nonneg 1)
      _ ≤ 1 / 2 := by
          have hdiv : exp 1 / C ≤ 1 := (div_le_one hC).mpr hC_domain
          calc
            (1 / (2 * C)) * exp 1 = (1 / 2) * (exp 1 / C) := by
              field_simp [hC.ne']
            _ ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left hdiv (by norm_num)
            _ = 1 / 2 := by norm_num
  have hZ_indep : iIndepFun Z μ := by
    have hY_indep : iIndepFun Y μ := by
      simpa only [Y] using iIndepFun_centered_sq (μ := μ) (X := X) h_indep
    simpa only [Z, Function.comp_def] using
      hY_indep.comp (fun i x => A i i * x) (fun _ => by fun_prop)
  have hZ_meas : ∀ i, AEMeasurable (Z i) μ := by
    intro i
    change AEMeasurable
      (fun ω => A i i * (X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂μ)) μ
    exact (((hX_subG i).aemeasurable.pow_const 2).sub_const _).const_mul _
  have hZ_int :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Integrable (fun ω => exp (θ * Z i ω)) μ := by
    intro i _
    have hsmall_lt : |A i i * θ| * K ^ 2 * exp 1 < 1 := by
      linarith [hhalf_i i]
    have hint :=
      integrable_exp_centered_sq_of_hasSubgaussianMGF_of_le
        (hX_subG i) hKsq_pos hC0_le hsmall_lt
    convert hint using 1
    ext ω
    change exp (θ * (A i i * (X i ω ^ 2 - ∫ x, X i x ^ 2 ∂μ))) = _
    ring_nf
  have hcgf_sum :
      cgf (fun ω => ∑ i, Z i ω) μ θ = ∑ i, cgf (Z i) μ θ := by
    have hfun : (fun ω => ∑ i, Z i ω) = (∑ i, Z i) := by
      ext ω
      simp
    rw [hfun]
    exact hZ_indep.cgf_sum₀ hZ_meas (s := Finset.univ) hZ_int
  have hcgf_i :
      ∀ i, cgf (Z i) μ θ ≤
        2 * exp 1 * (A i i * θ * K ^ 2 * exp 1) ^ 2 := by
    intro i
    have hbase :=
      centered_sq_cgf_le_of_hasSubgaussianMGF_of_le
        (hX_subG i) hKsq_pos hC0_le (hhalf_i i)
    calc
      cgf (Z i) μ θ
          = cgf (Y i) μ (A i i * θ) := by
              dsimp [Z]
              exact cgf_const_mul (μ := μ) (Y := Y i) (A i i) θ
      _ ≤ 2 * exp 1 * (A i i * θ * K ^ 2 * exp 1) ^ 2 := hbase
  have hsum_cgf_le :
      (∑ i, cgf (Z i) μ θ) ≤
        ∑ i, 2 * exp 1 * (A i i * θ * K ^ 2 * exp 1) ^ 2 :=
    Finset.sum_le_sum fun i _ => hcgf_i i
  have hsum_eq :
      (∑ i, 2 * exp 1 * (A i i * θ * K ^ 2 * exp 1) ^ 2) =
        (2 * exp 1 ^ 3) * θ ^ 2 * K ^ 4 * ∑ i, A i i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  have hconst_le :
      (2 * exp 1 ^ 3) * θ ^ 2 * K ^ 4 * ∑ i, A i i ^ 2 ≤
        C * θ ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by
    have hnonneg : 0 ≤ θ ^ 2 * K ^ 4 := by positivity
    have hdiag_le := sum_diag_sq_le_frobeniusNorm_sq A
    calc
      (2 * exp 1 ^ 3) * θ ^ 2 * K ^ 4 * ∑ i, A i i ^ 2
          = (2 * exp 1 ^ 3) * (θ ^ 2 * K ^ 4) * ∑ i, A i i ^ 2 := by ring_nf
      _ ≤ C * (θ ^ 2 * K ^ 4) * ∑ i, A i i ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC_quad hnonneg)
            (Finset.sum_nonneg fun i _ => sq_nonneg (A i i))
      _ ≤ C * (θ ^ 2 * K ^ 4) * deterministicFrobeniusNorm A ^ 2 := by
          exact mul_le_mul_of_nonneg_left hdiag_le
            (mul_nonneg hC.le hnonneg)
      _ = C * θ ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by ring_nf
  calc
    cgf (diagonalCenteredQuadraticForm μ A X) μ θ
        = cgf (fun ω => ∑ i, Z i ω) μ θ := by rfl
    _ = ∑ i, cgf (Z i) μ θ := hcgf_sum
    _ ≤ ∑ i, 2 * exp 1 * (A i i * θ * K ^ 2 * exp 1) ^ 2 := hsum_cgf_le
    _ = (2 * exp 1 ^ 3) * θ ^ 2 * K ^ 4 * ∑ i, A i i ^ 2 := hsum_eq
    _ ≤ C * θ ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := hconst_le

end HansonWrightProof
end NLAlib
