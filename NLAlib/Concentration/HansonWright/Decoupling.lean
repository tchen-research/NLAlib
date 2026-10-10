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
import NLAlib.Concentration.HansonWright.VectorProductComparison

/-!
# Hanson–Wright proof: Decoupling

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

/-- Source-transport helper `integrable_exp_quadraticForm_cutMatrix` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integrable_exp_quadraticForm_cutMatrix {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) {X : Fin n → Ω → ℝ} {K l : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hsmall :
      (K ^ 2 * l ^ 2 / 2) * K ^ 2 * deterministicOperatorNorm (cutMatrix A s) ^ 2 * exp 1 < 1) :
    Integrable
      (fun ω => exp (l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω))) μ := by
  let E := EuclideanSpace ℝ (Fin n)
  let U : Ω → E :=
    fun ω => coordinateMask ((Finset.univ : Finset (Fin n)) \ s) (randomVector X ω)
  let V : Ω → E := fun ω => coordinateMask s (randomVector X ω)
  let ψ : Ω → E × E := fun ω => (U ω, V ω)
  let g : E × E → ℝ :=
    fun p => exp (l * inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A p.1) p.2)
  let F : Ω × Ω → ℝ :=
    fun p => exp (l * inner ℝ
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (cutMatrix A s) (randomVector X p.1))
      (randomVector X p.2))
  let H : Ω → ℝ :=
    fun ω => exp (l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω))
  have hX_meas : ∀ i, AEMeasurable (X i) μ := fun i => (hX_subG i).aemeasurable
  have hprod_int : Integrable F (μ.prod μ) := by
    dsimp [F]
    exact integrable_exp_inner_toEuclideanCLM_randomVector_prod (cutMatrix A s)
      h_indep hX_subG hsmall
  have hU_meas : AEMeasurable U μ := by
    dsimp [U]
    exact coordinateMask_aemeasurable _ hX_meas
  have hV_meas : AEMeasurable V μ := by
    dsimp [V]
    exact coordinateMask_aemeasurable _ hX_meas
  have hψ_meas : AEMeasurable ψ μ := hU_meas.prodMk hV_meas
  let φ : Ω × Ω → E × E := fun p => (U p.1, V p.2)
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
  have hcomp_same : Integrable (g ∘ ψ) μ :=
    (integrable_map_measure (by
      rw [hmap_same]
      exact hg_aesm) hψ_meas).1 hg_int_same
  change Integrable H μ
  rw [hH_eq]
  exact hcomp_same

/-- Source-transport helper `integral_exp_quadraticForm_cutMatrix_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integral_exp_quadraticForm_cutMatrix_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) {X : Fin n → Ω → ℝ} {K l : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hsmall :
      (K ^ 2 * l ^ 2 / 2) * K ^ 2 * deterministicOperatorNorm (cutMatrix A s) ^ 2 * exp 1 ≤ 1 / 2) :
    ∫ ω, exp (l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω)) ∂μ ≤
      exp (exp 1 ^ 2 * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm (cutMatrix A s) ^ 2) := by
  have hX_meas : ∀ i, AEMeasurable (X i) μ := fun i => (hX_subG i).aemeasurable
  have hprod_int :
      Integrable
        (fun p : Ω × Ω =>
          exp (l * inner ℝ
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (cutMatrix A s) (randomVector X p.1))
            (randomVector X p.2))) (μ.prod μ) :=
    integrable_exp_inner_toEuclideanCLM_randomVector_prod (cutMatrix A s)
      h_indep hX_subG (lt_of_le_of_lt hsmall (by norm_num))
  have heq :=
    integral_exp_quadraticForm_cutMatrix_eq_prod A s h_indep hX_meas hprod_int
  rw [heq]
  exact integral_exp_inner_toEuclideanCLM_randomVector_prod_le (cutMatrix A s)
    h_indep hX_subG hsmall

/-- Source-transport helper `integrable_exp_quadraticForm_offDiagonal` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integrable_exp_quadraticForm_offDiagonal {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {K l : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hsmall :
      (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * deterministicOperatorNorm A ^ 2 * exp 1 < 1) :
    Integrable
      (fun ω => exp (l * matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω))) μ := by
  classical
  let P : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powerset
  let R : Ω → ℝ := fun ω =>
    (P.card : ℝ)⁻¹ *
      ∑ s ∈ P, exp (4 * l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω))
  have hX_meas : ∀ i, AEMeasurable (X i) μ := fun i => (hX_subG i).aemeasurable
  have hsmall_cut : ∀ s ∈ P,
      (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 *
          deterministicOperatorNorm (cutMatrix A s) ^ 2 * exp 1 < 1 := by
    intro s hs
    have hop_sq : deterministicOperatorNorm (cutMatrix A s) ^ 2 ≤ deterministicOperatorNorm A ^ 2 := by
      nlinarith [operatorNorm_cutMatrix_le A s, operatorNorm_nonneg (cutMatrix A s),
        operatorNorm_nonneg A]
    have hcoef_nonneg :
        0 ≤ (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * exp 1 := by positivity
    calc
      (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 *
          deterministicOperatorNorm (cutMatrix A s) ^ 2 * exp 1
          = ((K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * exp 1) *
              deterministicOperatorNorm (cutMatrix A s) ^ 2 := by ring
      _ ≤ ((K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * exp 1) *
            deterministicOperatorNorm A ^ 2 :=
          mul_le_mul_of_nonneg_left hop_sq hcoef_nonneg
      _ = (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * deterministicOperatorNorm A ^ 2 * exp 1 := by
          ring
      _ < 1 := hsmall
  have hR_int : Integrable R μ := by
    dsimp [R]
    refine (MeasureTheory.integrable_finsetSum P fun s hs => ?_).const_mul _
    exact integrable_exp_quadraticForm_cutMatrix A s h_indep hX_subG (hsmall_cut s hs)
  have hleft_aesm :
      AEStronglyMeasurable
        (fun ω => exp (l * matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω))) μ := by
    have hleft_ae :
        AEMeasurable
          (fun ω => exp (l * matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω))) μ :=
      ((randomQuadraticForm_aemeasurable (offDiagonalMatrix A) hX_meas).const_mul l).exp
    exact hleft_ae.aestronglyMeasurable
  have hpoint :
      (fun ω => exp (l * matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω)))
        ≤ᵐ[μ] R := by
    filter_upwards with ω
    simpa [R, P] using
      exp_mul_quadraticForm_offDiagonal_le_average_cut A (fun i => X i ω) l
  refine Integrable.mono' hR_int hleft_aesm ?_
  filter_upwards [hpoint] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
  exact hω

/-- Source-transport helper `integral_exp_quadraticForm_offDiagonal_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integral_exp_quadraticForm_offDiagonal_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {K l : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hsmall :
      (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * deterministicOperatorNorm A ^ 2 * exp 1 ≤ 1 / 2) :
    ∫ ω, exp (l * matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω)) ∂μ ≤
      exp (exp 1 ^ 2 * (4 * l) ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2) := by
  classical
  let P : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powerset
  let R : Ω → ℝ := fun ω =>
    (P.card : ℝ)⁻¹ *
      ∑ s ∈ P, exp (4 * l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω))
  let B : ℝ := exp (exp 1 ^ 2 * (4 * l) ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2)
  have hX_meas : ∀ i, AEMeasurable (X i) μ := fun i => (hX_subG i).aemeasurable
  have hP_pos : 0 < (P.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨∅, Finset.empty_mem_powerset _⟩
  have hsmall_cut : ∀ s ∈ P,
      (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 *
          deterministicOperatorNorm (cutMatrix A s) ^ 2 * exp 1 ≤ 1 / 2 := by
    intro s hs
    have hop_sq : deterministicOperatorNorm (cutMatrix A s) ^ 2 ≤ deterministicOperatorNorm A ^ 2 := by
      nlinarith [operatorNorm_cutMatrix_le A s, operatorNorm_nonneg (cutMatrix A s),
        operatorNorm_nonneg A]
    have hcoef_nonneg :
        0 ≤ (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * exp 1 := by positivity
    calc
      (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 *
          deterministicOperatorNorm (cutMatrix A s) ^ 2 * exp 1
          = ((K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * exp 1) *
              deterministicOperatorNorm (cutMatrix A s) ^ 2 := by ring
      _ ≤ ((K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * exp 1) *
            deterministicOperatorNorm A ^ 2 :=
          mul_le_mul_of_nonneg_left hop_sq hcoef_nonneg
      _ = (K ^ 2 * (4 * l) ^ 2 / 2) * K ^ 2 * deterministicOperatorNorm A ^ 2 * exp 1 := by
          ring
      _ ≤ 1 / 2 := hsmall
  have hcut_int : ∀ s ∈ P,
      Integrable (fun ω =>
        exp (4 * l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω))) μ := by
    intro s hs
    exact integrable_exp_quadraticForm_cutMatrix A s h_indep hX_subG
      (lt_of_le_of_lt (hsmall_cut s hs) (by norm_num))
  have hR_int : Integrable R μ := by
    dsimp [R]
    exact (MeasureTheory.integrable_finsetSum P hcut_int).const_mul _
  have hleft_int :
      Integrable
        (fun ω => exp (l * matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω))) μ :=
    integrable_exp_quadraticForm_offDiagonal A h_indep hX_subG
      (lt_of_le_of_lt hsmall (by norm_num))
  have hpoint :
      (fun ω => exp (l * matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω)))
        ≤ᵐ[μ] R := by
    filter_upwards with ω
    simpa [R, P] using
      exp_mul_quadraticForm_offDiagonal_le_average_cut A (fun i => X i ω) l
  have hcut_bound : ∀ s ∈ P,
      ∫ ω, exp (4 * l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω)) ∂μ ≤ B := by
    intro s hs
    have hbase :=
      integral_exp_quadraticForm_cutMatrix_le A s h_indep hX_subG (hsmall_cut s hs)
    have hfrob := frobeniusNorm_cutMatrix_sq_le A s
    have hcoef_nonneg : 0 ≤ exp 1 ^ 2 * (4 * l) ^ 2 * K ^ 4 := by positivity
    have hexp_le :
        exp (exp 1 ^ 2 * (4 * l) ^ 2 * K ^ 4 *
            deterministicFrobeniusNorm (cutMatrix A s) ^ 2) ≤ B := by
      dsimp [B]
      apply exp_le_exp.mpr
      calc
        exp 1 ^ 2 * (4 * l) ^ 2 * K ^ 4 * deterministicFrobeniusNorm (cutMatrix A s) ^ 2
            = (exp 1 ^ 2 * (4 * l) ^ 2 * K ^ 4) *
                deterministicFrobeniusNorm (cutMatrix A s) ^ 2 := by ring
        _ ≤ (exp 1 ^ 2 * (4 * l) ^ 2 * K ^ 4) * deterministicFrobeniusNorm A ^ 2 :=
            mul_le_mul_of_nonneg_left hfrob hcoef_nonneg
        _ = exp 1 ^ 2 * (4 * l) ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by ring
    exact hbase.trans hexp_le
  calc
    ∫ ω, exp (l * matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω)) ∂μ
        ≤ ∫ ω, R ω ∂μ := integral_mono_ae hleft_int hR_int hpoint
    _ = (P.card : ℝ)⁻¹ *
          ∑ s ∈ P, ∫ ω,
            exp (4 * l * matrixQuadraticForm (cutMatrix A s) (fun i => X i ω)) ∂μ := by
          change (∫ ω, (P.card : ℝ)⁻¹ *
            ∑ s ∈ P, exp (4 * l * matrixQuadraticForm (cutMatrix A s)
              (fun i => X i ω)) ∂μ) = _
          rw [integral_const_mul]
          congr 1
          rw [MeasureTheory.integral_finsetSum]
          intro s hs
          exact hcut_int s hs
    _ ≤ (P.card : ℝ)⁻¹ * ∑ s ∈ P, B := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun s hs => hcut_bound s hs) (inv_nonneg.mpr hP_pos.le)
    _ = B := by
          simp
          field_simp [ne_of_gt hP_pos]

/-- Source-transport helper `exp_add_le_average_exp_two` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma exp_add_le_average_exp_two (a b : ℝ) :
    exp (a + b) ≤ (exp (2 * a) + exp (2 * b)) / 2 := by
  have hconv := convexOn_exp.2 (Set.mem_univ (2 * a)) (Set.mem_univ (2 * b))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  calc
    exp (a + b) = exp ((1 / 2 : ℝ) • (2 * a) + (1 / 2 : ℝ) • (2 * b)) := by
      congr 1
      norm_num
      ring
    _ ≤ (1 / 2 : ℝ) * exp (2 * a) + (1 / 2 : ℝ) * exp (2 * b) := hconv
    _ = (exp (2 * a) + exp (2 * b)) / 2 := by ring

/-- Source-transport helper `abs_two_mul_le_inv_quarter_of_abs_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma abs_two_mul_le_inv_quarter_of_abs_le {a C l : ℝ}
    (ha : 0 < a) (hC : 0 < C)
    (hl : |l| ≤ (2 * C * a)⁻¹) :
    |2 * l| ≤ (2 * (C / 4) * a)⁻¹ := by
  have hbase : |2 * l| ≤ 2 * (2 * C * a)⁻¹ := by
    calc
      |2 * l| = 2 * |l| := by rw [abs_mul, abs_of_pos two_pos]
      _ ≤ 2 * (2 * C * a)⁻¹ := mul_le_mul_of_nonneg_left hl (by norm_num)
  have hleft : 2 * (2 * C * a)⁻¹ = (C * a)⁻¹ := by
    field_simp [hC.ne', ha.ne']
  have hright : (2 * (C / 4) * a)⁻¹ = 2 * (C * a)⁻¹ := by
    field_simp [hC.ne', ha.ne']
    ring
  calc
    |2 * l| ≤ 2 * (2 * C * a)⁻¹ := hbase
    _ = (C * a)⁻¹ := hleft
    _ ≤ 2 * (C * a)⁻¹ := by
      exact le_mul_of_one_le_left (inv_nonneg.mpr (mul_nonneg hC.le ha.le)) (by norm_num)
    _ = (2 * (C / 4) * a)⁻¹ := hright.symm

/-- Source-transport helper `abs_mul_le_inv_two_of_abs_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma abs_mul_le_inv_two_of_abs_le {a C l : ℝ}
    (ha : 0 < a) (hC : 0 < C)
    (hl : |l| ≤ (2 * C * a)⁻¹) :
    |l| * a ≤ 1 / (2 * C) := by
  calc
    |l| * a ≤ (2 * C * a)⁻¹ * a :=
      mul_le_mul_of_nonneg_right hl ha.le
    _ = 1 / (2 * C) := by
      field_simp [hC.ne', ha.ne']

/-- Source-transport helper `offDiagonal_small_two_mul_of_abs_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma offDiagonal_small_two_mul_of_abs_le {K C op l : ℝ}
    (hK : 0 < K) (hC : 0 < C) (hop : 0 < op)
    (hC_sq : 16 * exp 1 ≤ C ^ 2)
    (hl : |l| ≤ (2 * C * K ^ 2 * op)⁻¹) :
    (K ^ 2 * (4 * (2 * l)) ^ 2 / 2) * K ^ 2 * op ^ 2 * exp 1 ≤ 1 / 2 := by
  let a : ℝ := K ^ 2 * op
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hscale : |l| * a ≤ 1 / (2 * C) := by
    have hden_eq : 2 * C * a = 2 * C * K ^ 2 * op := by
      dsimp [a]
      ring
    have hl_a : |l| ≤ (2 * C * a)⁻¹ := by
      rw [hden_eq]
      exact hl
    exact abs_mul_le_inv_two_of_abs_le (a := a) (C := C) (l := l) ha hC hl_a
  have hscale_sq :
      (|l| * a) ^ 2 ≤ (1 / (2 * C)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hscale
  have hsq_eq : (|l| * a) ^ 2 = l ^ 2 * K ^ 4 * op ^ 2 := by
    dsimp [a]
    rw [mul_pow, sq_abs]
    ring
  have hcore : l ^ 2 * K ^ 4 * op ^ 2 ≤ (1 / (2 * C)) ^ 2 := by
    rw [← hsq_eq]
    exact hscale_sq
  calc
    (K ^ 2 * (4 * (2 * l)) ^ 2 / 2) * K ^ 2 * op ^ 2 * exp 1
        = 32 * exp 1 * (l ^ 2 * K ^ 4 * op ^ 2) := by ring
    _ ≤ 32 * exp 1 * ((1 / (2 * C)) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 8 * exp 1 / C ^ 2 := by
      field_simp [hC.ne']
      ring
    _ ≤ 1 / 2 := by
      have hC2_pos : 0 < C ^ 2 := sq_pos_of_pos hC
      rw [div_le_iff₀ hC2_pos]
      nlinarith [hC_sq]

/-- Source-transport helper `offDiagonal_exponent_two_mul_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma offDiagonal_exponent_two_mul_le {K C F l : ℝ}
    (hC_offdiag_quad : 64 * exp 1 ^ 2 ≤ C) :
    exp 1 ^ 2 * (4 * (2 * l)) ^ 2 * K ^ 4 * F ^ 2 ≤
      C * l ^ 2 * K ^ 4 * F ^ 2 := by
  have hnonneg : 0 ≤ l ^ 2 * K ^ 4 * F ^ 2 := by positivity
  calc
    exp 1 ^ 2 * (4 * (2 * l)) ^ 2 * K ^ 4 * F ^ 2
        = (64 * exp 1 ^ 2) * (l ^ 2 * K ^ 4 * F ^ 2) := by ring
    _ ≤ C * (l ^ 2 * K ^ 4 * F ^ 2) :=
      mul_le_mul_of_nonneg_right hC_offdiag_quad hnonneg
    _ = C * l ^ 2 * K ^ 4 * F ^ 2 := by ring

end HansonWrightProof
end NLAlib
