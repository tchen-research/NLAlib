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
import NLAlib.Concentration.HansonWright.DiagonalCGF

/-!
# Hanson–Wright proof: Centering

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

/-- Source-transport helper `diagonalCenteredQuadraticForm_integrable_exp` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma diagonalCenteredQuadraticForm_integrable_exp {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C θ : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hC_domain : exp 1 ≤ C) (hOp : 0 < deterministicOperatorNorm A)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hθ : |θ| ≤ (2 * C * K ^ 2 * deterministicOperatorNorm A)⁻¹) :
    Integrable (fun ω => exp (θ * diagonalCenteredQuadraticForm μ A X ω)) μ := by
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
  have hsum_int :
      Integrable (fun ω => exp (θ * (∑ i, Z i) ω)) μ :=
    iIndepFun.integrable_exp_mul_sum₀ hZ_indep hZ_meas (s := Finset.univ) hZ_int
  convert hsum_int using 1
  ext ω
  congr 1
  simp only [diagonalCenteredQuadraticForm, Z, Y, Finset.sum_apply]

/-- Source-transport helper `quadraticForm_eq_sum_diag_of_offdiag_eq_zero` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma quadraticForm_eq_sum_diag_of_offdiag_eq_zero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (hA_diag : ∀ i j, i ≠ j → A i j = 0) :
    matrixQuadraticForm A x = ∑ i, A i i * x i ^ 2 := by
  unfold matrixQuadraticForm
  apply Finset.sum_congr rfl
  intro i _
  calc
    ∑ j, x i * A i j * x j = x i * A i i * x i := by
      exact Finset.sum_eq_single i
        (fun j _ hji => by
          rw [hA_diag i j hji.symm]
          ring)
        (fun hi => (hi (Finset.mem_univ i)).elim)
    _ = A i i * x i ^ 2 := by ring_nf

/-- Source-transport helper `centeredQuadraticForm_eq_diagonalCentered_of_offdiag_eq_zero` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma centeredQuadraticForm_eq_diagonalCentered_of_offdiag_eq_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K : ℝ}
    (hA_diag : ∀ i j, i ≠ j → A i j = 0)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) :
    centeredQuadraticForm μ A X = diagonalCenteredQuadraticForm μ A X := by
  have hterm_int : ∀ i, Integrable (fun ω => A i i * X i ω ^ 2) μ := by
    intro i
    exact ((integrable_pow_of_integrable_exp_mul
      (X := X i) (t := 1) one_ne_zero
      ((hX_subG i).integrable_exp_mul 1)
      ((hX_subG i).integrable_exp_mul (-1)) 2).const_mul (A i i))
  ext ω
  unfold centeredQuadraticForm randomQuadraticForm diagonalCenteredQuadraticForm
  have hqfun :
      (fun ω => matrixQuadraticForm A fun i => X i ω) =
        (fun ω => ∑ i, A i i * X i ω ^ 2) := by
    ext ω
    exact quadraticForm_eq_sum_diag_of_offdiag_eq_zero hA_diag
  rw [quadraticForm_eq_sum_diag_of_offdiag_eq_zero hA_diag]
  rw [show (∫ ω, matrixQuadraticForm A (fun i => X i ω) ∂μ) =
      ∫ ω, (∑ i, A i i * X i ω ^ 2) ∂μ by rw [hqfun]]
  have hintegral :
      ∫ ω, (∑ i, A i i * X i ω ^ 2) ∂μ =
        ∑ i, ∫ ω, A i i * X i ω ^ 2 ∂μ := by
    rw [MeasureTheory.integral_finsetSum]
    intro i _
    exact hterm_int i
  rw [hintegral]
  calc
    (∑ i, A i i * X i ω ^ 2) - ∑ i, ∫ (ω : Ω), A i i * X i ω ^ 2 ∂μ
        = ∑ i, (A i i * X i ω ^ 2 - ∫ (ω : Ω), A i i * X i ω ^ 2 ∂μ) := by
            rw [← Finset.sum_sub_distrib]
    _ = ∑ i, A i i * (X i ω ^ 2 - ∫ (ω : Ω), X i ω ^ 2 ∂μ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
        ring_nf

/-- Hanson-Wright MGF certificate for diagonal quadratic forms with sub-Gaussian coordinates. -/
theorem hasHansonWrightMGF_diagonal_of_subgaussian {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hC_domain : exp 1 ≤ C) (hC_quad : 2 * exp 1 ^ 3 ≤ C)
    (hOp : 0 < deterministicOperatorNorm A)
    (hA_diag : ∀ i j, i ≠ j → A i j = 0)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) :
    HasHansonWrightMGF μ A X K C := by
  have hcenter_eq :
      centeredQuadraticForm μ A X = diagonalCenteredQuadraticForm μ A X :=
    centeredQuadraticForm_eq_diagonalCentered_of_offdiag_eq_zero hA_diag hX_subG
  refine ⟨?_, ?_⟩
  · intro l hl
    rw [hcenter_eq]
    exact diagonalCenteredQuadraticForm_cgf_le hK hC hC_domain hC_quad hOp h_indep hX_subG hl
  · intro l hl
    rw [hcenter_eq]
    exact diagonalCenteredQuadraticForm_integrable_exp hK hC hC_domain hOp h_indep hX_subG hl

/-- Source-transport helper `mean_le_log_mgf` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma mean_le_log_mgf {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_int : Integrable X μ) {t : ℝ} (ht : 0 < t)
    (hexpX_int : Integrable (fun ω => exp (t * X ω)) μ) :
    ∫ ω, X ω ∂μ ≤ (1 / t) * log (∫ ω, exp (t * X ω) ∂μ) := by
  have h := (convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (by simp) (hX_int.const_mul t) hexpX_int)
  have h1 : ∫ ω, t * X ω ∂μ = t * ∫ ω, X ω ∂μ := integral_const_mul t X
  have h2 : t * ∫ ω, X ω ∂μ ≤ log (∫ ω, exp (t * X ω) ∂μ) := by
    have hexp_bound : exp (t * ∫ ω, X ω ∂μ) ≤ ∫ ω, exp (t * X ω) ∂μ := h1 ▸ h
    calc
      t * ∫ ω, X ω ∂μ = log (exp (t * ∫ ω, X ω ∂μ)) := (log_exp _).symm
      _ ≤ log (∫ ω, exp (t * X ω) ∂μ) :=
        log_le_log (exp_pos _) hexp_bound
  calc
    ∫ ω, X ω ∂μ = (∫ ω, X ω ∂μ) * t / t := by
      calc
        ∫ ω, X ω ∂μ = (∫ ω, X ω ∂μ) * 1 := by ring
        _ = (∫ ω, X ω ∂μ) * (t / t) := by rw [div_self ht.ne']
        _ = (∫ ω, X ω ∂μ) * t / t := by ring
    _ ≤ log (∫ ω, exp (t * X ω) ∂μ) / t := by
      exact div_le_div_of_nonneg_right (by linarith) ht.le
    _ = (1 / t) * log (∫ ω, exp (t * X ω) ∂μ) := by ring

/-- Source-transport helper `hasSubgaussianMGF_integral_le_zero` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma hasSubgaussianMGF_integral_le_zero {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ∂μ ≤ 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set t : ℝ := ε / ((c : ℝ) + 1) with ht_def
  have hden_pos : 0 < (c : ℝ) + 1 := by positivity
  have ht_pos : 0 < t := by
    rw [ht_def]
    positivity
  have hmean := mean_le_log_mgf h.integrable ht_pos (h.integrable_exp_mul t)
  have hmgf_pos : 0 < mgf X μ t := mgf_pos (h.integrable_exp_mul t)
  have hlog_le : log (mgf X μ t) ≤ (c : ℝ) * t ^ 2 / 2 := by
    calc
      log (mgf X μ t) ≤ log (exp ((c : ℝ) * t ^ 2 / 2)) :=
        log_le_log hmgf_pos (h.mgf_le t)
      _ = (c : ℝ) * t ^ 2 / 2 := log_exp _
  have hmean_le : ∫ ω, X ω ∂μ ≤ (1 / t) * ((c : ℝ) * t ^ 2 / 2) :=
    hmean.trans (mul_le_mul_of_nonneg_left hlog_le (by positivity))
  calc
    ∫ ω, X ω ∂μ ≤ (1 / t) * ((c : ℝ) * t ^ 2 / 2) := hmean_le
    _ = (c : ℝ) * t / 2 := by field_simp [ht_pos.ne']
    _ ≤ ε := by
      rw [ht_def]
      have hratio : (c : ℝ) / ((c : ℝ) + 1) ≤ 1 :=
        (div_le_one hden_pos).mpr (by linarith)
      calc
        (c : ℝ) * (ε / ((c : ℝ) + 1)) / 2 =
            (ε / 2) * ((c : ℝ) / ((c : ℝ) + 1)) := by ring
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
        _ ≤ ε := by linarith
    _ = 0 + ε := by ring

/-- A random variable satisfying the global sub-Gaussian MGF bound is centered. -/
lemma hasSubgaussianMGF_integral_eq_zero {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ∂μ = 0 := by
  have hle : ∫ ω, X ω ∂μ ≤ 0 := hasSubgaussianMGF_integral_le_zero h
  have hle_neg : ∫ ω, -X ω ∂μ ≤ 0 := hasSubgaussianMGF_integral_le_zero h.neg
  have hge : 0 ≤ ∫ ω, X ω ∂μ := by
    rw [integral_neg] at hle_neg
    linarith
  exact le_antisymm hle hge

/-- Source-transport helper `quadraticForm_eq_diag_add_offDiagonal` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma quadraticForm_eq_diag_add_offDiagonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    matrixQuadraticForm A x =
      (∑ i, A i i * x i ^ 2) + matrixQuadraticForm (offDiagonalMatrix A) x := by
  classical
  unfold matrixQuadraticForm offDiagonalMatrix
  calc
    ∑ i, ∑ j, x i * A i j * x j
        = ∑ i, (A i i * x i ^ 2 +
            ∑ j, x i * (if i = j then 0 else A i j) * x j) := by
          apply Finset.sum_congr rfl
          intro i _
          have hdiag_sum :
              (∑ j, (if i = j then A i i * x i * x i else 0)) =
                A i i * x i * x i := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro j _ hji
              simp [hji.symm]
            · intro hi
              exact (hi (Finset.mem_univ i)).elim
          calc
            ∑ j, x i * A i j * x j
                = (∑ j, (if i = j then A i i * x i * x i else 0)) +
                    ∑ j, x i * (if i = j then 0 else A i j) * x j := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro j _
                  by_cases hij : i = j
                  · subst j
                    simp only [if_true]
                    ring
                  · rw [if_neg hij, if_neg hij]
                    ring
            _ = A i i * x i ^ 2 +
                    ∑ j, x i * (if i = j then 0 else A i j) * x j := by
                  rw [hdiag_sum]
                  ring
    _ = (∑ i, A i i * x i ^ 2) +
          ∑ i, ∑ j, x i * (if i = j then 0 else A i j) * x j := by
          rw [Finset.sum_add_distrib]

/-- Source-transport helper `integrable_randomQuadraticForm_offDiagonal_of_subgaussian` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integrable_randomQuadraticForm_offDiagonal_of_subgaussian {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {K : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) :
    Integrable (randomQuadraticForm (offDiagonalMatrix A) X) μ := by
  classical
  have hterm : ∀ i j,
      Integrable (fun ω => X i ω * offDiagonalMatrix A i j * X j ω) μ := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [offDiagonalMatrix]
    · have hmul : Integrable ((X i) * (X j)) μ :=
        (h_indep.indepFun hij).integrable_mul (hX_subG i).integrable
          (hX_subG j).integrable
      convert hmul.const_mul (A i j) using 1
      ext ω
      simp [offDiagonalMatrix, hij]
      ring
  unfold randomQuadraticForm matrixQuadraticForm
  exact MeasureTheory.integrable_finsetSum _ fun i _ =>
    MeasureTheory.integrable_finsetSum _ fun j _ => hterm i j

/-- Source-transport helper `integral_randomQuadraticForm_offDiagonal_eq_zero` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integral_randomQuadraticForm_offDiagonal_eq_zero {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {K : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) :
    ∫ ω, randomQuadraticForm (offDiagonalMatrix A) X ω ∂μ = 0 := by
  classical
  have hterm_int : ∀ i j,
      Integrable (fun ω => X i ω * offDiagonalMatrix A i j * X j ω) μ := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [offDiagonalMatrix]
    · have hmul : Integrable ((X i) * (X j)) μ :=
        (h_indep.indepFun hij).integrable_mul (hX_subG i).integrable
          (hX_subG j).integrable
      convert hmul.const_mul (A i j) using 1
      ext ω
      simp [offDiagonalMatrix, hij]
      ring
  have hrow_int : ∀ i,
      Integrable (fun ω => ∑ j, X i ω * offDiagonalMatrix A i j * X j ω) μ := by
    intro i
    exact MeasureTheory.integrable_finsetSum _ fun j _ => hterm_int i j
  calc
    ∫ ω, randomQuadraticForm (offDiagonalMatrix A) X ω ∂μ
        = ∑ i, ∑ j,
            ∫ ω, X i ω * offDiagonalMatrix A i j * X j ω ∂μ := by
          unfold randomQuadraticForm matrixQuadraticForm
          rw [MeasureTheory.integral_finsetSum _ (fun i _ => hrow_int i)]
          apply Finset.sum_congr rfl
          intro i _
          rw [MeasureTheory.integral_finsetSum _ (fun j _ => hterm_int i j)]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          apply Finset.sum_eq_zero
          intro j _
          by_cases hij : i = j
          · subst j
            simp [offDiagonalMatrix]
          · have hpair := h_indep.indepFun hij
            have hmeas_i : AEStronglyMeasurable (X i) μ :=
              (hX_subG i).integrable.aestronglyMeasurable
            have hmeas_j : AEStronglyMeasurable (X j) μ :=
              (hX_subG j).integrable.aestronglyMeasurable
            have hmul_eq :
                ∫ ω, X i ω * X j ω ∂μ =
                  (∫ ω, X i ω ∂μ) * (∫ ω, X j ω ∂μ) :=
              hpair.integral_fun_mul_eq_mul_integral hmeas_i hmeas_j
            calc
              ∫ ω, X i ω * offDiagonalMatrix A i j * X j ω ∂μ
                  = ∫ ω, A i j * (X i ω * X j ω) ∂μ := by
                    apply integral_congr_ae
                    filter_upwards with ω
                    simp [offDiagonalMatrix, hij]
                    ring
              _ = A i j * ∫ ω, X i ω * X j ω ∂μ := by
                    rw [integral_const_mul]
              _ = A i j * ((∫ ω, X i ω ∂μ) * (∫ ω, X j ω ∂μ)) := by
                    rw [hmul_eq]
              _ = 0 := by
                    rw [hasSubgaussianMGF_integral_eq_zero (hX_subG i)]
                    ring

end HansonWrightProof
end NLAlib
