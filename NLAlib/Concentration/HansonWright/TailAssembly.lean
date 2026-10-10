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
import NLAlib.Concentration.HansonWright.Decoupling

/-!
# Hanson–Wright proof: TailAssembly

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

/-- Hanson-Wright MGF certificate from independent sub-Gaussian coordinates. -/
theorem hasHansonWrightMGF_of_subgaussian {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hC_domain : 4 * exp 1 ≤ C)
    (hC_diag_quad : 8 * exp 1 ^ 3 ≤ C)
    (hC_offdiag_domain : 16 * exp 1 ≤ C ^ 2)
    (hC_offdiag_quad : 64 * exp 1 ^ 2 ≤ C)
    (hOp : 0 < deterministicOperatorNorm A)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) :
    HasHansonWrightMGF μ A X K C := by
  let D : Ω → ℝ := diagonalCenteredQuadraticForm μ A X
  let O : Ω → ℝ := fun ω => matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω)
  let B : ℝ → ℝ := fun l => C * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2
  have hX_meas : ∀ i, AEMeasurable (X i) μ := fun i => (hX_subG i).aemeasurable
  have hKsq_op_pos : 0 < K ^ 2 * deterministicOperatorNorm A := by positivity
  have hCq_pos : 0 < C / 4 := by positivity
  have hCq_domain : exp 1 ≤ C / 4 := by linarith
  have hCq_quad : 2 * exp 1 ^ 3 ≤ C / 4 := by linarith
  have hcenter_eq :
      centeredQuadraticForm μ A X = fun ω => D ω + O ω := by
    dsimp [D, O]
    exact centeredQuadraticForm_eq_diagonal_add_offDiagonal A h_indep hX_subG
  have hD_ae : AEMeasurable D μ := by
    dsimp [D, diagonalCenteredQuadraticForm]
    exact Finset.aemeasurable_fun_sum _ fun i _ =>
      ((((hX_meas i).pow_const 2).sub_const _).const_mul _)
  have hO_ae : AEMeasurable O μ := by
    dsimp [O]
    exact randomQuadraticForm_aemeasurable (offDiagonalMatrix A) hX_meas
  have hmain : ∀ l : ℝ, |l| ≤ (2 * C * K ^ 2 * deterministicOperatorNorm A)⁻¹ →
      Integrable (fun ω => exp (l * centeredQuadraticForm μ A X ω)) μ ∧
        ∫ ω, exp (l * centeredQuadraticForm μ A X ω) ∂μ ≤ exp (B l) := by
    intro l hl
    have hden_eq : 2 * C * (K ^ 2 * deterministicOperatorNorm A) =
        2 * C * K ^ 2 * deterministicOperatorNorm A := by ring
    have hl_a : |l| ≤ (2 * C * (K ^ 2 * deterministicOperatorNorm A))⁻¹ := by
      rw [hden_eq]
      exact hl
    have hdiag_domain_a :
        |2 * l| ≤ (2 * (C / 4) * (K ^ 2 * deterministicOperatorNorm A))⁻¹ :=
      abs_two_mul_le_inv_quarter_of_abs_le
        (a := K ^ 2 * deterministicOperatorNorm A) (C := C) (l := l) hKsq_op_pos hC hl_a
    have hdiag_domain :
        |2 * l| ≤ (2 * (C / 4) * K ^ 2 * deterministicOperatorNorm A)⁻¹ := by
      simpa [mul_assoc] using hdiag_domain_a
    have hD_int : Integrable (fun ω => exp ((2 * l) * D ω)) μ := by
      dsimp [D]
      exact diagonalCenteredQuadraticForm_integrable_exp
        (A := A) (X := X) (K := K) (C := C / 4) (θ := 2 * l)
        hK hCq_pos hCq_domain hOp h_indep hX_subG hdiag_domain
    have hD_cgf :
        cgf D μ (2 * l) ≤ B l := by
      have hbase :=
        diagonalCenteredQuadraticForm_cgf_le
          (A := A) (X := X) (K := K) (C := C / 4) (θ := 2 * l)
          hK hCq_pos hCq_domain hCq_quad hOp h_indep hX_subG hdiag_domain
      dsimp [D, B] at hbase ⊢
      calc
        cgf (diagonalCenteredQuadraticForm μ A X) μ (2 * l)
            ≤ (C / 4) * (2 * l) ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := hbase
        _ = C * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by ring
    have hD_mgf_le : ∫ ω, exp ((2 * l) * D ω) ∂μ ≤ exp (B l) := by
      change mgf D μ (2 * l) ≤ exp (B l)
      rw [← exp_cgf hD_int]
      exact exp_le_exp.mpr hD_cgf
    have hsmall_offdiag :
        (K ^ 2 * (4 * (2 * l)) ^ 2 / 2) * K ^ 2 *
            deterministicOperatorNorm A ^ 2 * exp 1 ≤ 1 / 2 :=
      offDiagonal_small_two_mul_of_abs_le hK hC hOp hC_offdiag_domain hl
    have hO_int : Integrable (fun ω => exp ((2 * l) * O ω)) μ := by
      change Integrable (fun ω => exp ((2 * l) *
        matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω))) μ
      exact integrable_exp_quadraticForm_offDiagonal
        (A := A) (X := X) (K := K) (l := 2 * l)
        h_indep hX_subG (lt_of_le_of_lt hsmall_offdiag (by norm_num))
    have hO_mgf_le : ∫ ω, exp ((2 * l) * O ω) ∂μ ≤ exp (B l) := by
      have hbase :=
        integral_exp_quadraticForm_offDiagonal_le
          (A := A) (X := X) (K := K) (l := 2 * l)
          h_indep hX_subG hsmall_offdiag
      have hexp_le :
          exp (exp 1 ^ 2 * (4 * (2 * l)) ^ 2 * K ^ 4 *
              deterministicFrobeniusNorm A ^ 2) ≤ exp (B l) := by
        apply exp_le_exp.mpr
        dsimp [B]
        exact offDiagonal_exponent_two_mul_le
          (K := K) (C := C) (F := deterministicFrobeniusNorm A) (l := l) hC_offdiag_quad
      change ∫ ω, exp ((2 * l) *
        matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω)) ∂μ ≤ exp (B l)
      exact hbase.trans hexp_le
    let R : Ω → ℝ :=
      fun ω => (exp ((2 * l) * D ω) + exp ((2 * l) * O ω)) / 2
    have hR_int : Integrable R μ := by
      change Integrable
        (fun ω => (exp ((2 * l) * D ω) + exp ((2 * l) * O ω)) / 2) μ
      exact (hD_int.add hO_int).div_const 2
    have hleft_aesm :
        AEStronglyMeasurable (fun ω => exp (l * (D ω + O ω))) μ :=
      (((hD_ae.add hO_ae).const_mul l).exp).aestronglyMeasurable
    have hpoint :
        (fun ω => exp (l * (D ω + O ω))) ≤ᵐ[μ] R := by
      filter_upwards with ω
      dsimp [R]
      have hconv := exp_add_le_average_exp_two (l * D ω) (l * O ω)
      convert hconv using 1 <;> ring_nf
    have hDO_int : Integrable (fun ω => exp (l * (D ω + O ω))) μ := by
      refine Integrable.mono' hR_int hleft_aesm ?_
      filter_upwards [hpoint] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
      exact hω
    have hcenter_int : Integrable (fun ω => exp (l * centeredQuadraticForm μ A X ω)) μ :=
      hDO_int.congr (ae_of_all _ fun ω => by
        change exp (l * (D ω + O ω)) = exp (l * centeredQuadraticForm μ A X ω)
        rw [← congrFun hcenter_eq ω])
    have hDO_integral_le :
        ∫ ω, exp (l * (D ω + O ω)) ∂μ ≤ exp (B l) := by
      have hmono : ∫ ω, exp (l * (D ω + O ω)) ∂μ ≤ ∫ ω, R ω ∂μ :=
        integral_mono_ae hDO_int hR_int hpoint
      have hR_integral :
          ∫ ω, R ω ∂μ =
            (∫ ω, exp ((2 * l) * D ω) ∂μ +
              ∫ ω, exp ((2 * l) * O ω) ∂μ) / 2 := by
        change (∫ ω, (exp ((2 * l) * D ω) + exp ((2 * l) * O ω)) / 2 ∂μ) = _
        rw [integral_div]
        rw [integral_add hD_int hO_int]
      have hsum_le :
          ∫ ω, exp ((2 * l) * D ω) ∂μ +
              ∫ ω, exp ((2 * l) * O ω) ∂μ ≤
            exp (B l) + exp (B l) :=
        add_le_add hD_mgf_le hO_mgf_le
      calc
        ∫ ω, exp (l * (D ω + O ω)) ∂μ ≤ ∫ ω, R ω ∂μ := hmono
        _ = (∫ ω, exp ((2 * l) * D ω) ∂μ +
              ∫ ω, exp ((2 * l) * O ω) ∂μ) / 2 := hR_integral
        _ ≤ (exp (B l) + exp (B l)) / 2 :=
          div_le_div_of_nonneg_right hsum_le (by norm_num)
        _ = exp (B l) := by ring
    have hcenter_integral_le :
        ∫ ω, exp (l * centeredQuadraticForm μ A X ω) ∂μ ≤ exp (B l) := by
      calc
        ∫ ω, exp (l * centeredQuadraticForm μ A X ω) ∂μ
            = ∫ ω, exp (l * (D ω + O ω)) ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              rw [congrFun hcenter_eq ω]
        _ ≤ exp (B l) := hDO_integral_le
    exact ⟨hcenter_int, hcenter_integral_le⟩
  refine ⟨?_, ?_⟩
  · intro l hl
    have hres := hmain l hl
    have hmgf_pos : 0 < mgf (centeredQuadraticForm μ A X) μ l := mgf_pos hres.1
    have hmgf_le : mgf (centeredQuadraticForm μ A X) μ l ≤ exp (B l) := by
      exact hres.2
    calc
      cgf (centeredQuadraticForm μ A X) μ l
          = log (mgf (centeredQuadraticForm μ A X) μ l) := rfl
      _ ≤ log (exp (B l)) := log_le_log hmgf_pos hmgf_le
      _ = C * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by
        dsimp [B]
        rw [log_exp]
  · intro l hl
    exact (hmain l hl).1

/-- A proved Hanson-Wright MGF certificate for bounded coordinates.

If each coordinate satisfies `|Xᵢ| ≤ K` almost surely, then the quadratic form lies
in the interval `[-K²‖A‖₁, K²‖A‖₁]`.  The centered quadratic form is therefore
bounded by `2K²‖A‖₁`; the local bounded MGF lemma above gives a quadratic CGF
estimate.  The explicit side condition compares this bounded-coordinate constant
with the Frobenius-scale constant used by the Hanson-Wright tail statement. -/
theorem hasHansonWrightMGF_of_bounded {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C : ℝ} (hK : 0 ≤ K) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (hX_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hC_bound : 2 * entrywiseL1Norm A ^ 2 ≤ C * deterministicFrobeniusNorm A ^ 2) :
    HasHansonWrightMGF μ A X K C := by
  set B : ℝ := K ^ 2 * entrywiseL1Norm A with hB_def
  have hB_nonneg : 0 ≤ B := by
    rw [hB_def]
    exact mul_nonneg (sq_nonneg K) (entrywiseL1Norm_nonneg A)
  have hZ_meas : AEMeasurable (randomQuadraticForm A X) μ :=
    randomQuadraticForm_aemeasurable A hX_meas
  have hZ_range :
      ∀ᵐ ω ∂μ, randomQuadraticForm A X ω ∈ Set.Icc (-B) B := by
    simpa [B, hB_def] using
      randomQuadraticForm_mem_Icc_of_ae_coord_bound (μ := μ) A hK hX_bound
  have hZ_int : Integrable (randomQuadraticForm A X) μ :=
    Integrable.of_mem_Icc (-B) B hZ_meas hZ_range
  have hmean_abs : |∫ ω, randomQuadraticForm A X ω ∂μ| ≤ B := by
    have hlower :
        -B ≤ ∫ ω, randomQuadraticForm A X ω ∂μ := by
      calc -B = ∫ _ω, (-B : ℝ) ∂μ := by simp
        _ ≤ ∫ ω, randomQuadraticForm A X ω ∂μ := by
            exact integral_mono_ae (integrable_const _) hZ_int
              (hZ_range.mono fun _ hω => hω.1)
    have hupper :
        ∫ ω, randomQuadraticForm A X ω ∂μ ≤ B := by
      calc ∫ ω, randomQuadraticForm A X ω ∂μ
          ≤ ∫ _ω, (B : ℝ) ∂μ := by
            exact integral_mono_ae hZ_int (integrable_const _)
              (hZ_range.mono fun _ hω => hω.2)
        _ = B := by simp
    exact abs_le.mpr ⟨hlower, hupper⟩
  have hY_meas : AEMeasurable (centeredQuadraticForm μ A X) μ :=
    hZ_meas.sub_const _
  have hY_bound :
      ∀ᵐ ω ∂μ, |centeredQuadraticForm μ A X ω| ≤ 2 * B := by
    filter_upwards [hZ_range] with ω hω
    have hZ_abs : |randomQuadraticForm A X ω| ≤ B := abs_le.mpr hω
    unfold centeredQuadraticForm
    calc |randomQuadraticForm A X ω - ∫ x, randomQuadraticForm A X x ∂μ|
        ≤ |randomQuadraticForm A X ω| + |∫ x, randomQuadraticForm A X x ∂μ| :=
          abs_sub _ _
      _ ≤ B + B := add_le_add hZ_abs hmean_abs
      _ = 2 * B := by ring
  have hY_center : ∫ ω, centeredQuadraticForm μ A X ω ∂μ = 0 := by
    unfold centeredQuadraticForm
    rw [integral_sub hZ_int (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, sub_self]
  have h_sg :
      HasSubgaussianMGF (centeredQuadraticForm μ A X)
        ⟨(2 * B) ^ 2, sq_nonneg (2 * B)⟩ μ :=
    hasSubgaussianMGF_of_abs_le_of_integral_eq_zero hY_meas (by positivity)
      hY_bound hY_center
  refine ⟨?_, fun l _ => h_sg.integrable_exp_mul l⟩
  intro l _
  have h_cgf := h_sg.cgf_le l
  have h_const :
      ((⟨(2 * B) ^ 2, sq_nonneg (2 * B)⟩ : ℝ≥0) : ℝ) * l ^ 2 / 2 =
        2 * B ^ 2 * l ^ 2 := by
    simp
    ring
  calc cgf (centeredQuadraticForm μ A X) μ l
      ≤ ((⟨(2 * B) ^ 2, sq_nonneg (2 * B)⟩ : ℝ≥0) : ℝ) * l ^ 2 / 2 := h_cgf
    _ = 2 * B ^ 2 * l ^ 2 := h_const
    _ ≤ C * l ^ 2 * K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by
        rw [hB_def]
        exact bounded_hansonWright_cgf_constant_le A hC_bound l

/-- Source-transport helper `chernoff_bound_cgf` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma chernoff_bound_cgf {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {l t : ℝ} (hl : 0 ≤ l)
    (hint : Integrable (fun ω => exp (l * Y ω)) μ) :
    (μ {ω | t ≤ Y ω}).toReal ≤ exp (-l * t + cgf Y μ l) := by
  let f : Ω → ENNReal := fun ω => ENNReal.ofReal (exp (l * Y ω))
  let a : ENNReal := ENNReal.ofReal (exp (l * t))
  have hf_meas : AEMeasurable f μ := by
    exact hint.1.aemeasurable.ennreal_ofReal
  have ha_ne_zero : a ≠ 0 := by
    dsimp [a]
    exact ENNReal.ofReal_ne_zero_iff.mpr (exp_pos _)
  have ha_ne_top : a ≠ ⊤ := by
    dsimp [a]
    exact ENNReal.ofReal_ne_top
  have hmarkov : μ {ω | a ≤ f ω} ≤
      (∫⁻ ω, f ω ∂μ) / a := by
    exact MeasureTheory.meas_ge_le_lintegral_div hf_meas ha_ne_zero ha_ne_top
  have hsubset : {ω | t ≤ Y ω} ⊆ {ω | a ≤ f ω} := by
    intro ω hω
    dsimp [a, f]
    exact ENNReal.ofReal_le_ofReal
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hl))
  have hdiv_top : (∫⁻ ω, f ω ∂μ) / a ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact hint.lintegral_lt_top.ne
    · exact ha_ne_zero
  calc
    (μ {ω | t ≤ Y ω}).toReal ≤ (μ {ω | a ≤ f ω}).toReal :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsubset)
    _ ≤ ((∫⁻ ω, f ω ∂μ) / a).toReal :=
      ENNReal.toReal_mono hdiv_top hmarkov
    _ = exp (-l * t + cgf Y μ l) := by
      have hlin : (∫⁻ ω, f ω ∂μ) =
          ENNReal.ofReal (∫ ω, exp (l * Y ω) ∂μ) := by
        change (∫⁻ ω, ENNReal.ofReal (exp (l * Y ω)) ∂μ) = _
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun ω => exp_nonneg _)).symm
      rw [hlin, ENNReal.toReal_div,
        ENNReal.toReal_ofReal (integral_exp_pos hint).le]
      have ha_real : a.toReal = exp (l * t) := by
        dsimp [a]
        exact ENNReal.toReal_ofReal (exp_pos _).le
      rw [ha_real]
      rw [← exp_log (integral_exp_pos hint), ← exp_sub]
      congr 1
      unfold cgf mgf
      ring

/-- Source-transport helper `one_sided_tail_of_cgf_bound` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma one_sided_tail_of_cgf_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {v b C t : ℝ} (hC : 0 < C) (hv : 0 < v) (hb : 0 < b)
    (hcgf : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ → cgf Y μ l ≤ C * l ^ 2 * v)
    (hint : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
      Integrable (fun ω => exp (l * Y ω)) μ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ Y ω}).toReal ≤
      exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · calc (μ {ω | 0 ≤ Y ω}).toReal
      _ ≤ (1 : ℝ) := ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      _ = exp (-(1 / (4 * C)) * min (0 ^ 2 / v) (0 / b)) := by simp
  · set l : ℝ := min (t / (2 * C * v)) ((2 * C * b)⁻¹) with hl_def
    have hden_v : 0 < 2 * C * v := by positivity
    have hden_b : 0 < 2 * C * b := by positivity
    have hl_nonneg : 0 ≤ l := by
      rw [hl_def]
      exact le_min (div_nonneg ht (le_of_lt hden_v)) (inv_nonneg.mpr (le_of_lt hden_b))
    have hl_domain : |l| ≤ (2 * C * b)⁻¹ := by
      rw [abs_of_nonneg hl_nonneg, hl_def]
      exact min_le_right _ _
    have hl_le_v : l ≤ t / (2 * C * v) := by
      rw [hl_def]
      exact min_le_left _ _
    have hl_mul_le_t : l * (2 * C * v) ≤ t := by
      rwa [le_div_iff₀ hden_v] at hl_le_v
    have hquad_le : C * l ^ 2 * v ≤ l * t / 2 := by
      nlinarith [hl_mul_le_t, hl_nonneg, hC.le, hv.le]
    have h_exp_to_half : -l * t + C * l ^ 2 * v ≤ -(l * t / 2) := by
      linarith
    have h_rate :
        l * t / 2 = (1 / (4 * C)) * min (t ^ 2 / v) (t / b) := by
      by_cases hcase : t / (2 * C * v) ≤ (2 * C * b)⁻¹
      · have htb_le_v : t * b ≤ v := by
          rw [inv_eq_one_div] at hcase
          rw [div_le_div_iff₀ hden_v hden_b] at hcase
          nlinarith [hcase, hC, hb]
        have hmin : min (t ^ 2 / v) (t / b) = t ^ 2 / v := by
          rw [min_eq_left]
          rw [div_le_div_iff₀ hv hb]
          nlinarith [htb_le_v, ht_pos]
        rw [hl_def, min_eq_left hcase, hmin]
        field_simp [hC.ne', hv.ne']
        ring
      · have hcase' : (2 * C * b)⁻¹ ≤ t / (2 * C * v) := le_of_not_ge hcase
        have hv_le_tb : v ≤ t * b := by
          rw [inv_eq_one_div] at hcase'
          rw [div_le_div_iff₀ hden_b hden_v] at hcase'
          nlinarith [hcase', hC, hv]
        have hmin : min (t ^ 2 / v) (t / b) = t / b := by
          rw [min_eq_right]
          rw [div_le_div_iff₀ hb hv]
          nlinarith [hv_le_tb, ht_pos]
        rw [hl_def, min_eq_right hcase', hmin]
        field_simp [hC.ne', hb.ne']
        ring
    have h_chernoff := chernoff_bound_cgf
      (μ := μ) (Y := Y) (l := l) (t := t) hl_nonneg (hint l hl_domain)
    calc (μ {ω | t ≤ Y ω}).toReal
      _ ≤ exp (-l * t + cgf Y μ l) := h_chernoff
      _ ≤ exp (-l * t + C * l ^ 2 * v) := by
        exact exp_le_exp.mpr (by linarith [hcgf l hl_domain])
      _ ≤ exp (-(l * t / 2)) := exp_le_exp.mpr h_exp_to_half
      _ = exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
        rw [h_rate]
        ring_nf

/-- A two-sided sub-exponential tail bound from a local quadratic CGF estimate. -/
theorem two_sided_tail_of_cgf_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {v b C t : ℝ} (hC : 0 < C) (hv : 0 < v) (hb : 0 < b)
    (hcgf : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ → cgf Y μ l ≤ C * l ^ 2 * v)
    (hint : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
      Integrable (fun ω => exp (l * Y ω)) μ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |Y ω|}).toReal ≤
      2 * exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
  have hpos := one_sided_tail_of_cgf_bound hC hv hb hcgf hint ht
  have hcgf_neg :
      ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
        cgf (fun ω => -Y ω) μ l ≤ C * l ^ 2 * v := by
    intro l hl
    have h_eq : cgf (fun ω => -Y ω) μ l = cgf Y μ (-l) := by
      unfold cgf mgf
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      congr 1
      ring
    rw [h_eq]
    have hl' : |-l| ≤ (2 * C * b)⁻¹ := by simpa [abs_neg] using hl
    simpa using hcgf (-l) hl'
  have hint_neg : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
      Integrable (fun ω => exp (l * (-Y ω))) μ := by
    intro l hl
    convert hint (-l) (by simpa [abs_neg] using hl) using 1
    ext ω
    ring_nf
  have hneg := one_sided_tail_of_cgf_bound hC hv hb hcgf_neg hint_neg ht
  have h_subset :
      {ω | t ≤ |Y ω|} ⊆ {ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_or_gt 0 (Y ω) with hY | hY
    · left
      simpa [abs_of_nonneg hY] using hω
    · right
      simpa [abs_of_neg hY] using hω
  calc (μ {ω | t ≤ |Y ω|}).toReal
      ≤ (μ ({ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω})).toReal := by
        exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono h_subset)
    _ ≤ (μ {ω | t ≤ Y ω}).toReal + (μ {ω | t ≤ -Y ω}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩)
          (measure_union_le _ _)
    _ ≤ exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) +
        exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
        exact add_le_add hpos hneg
    _ = 2 * exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by ring

end HansonWrightProof
end NLAlib
