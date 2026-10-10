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
import NLAlib.Concentration.HansonWright.TailAssembly

/-!
# Hanson–Wright proof: UniversalBound

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

/-- Hanson-Wright tail bound with the MGF certificate proved from sub-Gaussian coordinates.

This theorem does not take `HasHansonWrightMGF` as a hypothesis.  Instead it proves
that certificate from independence and coordinate sub-Gaussian MGF bounds, then
optimizes the resulting Chernoff bound. -/
theorem hanson_wright_inequality {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C t : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hC_domain : 4 * exp 1 ≤ C)
    (hC_diag_quad : 8 * exp 1 ^ 3 ≤ C)
    (hC_offdiag_domain : 16 * exp 1 ≤ C ^ 2)
    (hC_offdiag_quad : 64 * exp 1 ^ 2 ≤ C)
    (hF : 0 < deterministicFrobeniusNorm A) (hOp : 0 < deterministicOperatorNorm A)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (ht : 0 ≤ t) :
    (μ {ω | t ≤ |centeredQuadraticForm μ A X ω|}).toReal ≤
      2 * exp (-(1 / (4 * C)) *
        min (t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2))
          (t / (K ^ 2 * deterministicOperatorNorm A))) := by
  have hHW : HasHansonWrightMGF μ A X K C :=
    hasHansonWrightMGF_of_subgaussian hK hC hC_domain hC_diag_quad
      hC_offdiag_domain hC_offdiag_quad hOp h_indep hX_subG
  have hv : 0 < K ^ 4 * deterministicFrobeniusNorm A ^ 2 := by positivity
  have hb : 0 < K ^ 2 * deterministicOperatorNorm A := by positivity
  exact two_sided_tail_of_cgf_bound hC hv hb
    (Y := centeredQuadraticForm μ A X)
    (fun l hl => by
      have hl' : |l| ≤ (2 * C * K ^ 2 * deterministicOperatorNorm A)⁻¹ := by
        convert hl using 2
        ring
      simpa [mul_assoc, mul_left_comm, mul_comm] using hHW.1 l hl')
    (fun l hl => by
      have hl' : |l| ≤ (2 * C * K ^ 2 * deterministicOperatorNorm A)⁻¹ := by
        convert hl using 2
        ring
      exact hHW.2 l hl') ht

/-- Source-transport helper `hanson_wright_scaled_rhs_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma hanson_wright_scaled_rhs_le {K C F O t : ℝ} (hK : 0 < K)
    (hC : 0 < C) (hF : 0 < F) (hO : 0 < O) (ht : 0 ≤ t) :
    2 * exp (-(1 / (4 * (C / 16))) *
        min (t ^ 2 / ((2 * K) ^ 4 * F ^ 2))
          (t / ((2 * K) ^ 2 * O))) ≤
      2 * exp (-(1 / (4 * C)) *
        min (t ^ 2 / (K ^ 4 * F ^ 2))
          (t / (K ^ 2 * O))) := by
  set q : ℝ := t ^ 2 / (K ^ 4 * F ^ 2) with hq_def
  set r : ℝ := t / (K ^ 2 * O) with hr_def
  have hq_nonneg : 0 ≤ q := by
    rw [hq_def]
    positivity
  have hr_nonneg : 0 ≤ r := by
    rw [hr_def]
    positivity
  have hq_scaled :
      t ^ 2 / ((2 * K) ^ 4 * F ^ 2) = q / 16 := by
    rw [hq_def]
    field_simp [hK.ne', hF.ne']
    ring
  have hr_scaled :
      t / ((2 * K) ^ 2 * O) = r / 4 := by
    rw [hr_def]
    field_simp [hK.ne', hO.ne']
    ring
  have hcoef : 1 / (4 * (C / 16)) = 4 / C := by
    field_simp [hC.ne']
    ring
  have hmin_scaled : min q r / 16 ≤ min (q / 16) (r / 4) := by
    apply le_min
    · exact div_le_div_of_nonneg_right (min_le_left q r) (by norm_num)
    · calc
        min q r / 16 ≤ r / 16 :=
          div_le_div_of_nonneg_right (min_le_right q r) (by norm_num)
        _ ≤ r / 4 := by nlinarith [hr_nonneg]
  have harg :
      -(1 / (4 * (C / 16))) *
        min (t ^ 2 / ((2 * K) ^ 4 * F ^ 2)) (t / ((2 * K) ^ 2 * O)) ≤
      -(1 / (4 * C)) *
        min (t ^ 2 / (K ^ 4 * F ^ 2)) (t / (K ^ 2 * O)) := by
    rw [hq_scaled, hr_scaled, hcoef]
    change -(4 / C) * min (q / 16) (r / 4) ≤ -(1 / (4 * C)) * min q r
    have hneg : -(4 / C) ≤ 0 := by
      have hpos : 0 ≤ 4 / C := by positivity
      linarith
    calc
      -(4 / C) * min (q / 16) (r / 4)
          ≤ -(4 / C) * (min q r / 16) :=
            mul_le_mul_of_nonpos_left hmin_scaled hneg
      _ = -(1 / (4 * C)) * min q r := by
          field_simp [hC.ne']
          ring
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr harg) (by norm_num)

/-- Convenience wrapper for the Hanson-Wright bound with an explicit coordinate
sub-Gaussian MGF scale and the same deterministic matrix hypotheses. -/
theorem hanson_wright_inequality_hdp_explicit {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C t : ℝ} (hK : 0 < K)
    (hC : 0 < C) (hC_domain : 4 * exp 1 ≤ C)
    (hC_diag_quad : 8 * exp 1 ^ 3 ≤ C)
    (hC_offdiag_domain : 16 * exp 1 ≤ C ^ 2)
    (hC_offdiag_quad : 64 * exp 1 ^ 2 ≤ C)
    (hF : 0 < deterministicFrobeniusNorm A) (hOp : 0 < deterministicOperatorNorm A)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (ht : 0 ≤ t) :
    (μ {ω | t ≤ |centeredQuadraticForm μ A X ω|}).toReal ≤
      2 * exp (-(1 / (4 * C)) *
        min (t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2))
          (t / (K ^ 2 * deterministicOperatorNorm A))) := by
  exact
    hanson_wright_inequality (μ := μ) (A := A) (X := X) (K := K) (C := C)
      (t := t) hK hC hC_domain hC_diag_quad hC_offdiag_domain
      hC_offdiag_quad hF hOp h_indep hX_subG ht

/-- The universal numerical constant used by the public Hanson-Wright endpoint. -/
def hansonWrightUniversalConstant : ℝ :=
  1 / (4 * (64 * exp 1 ^ 2))

/-- Source-transport helper `hansonWrightUniversalConstant_pos` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
theorem hansonWrightUniversalConstant_pos :
    0 < hansonWrightUniversalConstant := by
  simp only [hansonWrightUniversalConstant]
  positivity

/-- Hanson-Wright inequality with the public universal constant exposed in the
statement. The constant is independent of the matrix, coordinate family, and
sub-Gaussian scale. -/
theorem hanson_wright_inequality_hdp_explicit_constant
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K : ℝ} (hK : 0 < K)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) :
    ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ |centeredQuadraticForm μ A X ω|}).toReal ≤
        2 * exp (-hansonWrightUniversalConstant *
          min (t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2))
            (t / (K ^ 2 * deterministicOperatorNorm A))) := by
  let C0 : ℝ := 64 * exp 1 ^ 2
  have hexp_pos : 0 < exp 1 := exp_pos 1
  have hexp_ge_one : 1 ≤ exp 1 := one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hexp_le_eight : exp 1 ≤ 8 := by
    nlinarith [exp_one_lt_three.le]
  have hC0_pos : 0 < C0 := by
    dsimp [C0]
    positivity
  have hC0_domain : 4 * exp 1 ≤ C0 := by
    dsimp [C0]
    have hmul := mul_le_mul_of_nonneg_left hexp_ge_one
      (by positivity : 0 ≤ 4 * exp 1)
    nlinarith
  have hC0_diag_quad : 8 * exp 1 ^ 3 ≤ C0 := by
    dsimp [C0]
    have hmul := mul_le_mul_of_nonneg_left hexp_le_eight
      (by positivity : 0 ≤ 8 * exp 1 ^ 2)
    nlinarith
  have hC0_ge_offdiag : 16 * exp 1 ≤ C0 := by
    dsimp [C0]
    have hmul := mul_le_mul_of_nonneg_left hexp_ge_one
      (by positivity : 0 ≤ 16 * exp 1)
    nlinarith
  have hC0_ge_one : 1 ≤ C0 := by
    dsimp [C0]
    nlinarith [hexp_ge_one, sq_nonneg (exp 1)]
  have hC0_sq_ge : C0 ≤ C0 ^ 2 := by
    have hC0_nonneg : 0 ≤ C0 := hC0_pos.le
    have hmul := mul_le_mul hC0_ge_one (le_refl C0) hC0_nonneg hC0_nonneg
    simpa [pow_two] using hmul
  have hC0_offdiag_domain : 16 * exp 1 ≤ C0 ^ 2 :=
    hC0_ge_offdiag.trans hC0_sq_ge
  have hC0_offdiag_quad : 64 * exp 1 ^ 2 ≤ C0 := by
    dsimp [C0]
    rfl
  change ∀ t : ℝ, 0 ≤ t →
    (μ {ω | t ≤ |centeredQuadraticForm μ A X ω|}).toReal ≤
      2 * exp (-(1 / (4 * C0)) *
        min (t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2))
          (t / (K ^ 2 * deterministicOperatorNorm A)))
  intro t ht
  by_cases hF : 0 < deterministicFrobeniusNorm A
  · by_cases hOp : 0 < deterministicOperatorNorm A
    · exact
        hanson_wright_inequality (μ := μ) (A := A) (X := X)
          (K := K) (C := C0) (t := t) hK hC0_pos hC0_domain
          hC0_diag_quad hC0_offdiag_domain hC0_offdiag_quad hF hOp
          h_indep hX_subG ht
    · have hOp_nonneg : 0 ≤ deterministicOperatorNorm A := by
        unfold deterministicOperatorNorm
        exact norm_nonneg _
      have hOp_zero : deterministicOperatorNorm A = 0 := le_antisymm (le_of_not_gt hOp) hOp_nonneg
      have hfirst_nonneg :
          0 ≤ t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2) := by positivity
      have hsecond_zero : t / (K ^ 2 * deterministicOperatorNorm A) = 0 := by
        rw [hOp_zero, mul_zero, div_zero]
      have hmin :
          min (t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2))
              (t / (K ^ 2 * deterministicOperatorNorm A)) = 0 := by
        rw [hsecond_zero, min_eq_right hfirst_nonneg]
      calc
        (μ {ω | t ≤ |centeredQuadraticForm μ A X ω|}).toReal ≤ (1 : ℝ) :=
          ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
        _ ≤ 2 * exp (-(1 / (4 * C0)) *
            min (t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2))
              (t / (K ^ 2 * deterministicOperatorNorm A))) := by
            rw [hmin]
            norm_num
  · have hF_nonneg : 0 ≤ deterministicFrobeniusNorm A := by
      unfold deterministicFrobeniusNorm
      exact sqrt_nonneg _
    have hF_zero : deterministicFrobeniusNorm A = 0 := le_antisymm (le_of_not_gt hF) hF_nonneg
    have hOp_nonneg : 0 ≤ deterministicOperatorNorm A := by
      unfold deterministicOperatorNorm
      exact norm_nonneg _
    have hfirst_zero :
        t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2) = 0 := by
      rw [hF_zero]
      simp
    have hsecond_nonneg : 0 ≤ t / (K ^ 2 * deterministicOperatorNorm A) :=
      div_nonneg ht (mul_nonneg (sq_nonneg K) hOp_nonneg)
    have hmin :
        min (t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2))
            (t / (K ^ 2 * deterministicOperatorNorm A)) = 0 := by
      rw [hfirst_zero, min_eq_left hsecond_nonneg]
    calc
      (μ {ω | t ≤ |centeredQuadraticForm μ A X ω|}).toReal ≤ (1 : ℝ) :=
        ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      _ ≤ 2 * exp (-(1 / (4 * C0)) *
          min (t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2))
            (t / (K ^ 2 * deterministicOperatorNorm A))) := by
          rw [hmin]
          norm_num

/-- Existential-form compatibility wrapper for the Hanson-Wright endpoint.
The witness is the public `hansonWrightUniversalConstant`. -/
theorem hanson_wright_inequality_hdp {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K : ℝ} (hK : 0 < K)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ |centeredQuadraticForm μ A X ω|}).toReal ≤
        2 * exp (-c *
          min (t ^ 2 / (K ^ 4 * deterministicFrobeniusNorm A ^ 2))
            (t / (K ^ 2 * deterministicOperatorNorm A))) := by
  exact ⟨hansonWrightUniversalConstant, hansonWrightUniversalConstant_pos,
    hanson_wright_inequality_hdp_explicit_constant hK h_indep hX_subG⟩

end HansonWrightProof
end NLAlib
