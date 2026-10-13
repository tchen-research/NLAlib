/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Ported from HighDimProb (Y. Zhang, J. D. Lee, F. Liu; Apache-2.0),
HighDimProb/Concentration/HansonWright.lean, to Lean 4.33.1.
The original Apache-2.0 copyright notice is retained. The proof is stated in NLAlib's matrix
vocabulary (`quadForm`, `frobSq`, `frobNorm`, `specNorm`); there is no HighDimProb dependency.
-/
import NLAlib.Probability.Concentration.QuadraticForms.GaussianProductIntegrability
import NLAlib.Probability.SubGaussian.CenteredSquare
import NLAlib.ForMathlib.Probability.IndepExpSum
/-!
# Hanson–Wright proof: DiagonalCGF

A focused leaf of the transported independent-coordinate proof.
Its declarations live in namespace `NLAlib` (generic scalar sub-Gaussian facts are in
`NLAlib.Probability.SubGaussian.*`); the public bounds are in `NLAlib.Probability.Concentration.QuadraticForms.HansonWright`.
Atlas: `hanson-wright`. Source: HighDimProb (Zhang–Lee–Liu, Apache-2.0).
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The centered diagonal part of a quadratic form. -/
def diagonalCenteredQuadraticForm {n : ℕ} (μ : Measure Ω)
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, A i i * (X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂μ)

open scoped Matrix.Norms.L2Operator in
/-- Source-transport helper `diagonalCenteredQuadraticForm_cgf_le` for Hanson–Wright.
Atlas `hanson-wright` (helper). -/
lemma diagonalCenteredQuadraticForm_cgf_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C θ : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hC_domain : exp 1 ≤ C) (hC_quad : 2 * exp 1 ^ 3 ≤ C)
    (hOp : 0 < specNorm A)
    (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hθ : |θ| ≤ (2 * C * K ^ 2 * specNorm A)⁻¹) :
    cgf (diagonalCenteredQuadraticForm μ A X) μ θ ≤
      C * θ ^ 2 * K ^ 4 * frobNorm A ^ 2 := by
  let Y : Fin n → Ω → ℝ :=
    fun i ω => X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂μ
  let Z : Fin n → Ω → ℝ := fun i ω => A i i * Y i ω
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hK
  have hKsq_nonneg : 0 ≤ K ^ 2 := hKsq_pos.le
  have hC0_le : ((⟨K ^ 2, sq_nonneg K⟩ : ℝ≥0) : ℝ) ≤ K ^ 2 := by simp
  have hscale :
      |θ| * K ^ 2 * specNorm A ≤ 1 / (2 * C) := by
    have hfactor_nonneg : 0 ≤ K ^ 2 * specNorm A :=
      mul_nonneg hKsq_nonneg (specNorm_nonneg A)
    calc
      |θ| * K ^ 2 * specNorm A
          = |θ| * (K ^ 2 * specNorm A) := by ring_nf
      _ ≤ (2 * C * K ^ 2 * specNorm A)⁻¹ * (K ^ 2 * specNorm A) :=
          mul_le_mul_of_nonneg_right hθ hfactor_nonneg
      _ = 1 / (2 * C) := by
          field_simp [hC.ne', hKsq_pos.ne', hOp.ne']
  have hhalf_i : ∀ i, |A i i * θ| * K ^ 2 * exp 1 ≤ 1 / 2 := by
    intro i
    have hdiag := abs_diag_le_specNorm A i
    have hθ_abs_nonneg : 0 ≤ |θ| := abs_nonneg θ
    have hle_op :
        |θ| * |A i i| * K ^ 2 ≤ |θ| * specNorm A * K ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiag hθ_abs_nonneg) hKsq_nonneg
    calc
      |A i i * θ| * K ^ 2 * exp 1
          = (|θ| * |A i i| * K ^ 2) * exp 1 := by
              rw [abs_mul]
              ring_nf
      _ ≤ (|θ| * specNorm A * K ^ 2) * exp 1 :=
          mul_le_mul_of_nonneg_right hle_op (exp_nonneg 1)
      _ = (|θ| * K ^ 2 * specNorm A) * exp 1 := by ring_nf
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
      simpa only [Y] using iIndepFun_centered_sq (μ := μ) (X := X) hind
    simpa only [Z, Function.comp_def] using
      hY_indep.comp (fun i x => A i i * x) (fun _ => by fun_prop)
  have hZ_meas : ∀ i, AEMeasurable (Z i) μ := by
    intro i
    change AEMeasurable
      (fun ω => A i i * (X i ω ^ 2 - ∫ ω, X i ω ^ 2 ∂μ)) μ
    exact (((hmgf i).aemeasurable.pow_const 2).sub_const _).const_mul _
  have hZ_int :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Integrable (fun ω => exp (θ * Z i ω)) μ := by
    intro i _
    have hsmall_lt : |A i i * θ| * K ^ 2 * exp 1 < 1 := by
      linarith [hhalf_i i]
    have hint :=
      integrable_exp_centered_sq_of_hasSubgaussianMGF_of_le
        (hmgf i) hKsq_pos hC0_le hsmall_lt
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
        (hmgf i) hKsq_pos hC0_le (hhalf_i i)
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
        C * θ ^ 2 * K ^ 4 * frobNorm A ^ 2 := by
    have hnonneg : 0 ≤ θ ^ 2 * K ^ 4 := by positivity
    have hdiag_le := sum_diag_sq_le_frobNorm_sq A
    calc
      (2 * exp 1 ^ 3) * θ ^ 2 * K ^ 4 * ∑ i, A i i ^ 2
          = (2 * exp 1 ^ 3) * (θ ^ 2 * K ^ 4) * ∑ i, A i i ^ 2 := by ring_nf
      _ ≤ C * (θ ^ 2 * K ^ 4) * ∑ i, A i i ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC_quad hnonneg)
            (Finset.sum_nonneg fun i _ => sq_nonneg (A i i))
      _ ≤ C * (θ ^ 2 * K ^ 4) * frobNorm A ^ 2 := by
          exact mul_le_mul_of_nonneg_left hdiag_le
            (mul_nonneg hC.le hnonneg)
      _ = C * θ ^ 2 * K ^ 4 * frobNorm A ^ 2 := by ring_nf
  calc
    cgf (diagonalCenteredQuadraticForm μ A X) μ θ
        = cgf (fun ω => ∑ i, Z i ω) μ θ := by rfl
    _ = ∑ i, cgf (Z i) μ θ := hcgf_sum
    _ ≤ ∑ i, 2 * exp 1 * (A i i * θ * K ^ 2 * exp 1) ^ 2 := hsum_cgf_le
    _ = (2 * exp 1 ^ 3) * θ ^ 2 * K ^ 4 * ∑ i, A i i ^ 2 := hsum_eq
    _ ≤ C * θ ^ 2 * K ^ 4 * frobNorm A ^ 2 := hconst_le

end NLAlib
