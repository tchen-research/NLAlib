import NLAlib.Probability.Rademacher.Core
import NLAlib.Probability.SubGaussian.ExpSquare
import NLAlib.Matrix.Norms.Core
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Directional square-exponential control for independent signs

Every unit projection of an independent Rademacher vector satisfies a
dimension-free exponential-square bound. The convenient parameter `10`
is deliberately unoptimized; it places the bounded-entry lower witnesses
in a fixed admissible sub-Gaussian factor class.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace NLAlib

variable {ι : Type*} [Fintype ι]

/-- A unit directional projection of independent signs has sub-Gaussian
MGF variance proxy one. -/
theorem hasSubgaussianMGF_dotProduct_rademacherVector
    (u : ι → ℝ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
    HasSubgaussianMGF (fun x : ι → ℝ => u ⬝ᵥ x) 1 (rademacherVector ι) := by
  have hs : ∑ i, u i ^ 2 = 1 := by
    have h := norm_toLp_sq_eq_dotProduct_self u
    rw [hu] at h
    simpa only [dotProduct, pow_two, one_mul] using h.symm
  have hproxy : (∑ i, Real.toNNReal (u i ^ 2) * (1 : ℝ≥0)) = 1 := by
    apply NNReal.eq
    simpa only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_one, mul_one,
      Real.coe_toNNReal', max_eq_left (sq_nonneg _)] using hs
  have h := hasSubgaussianMGF_finset_sum_mul_of_iIndepFun
    (iIndepFun_eval_rademacherVector ι)
    (c := fun _ => (1 : ℝ≥0))
    (s := Finset.univ)
    (fun i _ => hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hasLaw_eval_rademacherVector i)) u
  simpa only [hproxy, dotProduct] using h

/-- Independent sign vectors satisfy the manuscript's directional
exponential-square factor hypothesis with the fixed parameter `10`.
This parameter is sufficient and is not claimed optimal.
atlas: khatri-rao-sharp-growth (partial) -/
theorem lintegral_exp_sq_dotProduct_rademacherVector_le_two
    (u : ι → ℝ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal (Real.exp ((u ⬝ᵥ x) ^ 2 / (10 : ℝ) ^ 2))
      ∂rademacherVector ι) ≤ 2 := by
  have hmgf := hasSubgaussianMGF_dotProduct_rademacherVector u hu
  have he0 := Real.exp_pos (1 : ℝ)
  have he3 := Real.exp_one_lt_three
  have hsmall : (1 / 100 : ℝ) * 1 * Real.exp 1 < 1 := by linarith
  have hi := integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le hmgf
    (θ := 1 / 100) (C0 := 1) (by norm_num) (by norm_num) (by norm_num) hsmall
  have hb := integral_exp_mul_sq_le_one_add_tail_of_hasSubgaussianMGF_of_le hmgf
    (θ := 1 / 100) (C0 := 1) (by norm_num) (by norm_num) (by norm_num) hsmall
  have hbound : (∫ x : ι → ℝ, Real.exp ((1 / 100 : ℝ) * (u ⬝ᵥ x) ^ 2)
      ∂rademacherVector ι) ≤ 2 := by
    apply hb.trans
    have hden : 0 < 1 - (1 / 100 : ℝ) * 1 * Real.exp 1 := by linarith
    rw [show Real.exp 1 * ((1 / 100 : ℝ) * 1 * Real.exp 1 *
        (1 - (1 / 100 : ℝ) * 1 * Real.exp 1)⁻¹) =
        (Real.exp 1 * ((1 / 100 : ℝ) * 1 * Real.exp 1)) /
          (1 - (1 / 100 : ℝ) * 1 * Real.exp 1) by ring]
    have heSq : Real.exp 1 ^ 2 < 9 := by nlinarith
    have ht : Real.exp 1 * ((1 / 100 : ℝ) * 1 * Real.exp 1) /
        (1 - (1 / 100 : ℝ) * 1 * Real.exp 1) ≤ 1 :=
      (div_le_one hden).2 (by nlinarith)
    linarith
  have hexp (x : ι → ℝ) : Real.exp ((u ⬝ᵥ x) ^ 2 / (10 : ℝ) ^ 2) =
      Real.exp ((1 / 100 : ℝ) * (u ⬝ᵥ x) ^ 2) := by congr 1; ring
  simp_rw [hexp]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  exact (ENNReal.ofReal_le_ofReal hbound).trans_eq (by norm_num)

end NLAlib
