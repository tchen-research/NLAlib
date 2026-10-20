import NLAlib.Probability.Gaussian.Calculus.CovarianceIntegral
import NLAlib.Probability.Gaussian.Basic.StandardVector
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Complex Gaussian variance controlled by the coordinate gradient

The exact native covariance integral, applied to a centered complex test
and its conjugate, yields the standard Gaussian Poincare constant one.
The gradient premise is a genuine pointwise finite coordinate sum.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
namespace NLAlib

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
local notation "E" => κ → ℝ

omit [DecidableEq κ] in
private theorem poincare_integral_id_standard :
    (∫ x : E, x ∂gaussianVector κ) = 0 := by
  have hi := (hasGaussianLaw_id_gaussianVector κ).memLp_two.integrable one_le_two
  ext k
  have he := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) k).integral_comp_comm hi
  have hz := integral_eq_zero_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k)
  simpa only [ContinuousLinearMap.proj_apply, Pi.zero_apply] using he.symm.trans hz

private theorem poincare_covariance_standard (i j : κ) :
    cov[(fun x : E => x i), (fun x : E => x j); gaussianVector κ] =
      if i = j then 1 else 0 := by
  rw [covariance_eq_sub (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector i))
    (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector j))]
  simp only [Pi.mul_apply]
  rw [integral_mul_apply_gaussianVector,
    integral_eq_zero_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector i),
    zero_mul, sub_zero]

omit [DecidableEq κ] in
private theorem norm_sum_mul_conj_le_of_sum_sq
    (a b : κ → ℂ) (V : ℝ)
    (ha : ∑ i, ‖a i‖ ^ 2 ≤ V) (hb : ∑ i, ‖b i‖ ^ 2 ≤ V) :
    ‖∑ i, a i * star (b i)‖ ≤ V := by
  have hYoung : 2 * (∑ i, ‖a i‖ * ‖b i‖) ≤
      (∑ i, ‖a i‖ ^ 2) + (∑ i, ‖b i‖ ^ 2) := by
    calc
      _ = ∑ i, 2 * (‖a i‖ * ‖b i‖) := Finset.mul_sum _ _ _
      _ ≤ ∑ i, (‖a i‖ ^ 2 + ‖b i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]
      _ = _ := Finset.sum_add_distrib
  have hsum : ∑ i, ‖a i‖ * ‖b i‖ ≤ V := by linarith
  calc
    _ ≤ ∑ i, ‖a i * star (b i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖a i‖ * ‖b i‖ := by simp only [norm_mul, norm_star]
    _ ≤ V := hsum

/-- The actual centered second moment of a bounded complex C¹ test on the
native standard Gaussian product is at most a uniform squared-coordinate
gradient bound, with the sharp scalar constant one. Continuous uniformly
bounded Frechet derivatives supply all integrability conditions. Empty
coordinate types and a zero gradient budget are included.
Source: the Gaussian Poincare consequence of Bandeira--Boedihardjo--van Handel,
arXiv:2108.06312v2, Corollary 4.12. -/
theorem integral_norm_sub_integral_sq_le_gaussian_gradient_bound
    (f : E → ℂ) (df : E → E →L[ℝ] ℂ)
    (hf : ∀ x, HasFDerivAt f (df x) x) (hdfc : Continuous df)
    (Cf Cd V : ℝ) (hfb : ∀ x, ‖f x‖ ≤ Cf) (hdfb : ∀ x, ‖df x‖ ≤ Cd)
    (hgrad : ∀ x, ∑ i, ‖df x (Pi.single i 1)‖ ^ 2 ≤ V) :
    (∫ x : E, ‖f x - ∫ y : E, f y ∂gaussianVector κ‖ ^ 2 ∂gaussianVector κ) ≤ V := by
  let : IsGaussian (gaussianVector κ) := by
    have h := (hasGaussianLaw_id_gaussianVector κ).isGaussian_map
    change IsGaussian ((gaussianVector κ).map id) at h
    rwa [Measure.map_id] at h
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hCd : 0 ≤ Cd := (norm_nonneg (df 0)).trans (hdfb 0)
  have hfint : Integrable f (gaussianVector κ) :=
    Integrable.of_bound hfc.aestronglyMeasurable Cf (Eventually.of_forall hfb)
  let m : ℂ := ∫ y : E, f y ∂gaussianVector κ
  let f0 : E → ℂ := fun x => f x - m
  have hf0 (x : E) : HasFDerivAt f0 (df x) x := (hf x).sub_const m
  have hf0b (x : E) : ‖f0 x‖ ≤ Cf + ‖m‖ :=
    (norm_sub_le _ _).trans (add_le_add (hfb x) le_rfl)
  have hf0mean : (∫ x : E, f0 x ∂gaussianVector κ) = 0 := by
    simp only [f0, integral_sub hfint (integrable_const _), integral_const,
      probReal_univ, one_smul, m, sub_self]
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.mul ℝ ℂ).bilinearComp
      (ContinuousLinearMap.id ℝ ℂ) Complex.conjCLE.toContinuousLinearMap
  have hB (a b : ℂ) : B a b = a * star b := rfl
  have hcov := integral_bilin_sub_bilin_integrals_eq_gaussian_covariance_integral
    (gaussianVector κ) poincare_integral_id_standard f0 df f0 df hf0 hdfc hf0 hdfc
    (Cf + ‖m‖) Cd (Cf + ‖m‖) Cd hf0b hdfb hf0b hdfb B
  simp only [poincare_covariance_standard, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at hcov
  simp only [hf0mean, map_zero, sub_zero] at hcov
  simp only [hB] at hcov
  let H (t : ℝ) (q : E × E) : ℂ := ∑ i,
    df q.1 (Pi.single i 1) * star
      (df (t • q.1 + Real.sqrt (1 - t ^ 2) • q.2) (Pi.single i 1))
  have hsingle (x : E) (i : κ) : ‖df x (Pi.single i 1)‖ ≤ Cd := by
    simpa only [Pi.norm_single, norm_one, mul_one] using
      ((df x).le_opNorm (Pi.single i 1)).trans
        (mul_le_mul_of_nonneg_right (hdfb x) (norm_nonneg _))
  have hkernelint (t : ℝ) (i : κ) : Integrable (fun q : E × E =>
      df q.1 (Pi.single i 1) * star
        (df (t • q.1 + Real.sqrt (1 - t ^ 2) • q.2) (Pi.single i 1)))
        ((gaussianVector κ).prod (gaussianVector κ)) := by
    have hc : Continuous (fun q : E × E => df q.1 (Pi.single i 1) * star
        (df (t • q.1 + Real.sqrt (1 - t ^ 2) • q.2) (Pi.single i 1))) := by fun_prop
    apply Integrable.of_bound hc.aestronglyMeasurable (Cd * Cd)
    exact Eventually.of_forall fun q => by
      rw [norm_mul, norm_star]
      exact mul_le_mul (hsingle q.1 i) (hsingle _ i) (norm_nonneg _) hCd
  have hvariance :
      ((∫ x : E, ‖f0 x‖ ^ 2 ∂gaussianVector κ : ℝ) : ℂ) =
        ∫ t : ℝ in (0 : ℝ)..1,
          ∫ q : E × E, H t q ∂(gaussianVector κ).prod (gaussianVector κ) := by
    calc
      _ = ∫ x : E, f0 x * star (f0 x) ∂gaussianVector κ := by
        rw [← integral_complex_ofReal]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change ((‖f0 x‖ ^ 2 : ℝ) : ℂ) = f0 x * (starRingEnd ℂ) (f0 x)
          rw [Complex.mul_conj', Complex.ofReal_pow]
      _ = ∫ t : ℝ in (0 : ℝ)..1, ∑ i, ∫ q : E × E,
          df q.1 (Pi.single i 1) * star
            (df (t • q.1 + Real.sqrt (1 - t ^ 2) • q.2) (Pi.single i 1))
              ∂(gaussianVector κ).prod (gaussianVector κ) := hcov
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t _
        exact (integral_finsetSum _ fun i _ => hkernelint t i).symm
  have hHbound (t : ℝ) (q : E × E) : ‖H t q‖ ≤ V :=
    norm_sum_mul_conj_le_of_sum_sq _ _ V (hgrad q.1) (hgrad _)
  have hHintegral (t : ℝ) :
      ‖∫ q : E × E, H t q ∂(gaussianVector κ).prod (gaussianVector κ)‖ ≤ V := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const
        (μ := (gaussianVector κ).prod (gaussianVector κ))
        (Eventually.of_forall (hHbound t))
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t (_ : t ∈ Set.uIoc (0 : ℝ) 1) => hHintegral t)
  rw [← hvariance] at hbound
  have hnonneg : 0 ≤ ∫ x : E, ‖f0 x‖ ^ 2 ∂gaussianVector κ :=
    integral_nonneg fun _ => sq_nonneg _
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    sub_zero, abs_one, mul_one, f0, m] using hbound

end NLAlib
