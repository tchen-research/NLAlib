import NLAlib.Gaussian.PolynomialGrowth
import NLAlib.Matrix.Measurable
import NLAlib.Matrix.InversePowerGrowth
import NLAlib.Matrix.GramSoftMinMeasurable

/-!
# Gaussian integrability of regularized Gram derivatives

Explicit polynomial growth of the regularized inverse-power Hessian gives
integrability under the original Gaussian matrix law.
Atlas: wishart-lambda-min-tail.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix

namespace NLAlib

/-- Every natural power of one plus Gaussian Frobenius size is integrable.
Source: Gaussian coordinate moments and finite-dimensional norm comparison;
atlas wishart-lambda-min-tail (regularization domination helper). -/
theorem integrable_one_add_frobSq_gaussianMatrix_pow (r k p : ℕ) :
    Integrable (fun G : Fin r → Fin k → ℝ => (1 + frobSq (Matrix.of G)) ^ p)
      (gaussianMatrix r k) := by
  have hFm : Measurable (fun G : Fin r → Fin k → ℝ => frobSq (Matrix.of G)) :=
    measurable_frobSq_of_entries fun i j => (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hm : Measurable (fun G : Fin r → Fin k → ℝ => (1 + frobSq (Matrix.of G)) ^ p) := by
    fun_prop
  have hdom : Integrable (fun G : Fin r → Fin k → ℝ =>
      (1 + (r : ℝ) * k) ^ p * (1 + ‖G‖) ^ (2 * p)) (gaussianMatrix r k) :=
    (integrable_const_add_norm_gaussianMatrix_pow r k (2 * p) 1 (by norm_num)).const_mul _
  apply hdom.mono' hm.aestronglyMeasurable
  filter_upwards with G
  have hf := frobSq_nonneg (Matrix.of G)
  have hN := norm_nonneg G
  have hd : 0 ≤ (r : ℝ) * k := by positivity
  have hNsq : ‖G‖ ^ 2 ≤ (1 + ‖G‖) ^ 2 := by nlinarith
  have hone : (1 : ℝ) ≤ (1 + ‖G‖) ^ 2 := by nlinarith
  have hbase : 1 + frobSq (Matrix.of G) ≤ (1 + (r : ℝ) * k) * (1 + ‖G‖) ^ 2 := by
    calc
      _ ≤ 1 + (r : ℝ) * k * ‖G‖ ^ 2 :=
        add_le_add (le_refl _) (frobSq_of_le_card_mul_sq_norm G)
      _ ≤ (1 + ‖G‖) ^ 2 + ((r : ℝ) * k) * (1 + ‖G‖) ^ 2 :=
        add_le_add hone (mul_le_mul_of_nonneg_left hNsq hd)
      _ = _ := by ring
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + frobSq (Matrix.of G)) hbase p
  rw [mul_pow, ← pow_mul] at hp
  rw [Real.norm_of_nonneg (pow_nonneg (by linarith : 0 ≤ 1 + frobSq (Matrix.of G)) p)]
  exact hp

/-- A measurable function dominated by an explicit Frobenius polynomial is
Gaussian integrable. Source: Gaussian moments and domination;
atlas wishart-lambda-min-tail (regularization helper). -/
theorem integrable_of_abs_le_frobSq_polynomial_gaussianMatrix
    (r k p : ℕ) (f : (Fin r → Fin k → ℝ) → ℝ) (hf : Measurable f) (C D : ℝ)
    (hbound : ∀ G, |f G| ≤ C + D * (1 + frobSq (Matrix.of G)) ^ p) :
    Integrable f (gaussianMatrix r k) := by
  have hd : Integrable (fun G : Fin r → Fin k → ℝ =>
      C + D * (1 + frobSq (Matrix.of G)) ^ p) (gaussianMatrix r k) :=
    (integrable_const C).add
      ((integrable_one_add_frobSq_gaussianMatrix_pow r k p).const_mul D)
  exact hd.mono' hf.aestronglyMeasurable (Eventually.of_forall fun G => by
    simpa only [Real.norm_eq_abs] using hbound G)

/-- Every coordinate second inverse-power Gram derivative is integrable under the
original Gaussian law at fixed positive regularization. Source: the explicit
operator Hessian growth polynomial and Gaussian moments; atlas
wishart-lambda-min-tail (Stein helper). -/
theorem integrable_gramSoftMinSecond_single_gaussianMatrix
    {r k : ℕ} (hr : 0 < r) (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (i : Fin r) (j : Fin k) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      gramSoftMinSecond n ε (Matrix.of G) (Matrix.single i j 1)) (gaussianMatrix r k) := by
  let : NeZero r := ⟨hr.ne'⟩
  apply integrable_of_abs_le_frobSq_polynomial_gaussianMatrix r k (n + 2)
    _ (measurable_gramSoftMinSecond_single n ε i j) 2
    (4 * ((n : ℝ) + 1) * ε⁻¹ ^ (n + 2) * (1 + ε * r) ^ (n + 1))
  intro G
  simpa only [Fintype.card_fin] using
    abs_gramSoftMinSecond_single_le_frobSq_polynomial n hn ε hε (Matrix.of G) i j

/-- Multiplication of the second Gram derivative by a bounded measurable scalar
test of the regularized minimum preserves integrability. Source: bounded test times
the Gaussian Hessian growth estimate; atlas wishart-lambda-min-tail (Stein helper). -/
theorem integrable_test_mul_gramSoftMinSecond_single_gaussianMatrix
    {r k : ℕ} (hr : 0 < r) (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (i : Fin r) (j : Fin k) (ψ : ℝ → ℝ) (hψ : Measurable ψ) (P : ℝ)
    (hψP : ∀ x, ‖ψ x‖ ≤ P) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      ψ (inversePowerSoftMin n (regularizedGram ε (Matrix.of G))) *
        gramSoftMinSecond n ε (Matrix.of G) (Matrix.single i j 1)) (gaussianMatrix r k) := by
  exact (integrable_gramSoftMinSecond_single_gaussianMatrix hr n hn ε hε i j).bdd_mul
    (hψ.comp (measurable_inversePowerSoftMin_regularizedGram n ε)).aestronglyMeasurable
    (Eventually.of_forall fun G => hψP _)

end NLAlib
