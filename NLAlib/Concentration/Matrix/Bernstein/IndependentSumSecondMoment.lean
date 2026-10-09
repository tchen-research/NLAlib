import NLAlib.Concentration.Matrix.Defs.Probability
import NLAlib.Concentration.Matrix.Defs.Dilation
import Mathlib.Analysis.Convex.Function
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Second moment of an independent centered matrix sum: cross terms vanish

Main declaration: `NLAlib.integral_sum_mul_sum_eq_sum_integral_mul`.

Atlas: `matrix-bernstein` (variance of an independent sum).

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Section 2.2.3, equations (2.2.5)-(2.2.6), printed pp. 27-28 (additivity of the variance of an independent sum; the cross terms vanish by independence and zero mean); used in Theorem 6.1.1 eq. (6.1.2), Theorem 6.6.1, and Theorem 7.3.1 eq. (7.3.2).
-/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace NLAlib

/-- Matrix multiplication as a continuous real-bilinear map (L2 operator norms). -/
private noncomputable def mulCLM (p q r : ℕ) :
    Matrix (Fin p) (Fin q) ℂ →L[ℝ] Matrix (Fin q) (Fin r) ℂ →L[ℝ] Matrix (Fin p) (Fin r) ℂ :=
  LinearMap.mkContinuous₂ (mulLinearMap ℝ) 1
    (fun A B => by simpa using Matrix.l2_opNorm_mul A B)

private lemma mulCLM_apply (p q r : ℕ) (A : Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin q) (Fin r) ℂ) :
    mulCLM p q r A B = A * B := by
  simp [mulCLM]

end NLAlib

open NLAlib

/-- For independent random matrices with `𝔼 f(X k) = 0`, the cross terms vanish: `𝔼 (∑ f(X k)) (∑ g(X
k)) = ∑ 𝔼 f(X k) g(X k)`.

Tropp 2015, §2.2.3, eqs (2.2.5–6). Atlas: `matrix-bernstein`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 6*.

The measurability hypothesis on `X` is not used by the proof; it is kept to match the source's
standing assumptions. -/
theorem NLAlib.integral_sum_mul_sum_eq_sum_integral_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n a b c N : ℕ}
    (X : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ)
    (f : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin a) (Fin b) ℂ)
    (g : Matrix (Fin m) (Fin n) ℂ → Matrix (Fin b) (Fin c) ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (_hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hfL2 : ∀ k, MemLp (fun ω => f (X k ω)) 2 μ)
    (hgL2 : ∀ k, MemLp (fun ω => g (X k ω)) 2 μ)
    (hfMean : ∀ k, (∫ ω, f (X k ω) ∂μ) = 0) :
    (∫ ω, (∑ k, f (X k ω)) * (∑ k, g (X k ω)) ∂μ) =
      ∑ k, ∫ ω, f (X k ω) * g (X k ω) ∂μ := by
  classical
  have hint : ∀ j k, Integrable (fun ω => f (X j ω) * g (X k ω)) μ := by
    intro j k
    have hm : AEStronglyMeasurable (fun ω => f (X j ω) * g (X k ω)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ) => A * B)
        (continuous_fst.matrix_mul continuous_snd) (hfL2 j).1 (hgL2 k).1
    have h1 := MemLp.of_bilin (p := 2) (q := 2) (r := 1)
      (fun (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ) => A * B) 1
      (hfL2 j) (hgL2 k) hm
      (Filter.Eventually.of_forall fun ω => by simpa using Matrix.l2_opNNNorm_mul _ _)
    exact memLp_one_iff_integrable.1 h1
  have hcross : ∀ j k, j ≠ k → ∫ ω, f (X j ω) * g (X k ω) ∂μ = 0 := by
    intro j k hjk
    have hind : IndepFun (fun ω => f (X j ω)) (fun ω => g (X k ω)) μ :=
      (hIndep.indepFun hjk).comp hf hg
    have h2 := hind.integral_bilin ((hfL2 j).integrable one_le_two)
      ((hgL2 k).integrable one_le_two) (mulCLM a b c)
    simp only [mulCLM_apply] at h2
    rw [h2, hfMean j, Matrix.zero_mul]
  simp_rw [Matrix.sum_mul, Matrix.mul_sum]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_finsetSum _ (fun k _ => hint j k)]
  rw [Finset.sum_eq_single j (fun k _ hkj => hcross j k (Ne.symm hkj)) (by simp)]
