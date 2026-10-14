import NLAlib.Polynomial.Quadrature.StieltjesError
import NLAlib.ForMathlib.Topology.ComplexPolynomialApproximation

/-! # Native complex Gauss convergence and Markov's theorem

Positive weights, increasing polynomial exactness and Weierstrass approximation
give convergence for every continuous complex function on a compact support
interval. Applying this to the scalar resolvent identifies Markov convergence
of the actual second-kind ratios. Infinite support means all orders exist.
Source: Gautschi (2004), Chapter 1; operator derivations AQ20.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Set Finset Filter
open scoped Topology
namespace NLAlib

/-- Actual canonical Gauss rules of increasing order converge for every
continuous complex function on the compact support interval. -/
theorem tendsto_sum_gaussWeights_mul_of_continuousOn
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) (hinf : μ.support.Infinite) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => ∑ i : Fin (n+1), (gaussWeights μ hμ (n+1) i : ℂ) *
      f (gaussNodes μ hμ (n+1) i)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (2 * μ.real univ + 1)
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_complex_polynomial_near_of_continuousOn hf hη
  refine ⟨p.natDegree, ?_⟩
  intro n hn
  have hnμ : (n+1 : ℕ∞) ≤ μ.support.encard := by rw [hinf.encard_eq]; simp
  have hdeg : p.degree < (2*(n+1) : ℕ) :=
    p.degree_le_natDegree.trans_lt (by exact_mod_cast (show p.natDegree < 2*(n+1) by omega))
  have he := norm_integral_sub_sum_gaussWeights_le_of_polynomial_approx hμ hs
    (Nat.zero_lt_succ n) hnμ hf hdeg (fun x hx => (hp x hx).le)
  rw [dist_eq_norm, norm_sub_rev]
  apply he.trans_lt
  have hd : 0 < 2*μ.real univ+1 := by positivity
  change 2*μ.real univ*(ε/(2*μ.real univ+1)) < ε
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hd).mpr
  nlinarith

/-- The actual second-kind ratios converge to the native Stieltjes transform
at every complex point outside the real support interval. The infinite-support
hypothesis ensures the canonical polynomials exist in every degree.
Source: Gautschi (2004), Markov theorem, AQ20.
atlas: jacobi-fraction-second-kind (partial) -/
theorem tendsto_secondKindPolynomial_div_stieltjesTransform
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) (hinf : μ.support.Infinite) {z : ℂ}
    (hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    Tendsto (fun n =>
      ((secondKindPolynomial (polynomialIntegral μ hμ) (n+1)).map Complex.ofRealHom).eval z /
        ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) (n+1)).map Complex.ofRealHom).eval z)
      atTop (𝓝 (stieltjesTransform μ z)) := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  have h := tendsto_sum_gaussWeights_mul_of_continuousOn hμ hs hinf
    ((continuous_const.sub Complex.continuous_ofReal).continuousOn.inv₀
      (fun x hx => sub_ne_zero.mpr (hz x hx)))
  convert! h using 1
  funext n
  rw [eval_map_secondKindPolynomial_div_eq_sum_gaussWeights_div hμ hs
    (Nat.zero_lt_succ n) (by rw [hinf.encard_eq]; simp) hz]
  simp only [div_eq_mul_inv, Pi.inv_apply, Pi.sub_apply]

end NLAlib
