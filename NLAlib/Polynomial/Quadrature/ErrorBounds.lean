import NLAlib.Polynomial.Quadrature.ClenshawCurtisConvergence
import NLAlib.Polynomial.Quadrature.GaussContinuousConvergence
import NLAlib.Polynomial.Quadrature.ClenshawCurtisEventual

/-! # Complete Gauss and Clenshaw–Curtis quadrature guarantees

The sharp analytic constants, corrected BV denominators, explicit eventual
Clenshaw–Curtis threshold, and convergence on every continuous function are
assembled for the actual endpoint interpolant and integrated Gauss cardinal rules.
This module realises atlas `gauss-clenshaw-curtis-quadrature-error`.
-/
noncomputable section
open Set MeasureTheory Polynomial Finset Filter
open scoped Topology
namespace NLAlib

/-- Actual Clenshaw–Curtis and Lebesgue Gauss quadrature satisfy all sharp analytic
and BV bounds and converge for every continuous function. Gauss nodes are supplied
through the natural distinct-interior orthogonal-nodal interface; positivity,
reflection and exactness of their integrated cardinal weights are proved from it.
The eventual Clenshaw–Curtis bound uses an explicit sufficient threshold.
Source: Trefethen, ATAP, Theorems 19.3–19.5, official 2013-edition errata to
equations (19.10) and (19.12),
and focused polynomial-approximation reroutes, explicit eventual-bound theorem.
atlas: gauss-clenshaw-curtis-quadrature-error -/
theorem quadrature_error_bounds_and_continuous_convergence
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    (hcard : ∀ n, Fintype.card (ι n) = n + 1)
    (v : ∀ n, ι n → ℝ) (hv : ∀ n, Function.Injective (v n))
    (hvI : ∀ n i, v n i ∈ Ioo (-1 : ℝ) 1)
    (horth : ∀ n (p : ℝ[X]), p.degree < Fintype.card (ι n) →
      ∫ x in (-1 : ℝ)..1, (Lagrange.nodal univ (v n)).eval x * p.eval x = 0)
    {A : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hAd : DifferentiableOn ℂ A (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖A z‖ ≤ M)
    {ν : ℕ} {F : ℕ → ℝ → ℝ} {V : ℝ} (hν : 0 < ν)
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    (∀ n : ℕ, 2 ≤ n →
      |(∫ x in (-1 : ℝ)..1, (A x).re) - clenshawCurtisRule n (fun x => (A x).re)| ≤
        (64 / 15 : ℝ) * M / (ρ ^ (n - 1) * (ρ ^ 2 - 1))) ∧
    (∀ n : ℕ, 1 ≤ n →
      |(∫ x in (-1 : ℝ)..1, (A x).re) -
        ∑ i, (∫ x in (-1 : ℝ)..1, (Lagrange.basis univ (v n) i).eval x) * (A (v n i)).re| ≤
          (64 / 15 : ℝ) * M / (ρ ^ (2 * n) * (ρ ^ 2 - 1))) ∧
    (∀ n : ℕ, ν < n → 2 ≤ n →
      |(∫ x in (-1 : ℝ)..1, F 0 x) - clenshawCurtisRule n (F 0)| ≤
        32 * V / (15 * Real.pi * ν * ((n : ℝ) - ν) ^ ν)) ∧
    (∀ n : ℕ, 1 ≤ n → ν < 2 * n + 1 →
      |(∫ x in (-1 : ℝ)..1, F 0 x) -
        ∑ i, (∫ x in (-1 : ℝ)..1, (Lagrange.basis univ (v n) i).eval x) * F 0 (v n i)| ≤
          32 * V / (15 * Real.pi * ν * (2 * (n : ℝ) + 1 - ν) ^ ν)) ∧
    (∀ n : ℕ, quadratureBvThreshold ν ≤ n →
      |(∫ x in (-1 : ℝ)..1, F 0 x) - clenshawCurtisRule n (F 0)| ≤
        32 * V / (15 * Real.pi * ν * (2 * (n : ℝ) + 1 - ν) ^ ν)) ∧
    Tendsto (fun n => clenshawCurtisRule n f) atTop (𝓝 (∫ x in (-1 : ℝ)..1, f x)) ∧
    Tendsto (fun n => ∑ i, (∫ x in (-1 : ℝ)..1,
      (Lagrange.basis univ (v n) i).eval x) * f (v n i)) atTop
        (𝓝 (∫ x in (-1 : ℝ)..1, f x)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact abs_integral_re_sub_clenshawCurtisRule_le_of_open_ellipse hρ hAd hM hn
  · intro n hn
    exact abs_integral_re_sub_gauss_lebesgue_le_of_open_ellipse hn (hcard n)
      (v n) (hv n) (hvI n) (horth n) hρ hAd hM
  · intro n hn hn2
    exact abs_integral_sub_clenshawCurtisRule_le_of_bv hν hn hn2 hAC hderiv hBV hV
  · intro n hn hnν
    exact abs_integral_sub_gauss_lebesgue_le_of_bv hn hν hnν (hcard n)
      (v n) (hv n) (hvI n) (horth n) hAC hderiv hBV hV
  · intro n hn
    exact abs_integral_sub_clenshawCurtisRule_le_eventual_of_bv hν hn hAC hderiv hBV hV
  · exact tendsto_clenshawCurtisRule_of_continuousOn hf
  · exact tendsto_gauss_lebesgue_of_continuousOn hcard v hv hvI horth hf

end NLAlib
