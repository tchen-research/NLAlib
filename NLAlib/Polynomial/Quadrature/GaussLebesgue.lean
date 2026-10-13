import NLAlib.Polynomial.Quadrature.GaussReflection
import NLAlib.Polynomial.Quadrature.BoundedVariationError

/-! # Sharp bounds for the actual Lebesgue Gauss weights

The integrated cardinal weights at distinct interior orthogonal nodes are
positive, sum to two, and inherit reflection. This supplies the structural
hypotheses of the sharp analytic and BV bounds without assuming them separately.
-/
noncomputable section
open Set MeasureTheory Polynomial Finset
namespace NLAlib

/-- The actual integrated cardinal rule at `(n+1)` interior orthogonal nodes has
positive weights, mass two, exact degree `2n+1`, and paired equal weights.
Source: Trefethen, ATAP, Theorems 19.1 and 19.4. -/
theorem gauss_lebesgue_quadrature_of_orthogonal_nodal
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (hcard : Fintype.card ι = n + 1)
    (v : ι → ℝ) (hv : Function.Injective v) (hvI : ∀ i, v i ∈ Ioo (-1 : ℝ) 1)
    (horth : ∀ p : ℝ[X], p.degree < Fintype.card ι →
      ∫ x in (-1 : ℝ)..1, (Lagrange.nodal univ v).eval x * p.eval x = 0) :
    (∀ i, 0 < ∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x) ∧
    (∑ i, ∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x) = 2 ∧
    (∀ p : ℝ[X], p.degree ≤ (2 * n + 1 : ℕ) →
      (∫ x in (-1 : ℝ)..1, p.eval x) =
        ∑ i, (∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x) * p.eval (v i)) ∧
    (∃ σ : ι ≃ ι, (∀ i, v (σ i) = -v i) ∧
      ∀ i, (∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v (σ i)).eval x) =
        ∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x) := by
  classical
  let μ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hμ : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    exact Ioc_subset_Icc_self hx
  have hvS : InjOn v (univ : Finset ι) := fun i hi j hj h => hv h
  have hsupp : ∀ i ∈ (univ : Finset ι), v i ∈ μ.support := by
    intro i hi
    apply Measure.interior_inter_support
    exact ⟨by rw [interior_Ioc]; exact hvI i, by rw [Measure.support_eq_univ]; trivial⟩
  have hInt (f : ℝ → ℝ) : (∫ x, f x ∂μ) = ∫ x in (-1 : ℝ)..1, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hcardpos : 0 < Fintype.card ι := by omega
  have hnon : (univ : Finset ι).Nonempty := card_pos.mp (by simpa only [card_univ] using hcardpos)
  have hrule := gauss_quadrature_of_orthogonal_nodal hμ univ hnon v hvS
    (fun p hp => by rw [hInt]; exact horth p (by simpa only [card_univ] using hp))
    ⟨v, hvS, hsupp⟩
  have hexact (p : ℝ[X]) (hp : p.degree ≤ (2 * n + 1 : ℕ)) :
      (∫ x in (-1 : ℝ)..1, p.eval x) =
        ∑ i, (∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x) * p.eval (v i) := by
    have hdegree : p.degree < (2 * (univ : Finset ι).card : ℕ) := by
      refine hp.trans_lt ?_
      rw [card_univ, hcard]
      exact_mod_cast (show 2 * n + 1 < 2 * (n + 1) by omega)
    simpa only [hInt] using hrule.2.2 p hdegree
  refine ⟨?_, ?_, hexact, exists_reflection_equiv_of_orthogonal_nodal v hv hvI horth⟩
  · intro i
    simpa only [hInt] using hrule.1 i (mem_univ _)
  · have h := hexact 1 (by rw [degree_one]; exact_mod_cast (show 0 ≤ 2 * n + 1 by omega))
    simpa only [eval_one, mul_one, intervalIntegral.integral_const, sub_neg_eq_add,
      smul_eq_mul, one_add_one_eq_two, mul_one] using h.symm

/-- The actual Lebesgue Gauss cardinal weights have the sharp analytic error
`64M/[15ρ^(2n)(ρ²−1)]`. Positivity, reflection and exactness follow from nodal
orthogonality. Source: Trefethen, ATAP, Theorem 19.4.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_re_sub_gauss_lebesgue_le_of_open_ellipse
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card ι = n + 1) (v : ι → ℝ) (hv : Function.Injective v)
    (hvI : ∀ i, v i ∈ Ioo (-1 : ℝ) 1)
    (horth : ∀ p : ℝ[X], p.degree < Fintype.card ι →
      ∫ x in (-1 : ℝ)..1, (Lagrange.nodal univ v).eval x * p.eval x = 0)
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) :
    |(∫ x in (-1 : ℝ)..1, (F x).re) -
      ∑ i, (∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x) * (F (v i)).re| ≤
        (64 / 15 : ℝ) * M / (ρ ^ (2 * n) * (ρ ^ 2 - 1)) := by
  obtain ⟨hpos, hmass, hexact, σ, hvσ, hwσ⟩ :=
    gauss_lebesgue_quadrature_of_orthogonal_nodal hcard v hv hvI horth
  exact abs_integral_re_sub_symmetric_quadrature_le_of_open_ellipse v
    (fun i => ∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x)
    (fun i => Ioo_subset_Icc_self (hvI i)) (fun i => (hpos i).le)
    hmass σ hvσ hwσ hn hexact hρ hFd hM

/-- The actual Lebesgue Gauss cardinal weights have the corrected BV error
`32V/[15πν(2n+1−ν)^ν]` under the full AC/BV derivative-chain hypotheses.
Source: Trefethen, ATAP, Theorem 19.4 and official 2013-edition errata to (19.10).
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_sub_gauss_lebesgue_le_of_bv
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n ν : ℕ} (hn : 1 ≤ n)
    (hν : 0 < ν) (hnν : ν < 2 * n + 1) (hcard : Fintype.card ι = n + 1)
    (v : ι → ℝ) (hv : Function.Injective v) (hvI : ∀ i, v i ∈ Ioo (-1 : ℝ) 1)
    (horth : ∀ p : ℝ[X], p.degree < Fintype.card ι →
      ∫ x in (-1 : ℝ)..1, (Lagrange.nodal univ v).eval x * p.eval x = 0)
    {F : ℕ → ℝ → ℝ} {V : ℝ}
    (hAC : ∀ j < ν, AbsolutelyContinuousOnInterval (F j) (-1) 1)
    (hderiv : ∀ j < ν, ∀ᵐ x : ℝ, x ∈ Icc (-1 : ℝ) 1 → deriv (F j) x = F (j + 1) x)
    (hBV : BoundedVariationOn (F ν) (Icc (-1 : ℝ) 1))
    (hV : (eVariationOn (F ν) (Icc (-1 : ℝ) 1)).toReal ≤ V) :
    |(∫ x in (-1 : ℝ)..1, F 0 x) -
      ∑ i, (∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x) * F 0 (v i)| ≤
        32 * V / (15 * Real.pi * ν * (2 * (n : ℝ) + 1 - ν) ^ ν) := by
  obtain ⟨hpos, hmass, hexact, σ, hvσ, hwσ⟩ :=
    gauss_lebesgue_quadrature_of_orthogonal_nodal hcard v hv hvI horth
  exact abs_integral_sub_symmetric_quadrature_le_of_bv v
    (fun i => ∫ x in (-1 : ℝ)..1, (Lagrange.basis univ v i).eval x)
    (fun i => Ioo_subset_Icc_self (hvI i)) (fun i => (hpos i).le)
    hmass σ hvσ hwσ hn hν hnν hexact hAC hderiv hBV hV

end NLAlib
