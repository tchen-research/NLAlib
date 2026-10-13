import NLAlib.Polynomial.Quadrature.ClenshawCurtisWeights
import NLAlib.Polynomial.Quadrature.ContinuousConvergence

/-!
# Clenshaw–Curtis convergence for continuous functions

Actual positive weights of mass two and exactness on every eventual polynomial
degree give continuous convergence by polynomial density.
-/

noncomputable section
open Polynomial Polynomial.Chebyshev Real Set MeasureTheory Filter
open scoped Topology
namespace NLAlib

/-- The finite weighted continuous-function rule is the actual integrated
interpolant of the function's canonical extension.
Source: integrating Lagrange's formula; ATAP, Chapter 19. -/
theorem clenshawCurtisLinearMap_apply_eq_rule (n : ℕ) (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    clenshawCurtisLinearMap n f =
      clenshawCurtisRule n (IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f) := by
  rw [clenshawCurtisRule_eq_sum_weights]
  change (∑ j ∈ Finset.range (n + 1), clenshawCurtisWeight n j *
    f ⟨node n j, node_mem_Icc⟩) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [IccExtend_of_mem _ _ node_mem_Icc]

/-- The actual rule integrates every polynomial through its degree cutoff exactly.
Source: uniqueness of degree-bounded Lagrange interpolation; ATAP, Chapter 19. -/
theorem clenshawCurtisRule_polynomial_exact {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    clenshawCurtisRule n p.eval = ∫ x in (-1 : ℝ)..1, p.eval x := by
  have hdeg : p.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    exact p.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hp)
  have hpoly := Lagrange.eq_interpolate (v := node n) (chebyshev_node_injOn n) hdeg
  rw [clenshawCurtisRule]
  have hvalues : p.eval ∘ node n = fun j => p.eval (node n j) := rfl
  rw [hvalues, ← hpoly]

/-- The actual continuous-function Clenshaw–Curtis functional is eventually
exact on every polynomial restriction.
Source: polynomial exactness and the finite weight formula; ATAP, Chapter 19. -/
theorem clenshawCurtisLinearMap_polynomial_exact (p : ℝ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    clenshawCurtisLinearMap n (p.toContinuousMapOn (Icc (-1 : ℝ) 1)) =
      ∫ x in (-1 : ℝ)..1, p.eval x := by
  rw [← clenshawCurtisRule_polynomial_exact hp, clenshawCurtisRule_eq_sum_weights]
  rfl

/-- Actual Clenshaw–Curtis quadrature converges on every continuous function
on the unit interval.
Source: positive actual weights, polynomial exactness, and Weierstrass density;
Trefethen, ATAP, Chapter 19.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem tendsto_clenshawCurtisLinearMap (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    Tendsto (fun n => clenshawCurtisLinearMap n f) atTop (𝓝 (unitIntervalIntegralLinearMap f)) :=
  tendsto_quadrature_of_bound_and_polynomial_exact clenshawCurtisLinearMap 2 (by norm_num)
    abs_clenshawCurtisLinearMap_le clenshawCurtisLinearMap_polynomial_exact f

/-- Actual Clenshaw–Curtis quadrature converges to the interval integral for
every continuous unit-interval real function.
Source: positive actual weights and polynomial density; Trefethen, ATAP, Chapter 19.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem tendsto_clenshawCurtisRule_of_continuousOn {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto (fun n => clenshawCurtisRule n f) atTop (𝓝 (∫ x in (-1 : ℝ)..1, f x)) := by
  let fc : C(Icc (-1 : ℝ) 1, ℝ) := ⟨fun x => f x, hf.domRestrict⟩
  have hrule : ∀ n, clenshawCurtisLinearMap n fc = clenshawCurtisRule n f := by
    intro n
    rw [clenshawCurtisRule_eq_sum_weights]
    rfl
  have hint : unitIntervalIntegralLinearMap fc = ∫ x in (-1 : ℝ)..1, f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    rw [IccExtend_of_mem _ _ hx]
    rfl
  have h := tendsto_clenshawCurtisLinearMap fc
  simp only [hrule, hint] at h
  exact h

end NLAlib
