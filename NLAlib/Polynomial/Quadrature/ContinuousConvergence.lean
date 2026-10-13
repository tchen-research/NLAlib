import NLAlib.Polynomial.Quadrature.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous convergence of stable polynomial-exact quadrature rules

A uniform bound and eventual polynomial exactness imply convergence on all
continuous functions. Positivity and mass two supply that bound for standard rules.
-/

noncomputable section
open Polynomial Real Set MeasureTheory Filter
open scoped Topology
namespace NLAlib

/-- Lebesgue integration of a continuous function on the unit interval,
as a linear functional. Clamping supplies its canonical real extension.
Source: ordinary interval integration; quadrature convergence. -/
def unitIntervalIntegralLinearMap : C(Icc (-1 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x in (-1 : ℝ)..1, IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f x
  map_add' f g := by
    change (∫ x in (-1 : ℝ)..1,
      IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f x + IccExtend (by norm_num : (-1 : ℝ) ≤ 1) g x) = _
    exact intervalIntegral.integral_add
      (f.continuous.Icc_extend'.intervalIntegrable _ _)
      (g.continuous.Icc_extend'.intervalIntegrable _ _)
  map_smul' c f := by
    change (∫ x in (-1 : ℝ)..1, c * IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f x) = _
    rw [intervalIntegral.integral_const_mul]
    rfl

/-- Interval integration has operator bound two on the unit interval.
Source: the interval integral norm estimate; quadrature convergence. -/
theorem abs_unitIntervalIntegralLinearMap_le (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    |unitIntervalIntegralLinearMap f| ≤ 2 * ‖f‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
    (f := IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f) (C := ‖f‖) (fun x hx => by
      have hx' := uIoc_subset_uIcc hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx'
      rw [IccExtend_of_mem _ _ hx']
      exact f.norm_coe_le_norm ⟨x, hx'⟩)
  simpa only [unitIntervalIntegralLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    Real.norm_eq_abs, sub_neg_eq_add, one_add_one_eq_two, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    mul_comm] using h

/-- Integration of a polynomial restriction is its ordinary interval integral.
Source: clamping is the identity on the interval; quadrature convergence. -/
theorem unitIntervalIntegralLinearMap_polynomial (p : ℝ[X]) :
    unitIntervalIntegralLinearMap (p.toContinuousMapOn (Icc (-1 : ℝ) 1)) =
      ∫ x in (-1 : ℝ)..1, p.eval x := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  rw [IccExtend_of_mem _ _ hx]
  rfl

/-- Uniformly bounded rules which eventually integrate every polynomial exactly
converge on every continuous unit-interval function.
Source: Weierstrass density and the positive-rule argument in ATAP, Chapter 19.
Helper for `gauss-clenshaw-curtis-quadrature-error`. -/
theorem tendsto_quadrature_of_bound_and_polynomial_exact
    (Q : ℕ → (C(Icc (-1 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ)) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n f, |Q n f| ≤ B * ‖f‖)
    (hexact : ∀ (p : ℝ[X]) (n : ℕ), p.natDegree ≤ n →
      Q n (p.toContinuousMapOn (Icc (-1 : ℝ) 1)) = ∫ x in (-1 : ℝ)..1, p.eval x)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    Tendsto (fun n => Q n f) atTop (𝓝 (unitIntervalIntegralLinearMap f)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hden : 0 < B + 2 := by linarith
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap (-1) 1 f
    (ε / (B + 2)) (div_pos hε hden)
  refine ⟨p.natDegree, fun n hn => ?_⟩
  let pc := p.toContinuousMapOn (Icc (-1 : ℝ) 1)
  have hQ : Q n pc = unitIntervalIntegralLinearMap pc :=
    (hexact p n hn).trans (unitIntervalIntegralLinearMap_polynomial p).symm
  have heq : Q n f - unitIntervalIntegralLinearMap f =
      Q n (f - pc) - unitIntervalIntegralLinearMap (f - pc) := by
    rw [map_sub, map_sub, hQ]
    ring
  rw [Real.dist_eq, heq]
  calc
    |Q n (f - pc) - unitIntervalIntegralLinearMap (f - pc)| ≤
        |Q n (f - pc)| + |unitIntervalIntegralLinearMap (f - pc)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (Q n (f - pc)) (unitIntervalIntegralLinearMap (f - pc))
    _ ≤ (B + 2) * ‖f - pc‖ := by
      have hq := hbound n (f - pc)
      have hi := abs_unitIntervalIntegralLinearMap_le (f - pc)
      nlinarith
    _ < (B + 2) * (ε / (B + 2)) := by
      apply mul_lt_mul_of_pos_left _ hden
      simpa only [pc, norm_sub_rev] using hp
    _ = ε := mul_div_cancel₀ ε hden.ne'

end NLAlib
