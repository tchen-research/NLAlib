import NLAlib.Polynomial.OrthogonalPolynomials.MomentContinuity
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform moment-polynomial continuity on bounded sets

The leading coefficient cancels in a monic difference, leaving a finite sum of
lower coefficient differences. A bounded real set gives an explicit uniform
majorant tending to zero. Source: AQ22 in the operator re-derivations.
-/

noncomputable section
open Polynomial Finset
open scoped Topology
namespace NLAlib

/-- A bounded evaluation point controls the monic-polynomial difference by its
finitely many lower coefficient differences. -/
theorem abs_eval_monicOrthogonalPolynomial_sub_le
    (L M : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) {t R : ℝ} (ht : |t| ≤ R) :
    |(monicOrthogonalPolynomial L n).eval t - (monicOrthogonalPolynomial M n).eval t| ≤
      ∑ i : Fin n, |orthogonalPolynomialCoefficients L n i -
        orthogonalPolynomialCoefficients M n i| * R ^ i.val := by
  have heq : (monicOrthogonalPolynomial L n).eval t -
      (monicOrthogonalPolynomial M n).eval t =
        ∑ i : Fin n, (orthogonalPolynomialCoefficients L n i -
          orthogonalPolynomialCoefficients M n i) * t ^ i.val := by
    simp only [monicOrthogonalPolynomial, orthogonalPolynomialLowerPart,
      eval_add, eval_pow, eval_X, eval_finsetSum, eval_monomial]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_pow]
  gcongr

/-- Canonical monic moment polynomials converge uniformly on every bounded
real set at a nonsingular limiting moment system.
atlas: recurrence-coefficient-continuity (partial) -/
theorem tendstoUniformlyOn_monicOrthogonalPolynomial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : E → (ℝ[X] →ₗ[ℝ] ℝ)} {x : E} {n : ℕ} {s : Set ℝ} {R : ℝ}
    (hL : ∀ k, ContDiffAt ℝ 1 (fun y => L y (X ^ k)) x)
    (hn : hankelMomentDet (L x) n ≠ 0) (hR : ∀ t ∈ s, |t| ≤ R) :
    TendstoUniformlyOn (fun y t => (monicOrthogonalPolynomial (L y) n).eval t)
      (monicOrthogonalPolynomial (L x) n).eval (𝓝 x) s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hbound : Filter.Tendsto (fun y => ∑ i : Fin n,
      |orthogonalPolynomialCoefficients (L y) n i - orthogonalPolynomialCoefficients (L x) n i| *
        R ^ i.val) (𝓝 x) (𝓝 (0 : ℝ)) := by
    have h := tendsto_finsetSum (univ : Finset (Fin n))
      (f := fun i y => |orthogonalPolynomialCoefficients (L y) n i -
        orthogonalPolynomialCoefficients (L x) n i| * R ^ i.val) (fun i _ =>
      (((contDiffAt_orthogonalPolynomialCoefficients hL hn i).continuousAt.sub
        continuousAt_const).abs.mul continuousAt_const))
    simpa only [Pi.mul_apply, Pi.sub_apply, sub_self, abs_zero, zero_mul, sum_const_zero] using h
  filter_upwards [hbound.eventually (eventually_lt_nhds hε)] with y hy
  intro t ht
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_eval_monicOrthogonalPolynomial_sub_le (L y) (L x) n (hR t ht)).trans_lt hy

end NLAlib
