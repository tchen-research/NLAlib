import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Algebra.Polynomial

/-! # Hermite's circle integral formula

A finite resolvent identity for Lagrange interpolation, followed by the ordinary
circle Cauchy formula, proves the interpolant and interpolation-error formulas.
-/

noncomputable section
open Polynomial Set Complex
namespace NLAlib

/-- The finite resolvent identity for arbitrary distinct interpolation nodes.
Source: Trefethen, ATAP, proof of Theorem 11.1; the algebraic ingredient of
`hermite-integral-formula`. The empty interpolation set is included. -/
theorem nodal_resolvent_eq_sum_basis_div {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → F) (hv : Set.InjOn v s) {t x : F}
    (ht : ∀ i ∈ s, t ≠ v i) (hx : t ≠ x) :
    ((Lagrange.nodal s v).eval t - (Lagrange.nodal s v).eval x) /
      ((Lagrange.nodal s v).eval t * (t - x)) =
        ∑ i ∈ s, (Lagrange.basis s v i).eval x / (t - v i) := by
  classical
  let l := Lagrange.nodal s v
  let Q := l /ₘ (X - C t)
  have hl : l ≠ 0 := (Lagrange.nodal_monic (s := s) (v := v)).ne_zero
  have hlt : l.eval t ≠ 0 := by
    rw [Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => sub_ne_zero.mpr (ht i hi))
  have hQdeg : Q.degree < s.card := by
    have h := degree_divByMonic_lt l (X - C t) hl (by simp)
    simpa [l, Lagrange.degree_nodal] using h
  have hQeval (y : F) : l.eval t + (y - t) * Q.eval y = l.eval y := by
    have h := congrArg (fun P : F[X] => P.eval y) (modByMonic_add_div l (X - C t))
    simpa only [modByMonic_X_sub_C_eq_C_eval, eval_add, eval_C, eval_mul,
      eval_sub, eval_X] using h
  have hRdeg : (C (l.eval t)⁻¹ * Q).degree < s.card :=
    (degree_mul_le_of_le (degree_C_le) (le_refl Q.degree)).trans_lt (by simpa using hQdeg)
  have hR : C (l.eval t)⁻¹ * Q = Lagrange.interpolate s v (fun i => (t - v i)⁻¹) := by
    refine Lagrange.eq_interpolate_of_eval_eq _ hv hRdeg ?_
    intro i hi
    have h := hQeval (v i)
    rw [show l.eval (v i) = 0 from Lagrange.eval_nodal_at_node hi] at h
    simp only [eval_mul, eval_C]
    field_simp [hlt, sub_ne_zero.mpr (ht i hi)]
    linear_combination -h
  have hRx := congrArg (fun P : F[X] => P.eval x) hR
  simp only [eval_mul, eval_C, Lagrange.interpolate_apply, eval_finsetSum] at hRx
  have hQx := hQeval x
  change (l.eval t - l.eval x) / (l.eval t * (t - x)) = _
  simp only [div_eq_inv_mul]
  rw [← hRx]
  field_simp [hlt, sub_ne_zero.mpr hx]
  linear_combination hQx

private theorem sphere_ne_of_mem_ball {c t x : ℂ} {R : ℝ}
    (ht : t ∈ Metric.sphere c R) (hx : x ∈ Metric.ball c R) : t ≠ x := by
  intro h
  subst t
  exact (ne_of_lt (Metric.mem_ball.mp hx)) (Metric.mem_sphere.mp ht)

private theorem circleIntegrable_div_sub {f : ℂ → ℂ} {c x : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : ContinuousOn f (Metric.closedBall c R))
    (hx : x ∈ Metric.ball c R) : CircleIntegrable (fun t => f t / (t - x)) c R := by
  exact ((hf.mono Metric.sphere_subset_closedBall).div
    (continuous_id.sub continuous_const).continuousOn
    (fun t ht => sub_ne_zero.mpr (sphere_ne_of_mem_ball ht hx))).circleIntegrable hR

/-- Hermite's formula writes the Lagrange interpolant as one circle integral.
Source: Trefethen, ATAP, Theorem 11.1. It suffices that `f` is holomorphic in the
open disc and continuous on its closure; all nodes and the evaluation point are interior.
The empty set of nodes is included.
atlas: hermite-integral-formula -/
theorem eval_interpolate_eq_circleIntegral {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℂ) (hv : Set.InjOn v s) {f : ℂ → ℂ} {c x : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hvR : ∀ i ∈ s, v i ∈ Metric.ball c R) (hx : x ∈ Metric.ball c R) :
    (Lagrange.interpolate s v (f ∘ v)).eval x = (2 * Real.pi * I : ℂ)⁻¹ *
      ∮ t in C(c, R), f t *
        (((Lagrange.nodal s v).eval t - (Lagrange.nodal s v).eval x) /
          ((Lagrange.nodal s v).eval t * (t - x))) := by
  have hc : ContinuousOn f (Metric.closedBall c R) := by
    simpa only [closure_ball c hR.ne.symm] using hf.continuousOn
  have hInt (i : ι) (h : i ∈ s) := circleIntegrable_div_sub hR.le hc (hvR i h)
  have heq : (∮ t in C(c, R), f t *
        (((Lagrange.nodal s v).eval t - (Lagrange.nodal s v).eval x) /
          ((Lagrange.nodal s v).eval t * (t - x)))) =
        ∮ t in C(c, R), ∑ i ∈ s, (Lagrange.basis s v i).eval x • (f t / (t - v i)) := by
    refine circleIntegral.integral_congr hR.le ?_
    intro t ht
    dsimp only
    rw [nodal_resolvent_eq_sum_basis_div s v hv
      (fun i hi => sphere_ne_of_mem_ball ht (hvR i hi)) (sphere_ne_of_mem_ball ht hx),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_eq_mul]
    ring
  have hsum := circleIntegral.integral_fun_sum
    (f := fun i t => (Lagrange.basis s v i).eval x • (f t / (t - v i)))
    (fun i hi => (hInt i hi).const_smul)
  rw [heq, hsum]
  simp_rw [circleIntegral.integral_smul]
  rw [Finset.mul_sum]
  have hC (i : ι) (hi : i ∈ s) : (2 * Real.pi * I : ℂ)⁻¹ *
      (∮ t in C(c, R), f t / (t - v i)) = f (v i) := by
    simpa only [smul_eq_mul, div_eq_inv_mul] using
      hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (hvR i hi)
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, Function.comp_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_left_comm, hC i hi, mul_comm]

/-- Hermite's interpolation error formula holds also when the evaluation point is a node.
Source: Trefethen, ATAP, Theorem 11.1. A circle contour is used, matching Mathlib's
Cauchy formula; no interpolation remainder theorem is needed.
atlas: hermite-integral-formula -/
theorem sub_eval_interpolate_eq_circleIntegral {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℂ) (hv : Set.InjOn v s) {f : ℂ → ℂ} {c x : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hvR : ∀ i ∈ s, v i ∈ Metric.ball c R) (hx : x ∈ Metric.ball c R) :
    f x - (Lagrange.interpolate s v (f ∘ v)).eval x =
      (Lagrange.nodal s v).eval x * (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ t in C(c, R), f t / ((Lagrange.nodal s v).eval t * (t - x)) := by
  let l := Lagrange.nodal s v
  have hc : ContinuousOn f (Metric.closedBall c R) := by
    simpa only [closure_ball c hR.ne.symm] using hf.continuousOn
  have hlt (t : ℂ) (ht : t ∈ Metric.sphere c R) : l.eval t ≠ 0 := by
    rw [Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr fun i hi =>
      sub_ne_zero.mpr (sphere_ne_of_mem_ball ht (hvR i hi))
  have hE : CircleIntegrable (fun t => f t / (l.eval t * (t - x))) c R := by
    refine ((hc.mono Metric.sphere_subset_closedBall).div
      (l.continuous.continuousOn.mul (continuous_id.sub continuous_const).continuousOn)
      (fun t ht => mul_ne_zero (hlt t ht)
        (sub_ne_zero.mpr (sphere_ne_of_mem_ball ht hx)))).circleIntegrable hR.le
  have hX := circleIntegrable_div_sub hR.le hc hx
  have hK : (∮ t in C(c, R), f t *
        ((l.eval t - l.eval x) / (l.eval t * (t - x)))) =
      ∮ t in C(c, R), f t / (t - x) - l.eval x • (f t / (l.eval t * (t - x))) := by
    refine circleIntegral.integral_congr hR.le ?_
    intro t ht
    dsimp only
    simp only [smul_eq_mul]
    field_simp [hlt t ht, sub_ne_zero.mpr (sphere_ne_of_mem_ball ht hx)]
  have hP := eval_interpolate_eq_circleIntegral s v hv hR hf hvR hx
  change (Lagrange.interpolate s v (f ∘ v)).eval x = (2 * Real.pi * I : ℂ)⁻¹ *
    (∮ t in C(c, R), f t * ((l.eval t - l.eval x) / (l.eval t * (t - x)))) at hP
  have hC : (2 * Real.pi * I : ℂ)⁻¹ * (∮ t in C(c, R), f t / (t - x)) = f x := by
    simpa only [smul_eq_mul, div_eq_inv_mul] using
      hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hx
  have hIntSub := circleIntegral.integral_sub
    (f := fun t => f t / (t - x))
    (g := fun t => l.eval x • (f t / (l.eval t * (t - x)))) hX hE.const_smul
  rw [hK, hIntSub,
    circleIntegral.integral_smul, smul_eq_mul, mul_sub, hC] at hP
  change f x - (Lagrange.interpolate s v (f ∘ v)).eval x =
    l.eval x * (2 * Real.pi * I : ℂ)⁻¹ * _
  rw [hP]
  ring

end NLAlib
