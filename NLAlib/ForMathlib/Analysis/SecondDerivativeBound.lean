import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Integrating a power-weighted second derivative bound

An epsilon regularization converts the moment Hessian bound into a
quadratic bound without requiring the moment to be strictly positive.
Source: matrix_toolkit_open_routes_2026_10_15, F13--F15.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace NLAlib

/-- A global upper bound on the second derivative gives the quadratic
Taylor upper bound at one. -/
theorem le_add_of_second_derivative_le {f f' f'' : ℝ → ℝ} {C : ℝ}
    (h1 : ∀ t, HasDerivAt f (f' t) t)
    (h2 : ∀ t, HasDerivAt f' (f'' t) t)
    (hb : ∀ t, f'' t ≤ 2*C) : f 1 ≤ f 0 + f' 0 + C := by
  let g := fun t => f t - C*t^2
  let g' := fun t => f' t - 2*C*t
  let g'' := fun t => f'' t - 2*C
  have hg1 (t) : HasDerivAt g (g' t) t := by
    convert! (h1 t).sub (((hasDerivAt_id t).pow 2).const_mul C) using 1
    simp [g']
    ring
  have hg2 (t) : HasDerivAt g' (g'' t) t := by
    convert! (h2 t).sub ((hasDerivAt_id t).const_mul (2*C)) using 1
    simp [g'']
  have hc : ConcaveOn ℝ Set.univ g :=
    concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
      (fun t _ => (hg1 t).continuousAt.continuousWithinAt)
      (fun t _ => (hg1 t).hasDerivWithinAt)
      (fun t _ => (hg2 t).hasDerivWithinAt)
      (by intro t _; dsimp [g'']; linarith [hb t])
  have h := hc.slope_le_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    zero_lt_one (hg1 0)
  simp only [slope_def_field, g, g', one_pow, mul_one, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero, div_one] at h
  linarith

/-- The second derivative of a positive real power along a twice
differentiable scalar function. -/
theorem hasDerivAt_power_first {f f' f'' : ℝ → ℝ} {t r : ℝ}
    (h1 : HasDerivAt f (f' t) t) (h2 : HasDerivAt f' (f'' t) t)
    (hf : 0 < f t) :
    HasDerivAt (fun s => r * f s ^ (r-1) * f' s)
      (r*(r-1)*f t^(r-2)*(f' t)^2 + r*f t^(r-1)*f'' t) t := by
  convert! ((h1.rpow_const (p := r-1) (Or.inl hf.ne')).const_mul r).mul h2 using 1
  rw [show r-1-1=r-2 by ring]
  ring

/-- A nonnegative moment with the usual power-weighted Hessian estimate
has a quadratic power bound. It allows zeros of the moment anywhere.
The hypothesis `f' 0 = 0` is supplied by evenness in applications. -/
theorem rpow_le_of_moment_second_derivative_le {f f' f'' : ℝ → ℝ} {p K : ℝ}
    (hp : 2 ≤ p) (hK : 0 ≤ K) (hf : ∀ t, 0 ≤ f t)
    (h1 : ∀ t, HasDerivAt f (f' t) t)
    (h2 : ∀ t, HasDerivAt f' (f'' t) t) (hzero : f' 0=0)
    (hb : ∀ t, f'' t ≤ p*(p-1)*f t^(1-2/p)*K) :
    f 1^(2/p) ≤ f 0^(2/p) + (p-1)*K := by
  have hp0 : 0 < p := by linarith
  let r := 2/p
  have hr : 0 < r := div_pos two_pos hp0
  have hr1 : r ≤ 1 := (div_le_one hp0).mpr hp
  have heps (e : ℝ) (he : 0 < e) :
      (f 1+e)^r ≤ (f 0+e)^r + (p-1)*K := by
    let u := fun t => f t+e
    have hu (t) : 0 < u t := add_pos_of_nonneg_of_pos (hf t) he
    have hu1 (t) : HasDerivAt u (f' t) t := (h1 t).add_const e
    let g := fun t => u t^r
    let g' := fun t => r*u t^(r-1)*f' t
    let g'' := fun t => r*(r-1)*u t^(r-2)*(f' t)^2+r*u t^(r-1)*f'' t
    have hg1 (t) : HasDerivAt g (g' t) t := by
      convert! (hu1 t).rpow_const (p := r) (Or.inl (hu t).ne') using 1
      dsimp [g, g']
      ring
    have hg2 (t) : HasDerivAt g' (g'' t) t :=
      hasDerivAt_power_first (hu1 t) (h2 t) (hu t)
    have hgB (t) : g'' t ≤ 2*((p-1)*K) := by
      have hneg : r*(r-1)*u t^(r-2)*(f' t)^2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos hr.le (by linarith))
            (Real.rpow_nonneg (hu t).le _)) (sq_nonneg _)
      have hprod : u t^(r-1)*f t^(1-r) ≤ 1 := by
        calc
          _ ≤ u t^(r-1)*u t^(1-r) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hf t) (by dsimp [u]; linarith) (by linarith))
            (Real.rpow_nonneg (hu t).le _)
          _ = 1 := by rw [← Real.rpow_add (hu t), show r-1+(1-r)=0 by ring, Real.rpow_zero]
      have hbound := mul_le_mul_of_nonneg_left (hb t)
        (mul_nonneg hr.le (Real.rpow_nonneg (hu t).le (r-1)))
      have hcoef : r*p=2 := by dsimp [r]; field_simp
      have hscale := mul_le_mul_of_nonneg_right hprod
        (mul_nonneg (by linarith : 0 ≤ p-1) hK)
      dsimp only [r] at hbound
      change r*u t^(r-1)*f'' t ≤ r*u t^(r-1)*(p*(p-1)*f t^(1-r)*K) at hbound
      have heq : r*u t^(r-1)*(p*(p-1)*f t^(1-r)*K) =
          2*(u t^(r-1)*f t^(1-r)*((p-1)*K)) := by
        calc
          _ = (r*p)*(u t^(r-1)*f t^(1-r)*((p-1)*K)) := by ring
          _ = _ := by rw [hcoef]
      rw [heq] at hbound
      dsimp [g'']
      linarith
    have h := le_add_of_second_derivative_le hg1 hg2 hgB
    simpa only [g, g', hzero, mul_zero, add_zero, u] using h
  have ht : Tendsto (fun e : ℝ => (f 1+e)^r-(f 0+e)^r)
      (𝓝[Set.Ioi 0] 0) (𝓝 (f 1^r-f 0^r)) := by
    have hc : Continuous (fun e : ℝ => (f 1+e)^r-(f 0+e)^r) :=
      ((continuous_const.add continuous_id).rpow_const (fun _ => Or.inr hr.le)).sub
        ((continuous_const.add continuous_id).rpow_const (fun _ => Or.inr hr.le))
    simpa only [add_zero] using (hc.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 0)
  have hi : f 1^r-f 0^r ≤ (p-1)*K := le_of_tendsto ht
    (eventually_mem_nhdsWithin.mono fun e he => by linarith [heps e he])
  linarith

end NLAlib
