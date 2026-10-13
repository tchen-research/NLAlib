import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.ProductMeasure
import NLAlib.Probability.Gaussian.Basic.StandardGaussian

/-!
# Linear forms of a standard Gaussian vector

For the standard Gaussian vector law `gaussianVector n` on `n → ℝ`:

* `gaussianVector_map_toLp_eq_stdGaussian`, `hasLaw_toLp_gaussianVector`: the bridge to
  Mathlib's `stdGaussian (EuclideanSpace ℝ n)`;
* `hasLaw_dotProduct_gaussianVector`: `v ⬝ g ~ N(0, 1)` for a unit vector `v`;
* `integrable_dotProduct_sq_gaussianVector`, `integral_dotProduct_sq_gaussianVector`:
  `E[(w ⬝ g)²] = ‖w‖²`;
* `hasGaussianLaw_id_gaussianVector`: the identity has a Gaussian law under `gaussianVector n`.

Vershynin 2018, §3.3.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- The standard Gaussian vector pushed to `EuclideanSpace ℝ n` is Mathlib's `stdGaussian`. -/
theorem gaussianVector_map_toLp_eq_stdGaussian :
    (gaussianVector n).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ n) :=
  map_pi_eq_stdGaussian

/-- `WithLp.toLp 2` carries `gaussianVector n` to `stdGaussian (EuclideanSpace ℝ n)`. -/
theorem hasLaw_toLp_gaussianVector :
    HasLaw (WithLp.toLp 2) (stdGaussian (EuclideanSpace ℝ n)) (gaussianVector n) where
  aemeasurable := (by fun_prop : Measurable (WithLp.toLp 2 : (n → ℝ) → _)).aemeasurable
  map_eq := gaussianVector_map_toLp_eq_stdGaussian

set_option backward.isDefEq.respectTransparency false in
/-- A unit linear form of a standard Gaussian vector is a standard Gaussian: `v ⬝ g ~ N(0, 1)`
when `‖v‖ = 1`. Vershynin 2018, Prop 3.3.2 (rotation invariance). -/
theorem hasLaw_dotProduct_gaussianVector (v : n → ℝ) (hv : ‖WithLp.toLp 2 v‖ = 1) :
    HasLaw (fun z => v ⬝ᵥ z) (gaussianReal 0 1) (gaussianVector n) := by
  let w : EuclideanSpace ℝ n := WithLp.toLp 2 v
  let L : StrongDual ℝ (EuclideanSpace ℝ n) := innerSL ℝ w
  have hLsq : ‖L‖ ^ 2 = 1 := by
    rw [show L = innerSL ℝ w from rfl, innerSL_apply_norm, hv, one_pow]
  have hfun : (fun z : n → ℝ => v ⬝ᵥ z) = L ∘ (WithLp.toLp 2) := by
    funext z
    simp [L, w, PiLp.inner_apply, dotProduct, mul_comm]
  refine ⟨(by rw [hfun]; fun_prop : Measurable (fun z : n → ℝ => v ⬝ᵥ z)).aemeasurable, ?_⟩
  rw [hfun, ← Measure.map_map L.continuous.measurable (by fun_prop), map_pi_eq_stdGaussian,
    IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, hLsq]
  simp

/-- A product of two coordinates of a standard Gaussian vector is integrable. -/
theorem integrable_mul_apply_gaussianVector (a b : n) :
    Integrable (fun g : n → ℝ => g a * g b) (gaussianVector n) := by
  classical
  have hmono : ∀ g : n → ℝ,
      g a * g b = ∏ c, g c ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)) := by
    intro g
    simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ, if_true]
  simp_rw [hmono]
  exact Integrable.fintype_prod (f := fun c (x : ℝ) =>
    x ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)))
    (fun c => integrable_pow_gaussianReal _)

/-- The coordinates of a standard Gaussian vector are orthonormal in `L²`:
`E[g a g b] = δ_{ab}`. -/
theorem integral_mul_apply_gaussianVector [DecidableEq n] (a b : n) :
    ∫ g, g a * g b ∂(gaussianVector n) = if a = b then 1 else 0 := by
  have hmono : ∀ g : n → ℝ,
      g a * g b = ∏ c, g c ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)) := by
    intro g
    simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ, if_true]
  have gm2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero aemeasurable_id
      (by simp [integral_id_gaussianReal (μ := 0) (v := 1)])] at h
    simpa using h
  simp_rw [hmono]
  rw [integral_fintype_prod_eq_prod (fun c (x : ℝ) =>
    x ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)))]
  by_cases h : a = b
  · subst h
    rw [Finset.prod_eq_single a]
    · simp [gm2]
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  · rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Ne.symm h])

/-- The square of a linear form of a standard Gaussian vector is integrable. -/
theorem integrable_dotProduct_sq_gaussianVector (w : n → ℝ) :
    Integrable (fun g : n → ℝ => (w ⬝ᵥ g) ^ 2) (gaussianVector n) := by
  have hexp : (fun g : n → ℝ => (w ⬝ᵥ g) ^ 2)
      = fun g => ∑ a, ∑ b, (w a * w b) * (g a * g b) := by
    funext g
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hexp]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_mul_apply_gaussianVector a b).const_mul _

/-- **Second moment of a linear form of a standard Gaussian vector**: `E[(w ⬝ g)²] = ‖w‖²`.
Vershynin 2018, Prop 3.3.2. -/
theorem integral_dotProduct_sq_gaussianVector (w : n → ℝ) :
    ∫ g, (w ⬝ᵥ g) ^ 2 ∂(gaussianVector n) = ‖WithLp.toLp 2 w‖ ^ 2 := by
  classical
  have hexp : (fun g : n → ℝ => (w ⬝ᵥ g) ^ 2)
      = fun g => ∑ a, ∑ b, (w a * w b) * (g a * g b) := by
    funext g
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hexp, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_mul_apply_gaussianVector a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ => (integrable_mul_apply_gaussianVector _ b).const_mul _,
    integral_const_mul, integral_mul_apply_gaussianVector]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [sq]

/-- A vector of independent standard normals has a Gaussian law. Vershynin 2018, §3.3.1. -/
theorem hasGaussianLaw_id_gaussianVector (κ : Type*) [Fintype κ] :
    HasGaussianLaw (fun x : κ → ℝ => x) (gaussianVector κ) := by
  have h := iIndepFun.hasGaussianLaw (P := gaussianVector κ)
    (X := fun k (x : κ → ℝ) => x k) (fun k => ⟨by
      have := (measurePreserving_eval (fun _ : κ => gaussianReal (0 : ℝ) 1) k).map_eq
      rw [this]; infer_instance⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

end NLAlib
