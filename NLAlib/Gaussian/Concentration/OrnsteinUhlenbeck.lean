import NLAlib.Gaussian.Concentration.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Convolution

/-!
# The Ornstein–Uhlenbeck semigroup

`ornsteinUhlenbeck t h x = ∫ h(e^{-t} x + √(1 - e^{-2t}) y) dγ(y)` (Mehler's formula) is the
Ornstein–Uhlenbeck semigroup `P_t` on the standard Gaussian line `γ = N(0,1)`. This file proves

* `integral_ornsteinUhlenbeck`: `γ` is invariant, `∫ P_t h dγ = ∫ h dγ` (`t ≥ 0`);
* `hasDerivAt_ornsteinUhlenbeck`: the commutation relation `(P_t f)' = e^{-t} P_t f'` for
  `f ∈ C¹` with bounded derivative,

together with the rotation-invariance fact behind the first item,
`map_add_mul_prod_gaussianReal`: `(x, y) ↦ a x + b y` pushes `γ ⊗ γ` to `γ` when `a² + b² = 1`.
The entropy dissipation identity is in `NLAlib.Gaussian.Concentration.OrnsteinUhlenbeckEntropy`.

Source: Ledoux, *The Concentration of Measure Phenomenon*, §5.1; Bakry–Gentil–Ledoux 2014, §2.7.1.
Atlas: `ornstein-uhlenbeck`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- The image of `γ ⊗ γ` under `(x, y) ↦ a x + b y` is `γ = N(0,1)` when `a² + b² = 1`.
Atlas: `ornstein-uhlenbeck` (helper). Ported from Prove2me solution
`GaussianMatrix.ou_semigroup_invariant`. -/
theorem map_add_mul_prod_gaussianReal (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      = gaussianReal 0 1 := by
  have h1 : (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (fun x => a * x) (fun y => b * y) := by
    ext p; simp
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  rw [← Measure.conv, gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · apply NNReal.eq; simp [hab]

/-- For `h ∈ L¹(γ)` and `a² + b² = 1`, `∫∫ h(a x + b y) dγ(y) dγ(x) = ∫ h dγ`.
Atlas: `ornstein-uhlenbeck` (helper). Ported from Prove2me solution
`GaussianMatrix.ou_semigroup_invariant`. -/
theorem integral_integral_comp_add_mul_gaussianReal (h : ℝ → ℝ)
    (hh : Integrable h (gaussianReal 0 1)) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ∫ x, (∫ y, h (a * x + b * y) ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ x, h x ∂(gaussianReal 0 1) := by
  have hmap := map_add_mul_prod_gaussianReal a b hab
  have hF : AEMeasurable (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by fun_prop
  have hh' : Integrable h (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => a * p.1 + b * p.2)) := by rw [hmap]; exact hh
  have hcomp : Integrable (fun p : ℝ × ℝ => h (a * p.1 + b * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (integrable_map_measure hh'.aestronglyMeasurable hF).1 hh'
  rw [← integral_prod (fun p : ℝ × ℝ => h (a * p.1 + b * p.2)) hcomp]
  rw [← integral_map hF (by rw [hmap]; exact hh.aestronglyMeasurable), hmap]

/-- The **Ornstein–Uhlenbeck semigroup** on the standard Gaussian line (Mehler's formula):
`P_t h(x) = ∫ h(e^{-t} x + √(1 - e^{-2t}) y) dγ(y)`, `γ = N(0,1)`. Unfolds by `rfl` to the
integral written out in the Prove2me statements. Source: Bakry–Gentil–Ledoux 2014, (2.7.1).
Atlas: `ornstein-uhlenbeck`. Ported from the Prove2me solutions
`GaussianMatrix.ou_entropy_hasDerivAt` (`ouP`) and
`GaussianMatrix.gaussian_logsobolev_bounded_below` (`ouSG`). -/
def ornsteinUhlenbeck (t : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, h (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y) ∂(gaussianReal 0 1)

/-- **Invariance of the Gaussian measure** under the Ornstein–Uhlenbeck semigroup:
`∫ P_t h dγ = ∫ h dγ` for `h ∈ L¹(γ)` and `t ≥ 0`. Source: Bakry–Gentil–Ledoux 2014, §2.7.1;
Ledoux, *Concentration of Measure*, §5.1. Atlas: `ornstein-uhlenbeck`. Ported from Prove2me
solution `GaussianMatrix.ou_semigroup_invariant`. -/
theorem integral_ornsteinUhlenbeck (h : ℝ → ℝ) (hh : Integrable h (gaussianReal 0 1)) (t : ℝ)
    (ht : 0 ≤ t) :
    ∫ x, ornsteinUhlenbeck t h x ∂(gaussianReal 0 1) = ∫ x, h x ∂(gaussianReal 0 1) := by
  apply integral_integral_comp_add_mul_gaussianReal h hh
  have h1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [Real.sq_sqrt (by linarith), sq, ← Real.exp_add]
  ring_nf

/-- A `C¹`-function with bounded derivative composed with an affine map is `γ`-integrable.
Atlas: `ornstein-uhlenbeck` (helper). Ported from Prove2me solution
`GaussianMatrix.ou_semigroup_commutation`. -/
theorem integrable_comp_add_mul_of_abs_deriv_le (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (c d : ℝ) :
    Integrable (fun y => f (c + d * y)) (gaussianReal 0 1) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hdf 0)
  refine Integrable.mono' ((integrable_const (|f 0| + C * |c|)).add
    (integrable_abs_gaussianReal.const_mul (C * |d|))) ?_ ?_
  · exact (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_le_abs_add_mul_abs_of_abs_deriv_le f hf C hdf _).trans ?_
    have : |c + d * y| ≤ |c| + |d| * |y| := by
      rw [← abs_mul]; exact abs_add_le _ _
    simp only [Pi.add_apply]
    nlinarith

/-- **Commutation relation** of the Ornstein–Uhlenbeck semigroup: for `f ∈ C¹` with
`|f'| ≤ C`, `(P_t f)'(x) = e^{-t} P_t f'(x)`. Source: Bakry–Gentil–Ledoux 2014, §2.7.1
(`∇P_t = e^{-t} P_t ∇`). Atlas: `ornstein-uhlenbeck`. Ported from Prove2me solution
`GaussianMatrix.ou_semigroup_commutation`. -/
theorem hasDerivAt_ornsteinUhlenbeck (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (t x : ℝ) :
    HasDerivAt (ornsteinUhlenbeck t f) (Real.exp (-t) * ornsteinUhlenbeck t (deriv f) x) x := by
  unfold ornsteinUhlenbeck
  set a := Real.exp (-t)
  set b := Real.sqrt (1 - Real.exp (-(2 * t)))
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  rw [← integral_const_mul]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun z y => f (a * z + b * y)) (F' := fun z y => a * deriv f (a * z + b * y))
    (x₀ := x) (bound := fun _ => |a| * C) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall (fun z =>
      (hfd.continuous.comp (by fun_prop)).aestronglyMeasurable)
  · exact integrable_comp_add_mul_of_abs_deriv_le f hfd C hdf (a * x) b
  · exact ((hfc.comp (by fun_prop)).const_mul a).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y z _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hdf _) (abs_nonneg _)
  · exact integrable_const _
  · refine Filter.Eventually.of_forall (fun y z _ => ?_)
    have h1 : HasDerivAt (fun z => a * z + b * y) a z := by
      simpa using ((hasDerivAt_id z).const_mul a).add_const (b * y)
    have := (hfd (a * z + b * y)).hasDerivAt.comp z h1
    rw [mul_comm (deriv f _) a] at this
    exact this

end NLAlib
