import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.ProductMeasure

/-!
# Linear forms of a standard Gaussian vector

For `g` with law `Measure.pi fun _ : Fin r => gaussianReal 0 1`:

* `pi_gaussianReal_map_dotProduct_unit`: `v ⬝ g ~ N(0, 1)` for a unit vector `v`;
* `integrable_and_integral_dotProduct_sq_pi_gaussianReal`: `E[(w ⬝ g)²] = w ⬝ w`;
* `hasGaussianLaw_id_pi_gaussianReal`: the identity has a Gaussian law under the product of
  standard normals (moved from the former `Probability/Gaussian/Basic/GaussianMatrix.lean`).

Moved from `NLAlib.RandomMatrix.Gaussian.InverseMoments.Probe` and `…OffDiagonal` (dedup round,
2026-10-12). Atlas: helpers of `gaussian-positive-moments`, `inverse-wishart-frob-moment`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

set_option backward.isDefEq.respectTransparency false in
/-- A unit directional Gaussian probe is a scalar standard Gaussian.
Source: Gaussian orthogonal invariance; atlas `gaussian-positive-moments` (probe interface). -/
theorem pi_gaussianReal_map_dotProduct_unit {r : ℕ} (v : Fin r → ℝ)
    (hv : v ⬝ᵥ v = 1) :
    (Measure.pi fun _ : Fin r => gaussianReal 0 1).map (fun z => v ⬝ᵥ z)
      = gaussianReal 0 1 := by
  let w : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 v
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin r)) := innerSL ℝ w
  have hLsq : ‖L‖ ^ 2 = 1 := by
    rw [show L = innerSL ℝ w from rfl, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]
    simpa [w, dotProduct, sq] using hv
  have hfun : (fun z : Fin r → ℝ => v ⬝ᵥ z) = L ∘ (WithLp.toLp 2) := by
    funext z
    simp [L, w, PiLp.inner_apply, dotProduct, mul_comm]
  rw [hfun, ← Measure.map_map L.continuous.measurable (by fun_prop), map_pi_eq_stdGaussian,
    IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, hLsq]
  simp

/-- **Second moment of a linear form of a standard Gaussian vector.** For `w ∈ ℝᵏ` and `g` a
standard Gaussian vector, `(w ⬝ g)²` is integrable and `E[(w ⬝ g)²] = w ⬝ w`.

Helper for Tropp–Webber 2023, Lemma B.2. Atlas: `inverse-wishart-frob-moment` (helper). Ported
from the Prove2me solution `Sol_GaussianMatrix_inverse_wishart_offdiag_sq_moment`
(`iwg_gauss_sq`). -/
theorem integrable_and_integral_dotProduct_sq_pi_gaussianReal {k : ℕ} (w : Fin k → ℝ) :
    Integrable (fun g : Fin k → ℝ => (w ⬝ᵥ g) ^ 2) (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, (w ⬝ᵥ g) ^ 2 ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = w ⬝ᵥ w := by
  set μ := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  have hmono : ∀ (a b : Fin k) (g : Fin k → ℝ),
      g a * g b = ∏ c, g c ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)) := by
    intro a b g
    simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ, if_true]
  have gint : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) (gaussianReal 0 1) := by
    intro m
    have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (m : NNReal)).integrable_norm_pow'
    refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_pow]
  have hint2 : ∀ a b : Fin k, Integrable (fun g : Fin k → ℝ => g a * g b) μ := by
    intro a b
    simp_rw [hmono a b]
    exact Integrable.fintype_prod (f := fun c (x : ℝ) =>
      x ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0))) (fun c => gint _)
  have gm2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero aemeasurable_id
      (by simp [integral_id_gaussianReal (μ := 0) (v := 1)])] at h
    simpa using h
  have hval2 : ∀ a b : Fin k, ∫ g, g a * g b ∂μ = if a = b then 1 else 0 := by
    intro a b
    simp_rw [hmono a b]
    rw [hμ, integral_fintype_prod_eq_prod (fun c (x : ℝ) =>
      x ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)))]
    by_cases h : a = b
    · subst h
      rw [Finset.prod_eq_single a]
      · simp [gm2]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Ne.symm h])
  have hexp : (fun g : Fin k → ℝ => (w ⬝ᵥ g) ^ 2)
      = fun g => ∑ a, ∑ b, (w a * w b) * (g a * g b) := by
    funext g
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (hint2 a b).const_mul _, ?_⟩
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint2 a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ => (hint2 _ b).const_mul _, integral_const_mul, hval2]
  simp [dotProduct]

/-- A vector of independent standard normals has a Gaussian law. Ported from Prove2me solution
`GaussianMatrix.gordon_upper` (helper `gu_hasGaussianLaw_pi`). Atlas: `gaussian-matrix-def`. -/
theorem hasGaussianLaw_id_pi_gaussianReal (κ : Type*) [Fintype κ] :
    HasGaussianLaw (fun x : κ → ℝ => x) (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have h := iIndepFun.hasGaussianLaw (P := Measure.pi fun _ : κ => gaussianReal 0 1)
    (X := fun k (x : κ → ℝ) => x k) (fun k => ⟨by
      have := (measurePreserving_eval (fun _ : κ => gaussianReal (0 : ℝ) 1) k).map_eq
      rw [this]; infer_instance⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

end NLAlib
