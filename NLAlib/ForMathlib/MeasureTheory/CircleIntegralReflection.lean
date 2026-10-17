import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Real circle integrals of Schwarz-symmetric functions

Conjugation reverses the circle's orientation. Consequently the normalized
circle integral of a Schwarz-symmetric function is real. These generic
identities support the realness of Stahl's exterior contour density.
-/

noncomputable section

open Complex MeasureTheory Set Metric
open scoped Interval ComplexConjugate

namespace circleIntegral

/-- Schwarz symmetry on the integration circle makes its unnormalized
contour integral purely imaginary. No differentiability assumption is needed:
the identity follows from the circle parametrization and orientation reversal.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem conj_eq_neg_of_conj_eq {f : ℂ → ℂ} {r : ℝ}
    (hf : ∀ z ∈ sphere (0 : ℂ) |r|, f (conj z) = conj (f z)) :
    conj (∮ z in C(0, r), f z) = -(∮ z in C(0, r), f z) := by
  let F : ℝ → ℂ := fun θ => circleMap 0 r θ * I * f (circleMap 0 r θ)
  have hF : Function.Periodic F (2 * Real.pi) := by
    intro θ
    dsimp [F]
    rw [(periodic_circleMap 0 r) θ]
  have hc (θ : ℝ) : conj (F θ) = -F (-θ) := by
    have hs := hf (circleMap 0 r θ) (circleMap_mem_sphere' 0 r θ)
    dsimp [F]
    rw [map_mul, map_mul, conj_I, conj_circleMap_zero, ← hs,
      conj_circleMap_zero]
    ring
  have hperiod : (∫ θ in -(2 * Real.pi)..0, F θ) = ∫ θ in 0..2 * Real.pi, F θ := by
    simpa using hF.intervalIntegral_add_eq (-(2 * Real.pi)) 0
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
  change conj (∫ θ in 0..2 * Real.pi, F θ) = -(∫ θ in 0..2 * Real.pi, F θ)
  rw [← intervalIntegral.intervalIntegral_conj]
  simp_rw [hc]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg, neg_zero, hperiod]

/-- A Schwarz-symmetric integrand has real normalized circle integral.
This is the orientation-pairing identity used for real contour densities.
Source: Stahl (2013), Theorem 2 (supporting analysis).
Atlas: `trace-exponential-stahl` (helper). -/
theorem normalized_im_eq_zero_of_conj_eq {f : ℂ → ℂ} {r : ℝ}
    (hf : ∀ z ∈ sphere (0 : ℂ) |r|, f (conj z) = conj (f z)) :
    ((2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), f z)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [map_mul, conj_eq_neg_of_conj_eq hf]
  have hcoef : conj ((2 * Real.pi * I : ℂ)⁻¹) = -(2 * Real.pi * I : ℂ)⁻¹ := by
    simp only [map_inv₀, map_mul, map_ofNat, conj_ofReal, conj_I, mul_neg, inv_neg]
  rw [hcoef]
  ring

end circleIntegral
