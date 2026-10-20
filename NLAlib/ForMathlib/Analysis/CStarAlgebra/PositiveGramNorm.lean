import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Rooted positive-functional Gram moments are bounded by the norm -/

noncomputable section
set_option autoImplicit false
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A normalized positive functional bounds every actual rooted Gram moment
by the native C-star norm. Traciality is unnecessary. -/
theorem PositiveLinearMap.gramMoment_rpow_le_norm (φ : A →ₚ[ℂ] ℂ)
    (hφ : φ 1 = 1) (T : A) {p : ℕ} (hp : 0 < p) :
    ((φ ((star T * T)^p)).re) ^ (1 / ((2*p : ℕ) : ℝ)) ≤ ‖T‖ := by
  have hG : 0 ≤ (star T*T)^p := CStarAlgebra.pow_nonneg (star_mul_self_nonneg T) p
  have hr : 0 ≤ (φ ((star T*T)^p)).re := (Complex.nonneg_iff.mp (φ.map_nonneg hG)).1
  have hn := φ.norm_apply_le_of_nonneg ((star T*T)^p) hG
  rw [hφ, norm_one, one_mul] at hn
  have hb : (φ ((star T*T)^p)).re ≤ ‖T‖ ^ (2*p) := by
    calc
      _ ≤ ‖φ ((star T*T)^p)‖ := Complex.re_le_norm _
      _ ≤ ‖(star T*T)^p‖ := hn
      _ ≤ ‖star T*T‖ ^ p := norm_pow_le' _ hp
      _ = _ := by rw [CStarRing.norm_star_mul_self]; ring
  have hh := Real.rpow_le_rpow hr hb (by positivity : (0:ℝ) ≤ 1/((2*p:ℕ):ℝ))
  calc
    _ ≤ (‖T‖ ^ (2*p)) ^ (1 / ((2*p : ℕ) : ℝ)) := hh
    _ = ‖T‖ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg T)]
      have hpn : ((2*p : ℕ):ℝ) ≠ 0 := by positivity
      rw [mul_one_div_cancel hpn, Real.rpow_one]
