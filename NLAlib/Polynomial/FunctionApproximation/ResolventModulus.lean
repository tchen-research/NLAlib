import NLAlib.ForMathlib.Analysis.Complex.ResolventModulus
import NLAlib.Polynomial.BestApproximation.Jackson
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Actual Jackson polynomials for the scalar resolvent modulus

The proved global inverse-height-squared Lipschitz bound and the sharp real
interval Jackson theorem construct an actual polynomial approximant. The
zero-radius interval is handled by the exact constant polynomial. No
approximation certificate is supplied as a premise.

This is the approximation input to Theorem 4.2 of arXiv:2406.11453v2.
-/

noncomputable section
set_option autoImplicit false

namespace NLAlib

/-- On every centered compact interval, the scalar nonreal resolvent
modulus has an actual degree-`r` polynomial approximant with the sharp
Jackson interval constant, including a zero-radius interval. -/
theorem exists_degree_le_resolvent_modulus_jackson {z : ℂ} (hz : 0 < z.im)
    (M : ℝ) (hM : 0 ≤ M) (r : ℕ) :
    ∃ Q : Polynomial ℝ, Q.degree ≤ r ∧ ∀ x ∈ Set.Icc (-M) M,
      |‖(z - (x : ℂ))⁻¹‖ - Q.eval x| ≤
        Real.pi * M / (2 * (r + 1 : ℝ) * z.im ^ 2) := by
  by_cases hzero : M = 0
  · subst M
    refine ⟨Polynomial.C ‖z⁻¹‖, ?_, ?_⟩
    · exact Polynomial.degree_C_le.trans (by exact_mod_cast Nat.zero_le r)
    · intro x hx
      have hxzero : x = 0 := by linarith [hx.1, hx.2]
      subst x
      simp
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
  have hLip : LipschitzOnWith ⟨z.im⁻¹ ^ 2, by positivity⟩
      (fun x : ℝ => ‖(z - (x : ℂ))⁻¹‖) (Set.Icc (-M) M) :=
    (Complex.lipschitzWith_norm_inv_sub_of_im_pos hz).lipschitzOnWith
  obtain ⟨Q, hQ, hApprox⟩ := exists_degree_le_abs_sub_eval_le_jackson_interval
    (by linarith : -M < M) hLip r
  refine ⟨Q, hQ, ?_⟩
  intro x hx
  have h := hApprox x hx
  change |‖(z - (x : ℂ))⁻¹‖ - Q.eval x| ≤
    Real.pi * (z.im⁻¹ ^ 2) * (M - -M) / (4 * (r + 1 : ℝ)) at h
  have hc : Real.pi * (z.im⁻¹ ^ 2) * (M - -M) / (4 * (r + 1 : ℝ)) =
      Real.pi * M / (2 * (r + 1 : ℝ) * z.im ^ 2) := by
    have hr : (r + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hz.ne', hr]
    ring
  rwa [hc] at h

/-- The actual degree-`r` Jackson approximant has the source's simpler
`6M/(rη²)` bound when `r` is positive. -/
theorem exists_degree_le_resolvent_modulus_approximation {z : ℂ} (hz : 0 < z.im)
    (M : ℝ) (hM : 0 ≤ M) (r : ℕ) (hr : 0 < r) :
    ∃ Q : Polynomial ℝ, Q.degree ≤ r ∧ ∀ x ∈ Set.Icc (-M) M,
      |‖(z - (x : ℂ))⁻¹‖ - Q.eval x| ≤ 6 * M / ((r : ℝ) * z.im ^ 2) := by
  obtain ⟨Q, hQ, hApprox⟩ := exists_degree_le_resolvent_modulus_jackson hz M hM r
  refine ⟨Q, hQ, fun x hx => (hApprox x hx).trans ?_⟩
  have hrR : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (r + 1 : ℝ) * z.im ^ 2)
    (mul_pos hrR (sq_pos_of_pos hz))).mpr
  have hpi : Real.pi * (r : ℝ) ≤ 12 * (r + 1 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hrR.le
    linarith
  convert mul_le_mul_of_nonneg_right hpi (mul_nonneg hM (sq_nonneg z.im)) using 1 <;> ring

end NLAlib

end
