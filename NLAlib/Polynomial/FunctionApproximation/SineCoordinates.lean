import NLAlib.ForMathlib.Analysis.Complex.SineCoordinates
import NLAlib.Polynomial.FunctionApproximation.BernsteinWalsh

/-!
# Sine coordinates and finite polynomial growth

The sine of a complex number lies in the filled Bernstein ellipse with
parameter `exp |Im u|`. Small sine coordinates therefore translate real
interval bounds into finite complex polynomial bounds.
Source: the focused polynomial Bernstein reroute, Section 2.
-/

noncomputable section

open Complex Set Polynomial

namespace NLAlib

/-- A complex sine value belongs to the filled Bernstein ellipse whose parameter
is the exponential of the absolute imaginary coordinate. This includes real
coordinates and ellipse parameter one. -/
theorem sin_mem_filledBernsteinEllipse (u : ℂ) :
    Complex.sin u ∈ filledBernsteinEllipse (Real.exp |u.im|) := by
  let w := Complex.I * Complex.exp (-u * Complex.I)
  have hw : ‖w‖ = Real.exp u.im := by
    simp only [w, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp,
      Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.neg_im, mul_zero, mul_one, zero_sub, neg_neg]
  have hwJ : joukowski w = Complex.sin u := by
    have hinv : w⁻¹ = -Complex.I * Complex.exp (u * Complex.I) := by
      dsimp [w]
      rw [mul_inv_rev, Complex.inv_I, ← Complex.exp_neg]
      simp only [neg_mul, neg_neg]
      ring
    rw [joukowski, hinv]
    dsimp [w, Complex.sin]
    ring
  by_cases hu : 0 ≤ u.im
  · refine ⟨w, ⟨?_, ?_⟩, hwJ⟩
    · rw [hw]
      exact Real.one_le_exp_iff.mpr hu
    · rw [hw, abs_of_nonneg hu]
  · refine ⟨w⁻¹, ⟨?_, ?_⟩, ?_⟩
    · rw [norm_inv, hw, ← Real.exp_neg]
      exact Real.one_le_exp_iff.mpr (by linarith)
    · rw [norm_inv, hw, ← Real.exp_neg, abs_of_neg (lt_of_not_ge hu)]
    · rw [joukowski_inv, hwJ]

/-- A degree-bounded polynomial evaluated at a complex sine coordinate grows by
at most `exp (n |Im u|)` from its bound on the real unit interval. -/
theorem norm_eval_sin_le_mul_exp_abs_im {p : ℂ[X]} {n : ℕ} {M : ℝ}
    (hp : p.degree ≤ n)
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ M) (u : ℂ) :
    ‖p.eval (Complex.sin u)‖ ≤ M * Real.exp ((n : ℝ) * |u.im|) := by
  have h := norm_eval_le_mul_pow_of_mem_filledBernsteinEllipse hp hM
    (sin_mem_filledBernsteinEllipse u)
  simpa only [Real.exp_nat_mul] using h

/-- A polynomial bounded on the real unit interval has a quantitative complex
growth bound on the disk of radius one half. -/
theorem norm_eval_le_mul_exp_of_norm_le_half {p : ℂ[X]} {n : ℕ} {M : ℝ}
    (hp : p.degree ≤ n)
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, ‖p.eval (x : ℂ)‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖p.eval z‖ ≤ M * Real.exp ((n : ℝ) * |z.im| / Real.sqrt (1 - ‖z‖^2)) := by
  obtain ⟨u, hu, _, hum⟩ := Complex.exists_sin_eq_of_norm_le_half hz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨by norm_num, by norm_num⟩)
  have h := norm_eval_sin_le_mul_exp_abs_im hp hM u
  rw [hu] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ hM0
  apply Real.exp_le_exp.mpr
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hum (Nat.cast_nonneg n)

end NLAlib
