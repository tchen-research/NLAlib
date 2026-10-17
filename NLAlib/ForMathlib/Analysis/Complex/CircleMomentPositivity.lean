import NLAlib.ForMathlib.Analysis.Complex.EllipseHomotopy

/-!
# Positive exponential circle moments of half-plane functions

A holomorphic upper-half-plane function with nonnegative imaginary part has a
nonnegative negatively normalized exponential moment on an exterior circle,
provided it extends holomorphically across the exterior real rays and has one
uniform bound on a surrounding compact ball. The proof uses actual smooth
ellipse deformations and their quantitative vanishing errors.
-/

noncomputable section

open Set Filter
open scoped Topology ComplexConjugate

namespace Complex

/-- A Schwarz-symmetric holomorphic function off a compact real segment, with
nonnegative upper-half-plane imaginary part and a uniform bound, has a
nonnegative exponential circle moment. All contour deformations and the thin
limit are proved; neither a positive measure nor real-axis limits are assumed. -/
theorem neg_normalized_exp_circleIntegral_re_nonneg
    {h : ℂ → ℂ} {R M C : ℝ} (hM : 0 < M) (hRM : R < M)
    (hh : DifferentiableOn ℂ h {z | z.im ≠ 0 ∨ R < ‖z‖})
    (href : ∀ z : ℂ, h (conj z) = conj (h z))
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ M + 1 → ‖h z‖ ≤ C) :
    0 ≤ (-((2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(0, M), exp z * h z))).re := by
  apply nonneg_of_neg_normalized_exp_ellipseIntegral_re_eq
    (h := h) (M := M) (C := C) (δ := 1) hM.le zero_lt_one
  · intro ε hε
    apply hh.continuousOn.comp (by unfold ellipseMap; fun_prop)
    intro θ _
    exact ellipseMap_mem_off_real_or_exterior hM hε.1 hRM
  · intro ε _ θ _
    exact href _
  · exact him
  · intro ε hε θ _
    apply hbound
    exact (norm_ellipseMap_le hM.le hε.1.le _).trans (by linarith [hε.2])
  · intro ε hε
    rw [← circleIntegral_eq_ellipseIntegral_of_differentiableOn_off_real_or_exterior
      (f := fun z => exp z * h z) hM hε.1 hRM (differentiable_exp.differentiableOn.mul hh)]

end Complex
