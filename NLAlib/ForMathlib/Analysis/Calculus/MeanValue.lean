import Mathlib.Analysis.Calculus.MeanValue

/-!
# Linear growth from a bounded derivative

`abs_le_abs_add_mul_abs_of_abs_deriv_le`: a differentiable `f : ℝ → ℝ` with `|f'| ≤ C` satisfies
`|f z| ≤ |f 0| + C |z|`. A general consequence of the mean value inequality, not about NLAlib's
objects; candidate for upstreaming to `Mathlib/Analysis/Calculus/MeanValue.lean`. Used throughout
`NLAlib.Gaussian.Concentration` (atlas `gaussian-integration-by-parts`).
-/

namespace NLAlib

/-- A function with derivative bounded by `C` grows at most linearly:
`|f z| ≤ |f 0| + C |z|`. Atlas: `gaussian-integration-by-parts` (helper). Ported from Prove2me
solution `GaussianMatrix.gaussian_ibp_one_dim`. -/
theorem abs_le_abs_add_mul_abs_of_abs_deriv_le (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (z : ℝ) : |f z| ≤ |f 0| + C * |z| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.univ) (C := C)
    (fun x _ => hf x) (fun x _ => by simpa using hdf x) convex_univ (Set.mem_univ 0)
    (Set.mem_univ z)
  simp only [Real.norm_eq_abs, sub_zero] at this
  have h2 := abs_sub_abs_le_abs_sub (f z) (f 0)
  linarith

end NLAlib
