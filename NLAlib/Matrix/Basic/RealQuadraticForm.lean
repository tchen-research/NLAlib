import NLAlib.Matrix.Basic.QuadForm
import NLAlib.Matrix.Norms.Core

/-!
# Real matrices tested on complex vectors

The real part of a complex quadratic probe is the sum of its real and imaginary
vector probes. Their squared Euclidean norms add to the complex squared norm.
These identities let real random-matrix variance bounds retain their dimension.
-/

noncomputable section

open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- Complexifying a real matrix splits the real part of each quadratic form
into the real- and imaginary-vector quadratic forms. Symmetry is unnecessary. -/
theorem re_quadForm_map_ofReal (A : Matrix n n ℝ) (u : n → ℂ) :
    (quadForm (A.map Complex.ofReal) u).re =
      quadForm A (fun i => (u i).re) + quadForm A (fun i => (u i).im) := by
  simp only [quadForm_eq_sum, Complex.re_sum, Matrix.map_apply,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, star_trivial,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The squared real- and imaginary-part Euclidean norms add to the squared
complex Euclidean norm. -/
theorem norm_toLp_re_sq_add_norm_toLp_im_sq (u : n → ℂ) :
    ‖WithLp.toLp 2 (fun i => (u i).re)‖ ^ 2 +
      ‖WithLp.toLp 2 (fun i => (u i).im)‖ ^ 2 = ‖WithLp.toLp 2 u‖ ^ 2 := by
  simp only [norm_toLp_sq_eq_dotProduct_self, norm_toLp_sq_eq_re_star_dotProduct,
    RCLike.re_eq_complex_re, dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end NLAlib
