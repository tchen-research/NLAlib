import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-! # Native matrix inverse bounds near scalar matrices

Multiplying the actual inverse equation controls an existing inverse by
its distance from a scalar matrix, including nonnormal and empty cases.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
namespace Matrix
variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The true operator norm of an existing matrix inverse is at most the
reciprocal gap from a scalar perturbation. Neither normality nor a
Neumann-series representation is required. Empty matrix dimensions are
included. Source: the standard inverse perturbation bound. -/
theorem norm_nonsing_inv_le_of_sub_smul_one_le
    (X : Matrix n n 𝕜) (w : 𝕜) (r : ℝ) (hX : IsUnit X)
    (herror : ‖X-w•1‖≤r) (hgap : r<‖w‖) :
    ‖X⁻¹‖≤(‖w‖-r)⁻¹ := by
  have h1 : ‖(1 : Matrix n n 𝕜)‖≤1 := by
    rw [← Matrix.diagonal_one,Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp
  have he : w•X⁻¹=1-(X-w•1)*X⁻¹ := by
    rw [Matrix.sub_mul,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hX),
      Matrix.smul_mul,Matrix.one_mul]
    abel
  have hn : ‖w‖*‖X⁻¹‖≤1+r*‖X⁻¹‖ := by
    calc
      _ = ‖w•X⁻¹‖ := (norm_smul _ _).symm
      _ = ‖1-(X-w•1)*X⁻¹‖ := by rw [he]
      _ ≤ ‖(1 : Matrix n n 𝕜)‖+‖(X-w•1)*X⁻¹‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add h1 ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right herror (norm_nonneg _)))
  have hd : ‖X⁻¹‖≤1/(‖w‖-r) := (le_div_iff₀ (sub_pos.mpr hgap)).mpr (by
    nlinarith only [hn])
  simpa only [one_div] using hd

end Matrix
