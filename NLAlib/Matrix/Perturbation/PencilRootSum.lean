import NLAlib.ForMathlib.Analysis.Matrix.RootCluster
import NLAlib.Matrix.Perturbation.HermitianPencilRoots

/-!
# The upper-root sum of an inverse Hermitian pencil

The function is defined using the actual characteristic roots with algebraic
multiplicities. For a Hermitian pencil with invertible slope matrix it is
holomorphic off the real parameter axis, has nonnegative imaginary part, and
obeys a uniform bound on bounded parameter sets. This closes the first bridge
in the planar root-sum approach to `trace-exponential-stahl`.
-/

noncomputable section

open Complex Set
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Sum of all upper-half-plane roots of `det (u I - A + z D)`, counted with
their algebraic multiplicities through the inverse characteristic polynomial.
The root interpretation requires `D` invertible; the expression is total. -/
def inversePencilUpperRootSum (A D : Matrix n n ℂ) (u : ℂ) : ℂ := by
  classical
  exact (((D⁻¹ * (A - u • (1 : Matrix n n ℂ))).charpoly.roots).filter
    (fun z => 0 < z.im)).sum

/-- Selecting upper roots gives a nonnegative imaginary part, including at
collisions and without a choice of individual roots. -/
theorem inversePencilUpperRootSum_im_nonneg (A D : Matrix n n ℂ) (u : ℂ) :
    0 ≤ (inversePencilUpperRootSum A D u).im := by
  exact Polynomial.im_sum_filter_roots_upper_nonneg _

/-- The actual upper-root sum of a Hermitian pencil is analytic throughout
both nonreal half-planes. The proof localizes the upper cluster by a fixed
circle and permits arbitrary collisions within the selected cluster.
Source: planar root-sum reorganization of Stahl's contour argument.
atlas: trace-exponential-stahl (partial) -/
theorem analyticAt_inversePencilUpperRootSum
    {A D : Matrix n n ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian)
    (hDu : IsUnit D) {u : ℂ} (hu : u.im ≠ 0) :
    AnalyticAt ℂ (inversePencilUpperRootSum A D) u := by
  have heq (v : ℂ) : D⁻¹ * (A - v • (1 : Matrix n n ℂ)) =
      D⁻¹ * A + v • (-D⁻¹) := by
    rw [mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_neg, sub_eq_add_neg]
  have h := Matrix.analyticAt_sum_filter_roots_charpoly_affine_upper
    (D⁻¹ * A) (-D⁻¹) u (by
      intro z hz
      rw [← heq] at hz
      exact im_ne_zero_of_det_hermitian_pencil_eq_zero hA hD hu
        ((det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul A D hDu u z).mpr hz))
  change AnalyticAt ℂ (fun v => ((D⁻¹ * (A - v • (1 : Matrix n n ℂ))).charpoly.roots.filter
    (fun z => 0 < z.im)).sum) u
  simpa only [heq] using h

/-- The inverse-pencil upper-root sum is bounded uniformly on bounded
parameter sets, with the dimension recording all algebraic multiplicities. -/
theorem norm_inversePencilUpperRootSum_le (A D : Matrix n n ℂ)
    (hD : IsUnit D) (u : ℂ) :
    ‖inversePencilUpperRootSum A D u‖ ≤
      (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) := by
  classical
  exact norm_sum_le_card_mul_specNorm_inv_of_le_roots_charpoly A D hD u _
    (Multiset.filter_le _ _)

/-- On each closed parameter ball the upper-root sum has one bound,
independently of proximity to the real axis. -/
theorem norm_inversePencilUpperRootSum_le_of_norm_le (A D : Matrix n n ℂ)
    (hD : IsUnit D) {u : ℂ} {M : ℝ} (hu : ‖u‖ ≤ M) :
    ‖inversePencilUpperRootSum A D u‖ ≤
      (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + M) := by
  exact (norm_inversePencilUpperRootSum_le A D hD u).trans
    (mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (Nat.cast_nonneg _) (specNorm_nonneg _)))

end NLAlib
