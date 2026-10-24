import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Algebra.BigOperators.Module

/-! # Centering finite rectangular matrix Gram sums

The finite covariance identity is pure matrix algebra. It uses real weights,
so their conjugates agree with the weights themselves.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 ι r c : Type*} [RCLike 𝕜] [Fintype ι] [Fintype r] [Fintype c]

omit [Fintype r] in
/-- A real weighted Gram sum centered at its actual mean equals the raw Gram
sum minus the mean Gram. Positivity of the weights is unnecessary for this identity. -/
theorem sum_smul_sub_mul_conjTranspose (p : ι → ℝ) (hp : ∑ i, p i = 1)
    (M : ι → Matrix r c 𝕜) (B : Matrix r c 𝕜) (hmean : ∑ i, p i • M i = B) :
    (∑ i, p i • ((M i - B) * (M i - B)ᴴ)) =
      (∑ i, p i • (M i * (M i)ᴴ)) - B * Bᴴ := by
  classical
  have hAdj : (∑ i, p i • (M i)ᴴ) = Bᴴ := by
    have h := congrArg Matrix.conjTranspose hmean
    simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial] using h
  have hright : (∑ i, p i • (M i * Bᴴ)) = B * Bᴴ := by
    simp only [← Matrix.smul_mul]
    rw [← Matrix.sum_mul, hmean]
  have hleft : (∑ i, p i • (B * (M i)ᴴ)) = B * Bᴴ := by
    simp only [← Matrix.mul_smul]
    rw [← Matrix.mul_sum, hAdj]
  have hconst : (∑ i, p i • (B * Bᴴ)) = B * Bᴴ := by
    rw [← Finset.sum_smul, hp, one_smul]
  have hexp (i : ι) : (M i - B) * (M i - B)ᴴ =
      M i * (M i)ᴴ - M i * Bᴴ - B * (M i)ᴴ + B * Bᴴ := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  simp_rw [hexp, smul_add, smul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hright, hleft, hconst]
  abel

end NLAlib
