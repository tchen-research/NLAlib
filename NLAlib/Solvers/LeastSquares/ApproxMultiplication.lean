/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.LeastSquares.SketchAndSolve
import NLAlib.Sketching.Properties.ObliviousSubspaceInjection.Basic

/-!
# Least squares from approximate multiplication and a lower embedding

A lower embedding controls the normal matrix, and an approximate-multiplication bound on
the cross term controls the fitted-value error. These are two separate deterministic
hypotheses. The result applies to every sketched minimizer and to rank-deficient designs.

Source: Sarlós 2006, Theorem 12; Woodruff 2014, proof of Theorem 2.16.
Atlas: `sketch-and-solve-ls` (AMM clause).
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- **AMM sketch-and-solve comparison.** If the sketch has lower squared-norm constant `α`
on a frame spanning `range A`, and the cross product with the optimal residual is at most
`γ` times its norm, then every sketched least-squares minimizer has squared residual at most
`1 + γ² / α²` times optimal. The lower-embedding assumption is essential; AMM alone does not
assert invertibility of the sketched normal matrix.
Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16.
atlas: sketch-and-solve-ls (partial) -/
theorem IsSubspaceInjection.norm_sub_mulVec_sq_le_of_cross_residual_le
    {k m n r : Type*} [Fintype k] [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    {S : Matrix k m ℝ} {A : Matrix m n ℝ} {U : Matrix m r ℝ}
    {b : m → ℝ} {x : n → ℝ} {α γ : ℝ}
    (hS : IsSubspaceInjection S U α) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hU : HasOrthonormalCols U)
    (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ b) x)
    (hcross : ‖WithLp.toLp 2 (Uᵀ *ᵥ (Sᵀ *ᵥ (S *ᵥ
        (b - A *ᵥ (moorePenroseInverse A *ᵥ b)))))‖ ≤
      γ * ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2 ≤ (1 + γ ^ 2 / α ^ 2) *
      ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖ ^ 2 := by
  let xstar := moorePenroseInverse A *ᵥ b
  let z := b - A *ᵥ xstar
  let c := Uᵀ *ᵥ (Sᵀ *ᵥ (S *ᵥ z))
  obtain ⟨w, hw⟩ := hA (show A *ᵥ (x - xstar) ∈ LinearMap.range A.mulVecLin from
    ⟨x - xstar, rfl⟩)
  change U *ᵥ w = A *ᵥ (x - xstar) at hw
  have hUw : ‖WithLp.toLp 2 (U *ᵥ w)‖ ^ 2 = ‖WithLp.toLp 2 w‖ ^ 2 := by
    rw [norm_toLp_sq_eq_dotProduct_self, norm_toLp_sq_eq_dotProduct_self,
      ← Matrix.dotProduct_transpose_mulVec U w, Matrix.mulVec_mulVec,
      show Uᵀ * U = 1 from hU, Matrix.one_mulVec]
  have hnormal := (isLeastSquaresSolution_iff_forall_dotProduct_mulVec_eq_zero
    (S * A) (S *ᵥ b) x).1 hx (x - xstar)
  have hres : S *ᵥ b - (S * A) *ᵥ x = S *ᵥ z - S *ᵥ (U *ᵥ w) := by
    rw [hw]
    simp only [z, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  rw [hres, ← Matrix.mulVec_mulVec, ← hw, sub_dotProduct] at hnormal
  have henergy : ‖WithLp.toLp 2 (S *ᵥ (U *ᵥ w))‖ ^ 2 = w ⬝ᵥ c := by
    rw [norm_toLp_sq_eq_dotProduct_self]
    have hcEq : w ⬝ᵥ c = S *ᵥ z ⬝ᵥ S *ᵥ (U *ᵥ w) := by
      calc
        w ⬝ᵥ c = (Sᵀ *ᵥ (S *ᵥ z)) ⬝ᵥ (U *ᵥ w) :=
          Matrix.dotProduct_transpose_mulVec U w _
        _ = (U *ᵥ w) ⬝ᵥ (Sᵀ *ᵥ (S *ᵥ z)) := dotProduct_comm _ _
        _ = _ := Matrix.dotProduct_transpose_mulVec S (U *ᵥ w) (S *ᵥ z)
    exact (sub_eq_zero.mp hnormal).symm.trans hcEq.symm
  have hCS : w ⬝ᵥ c ≤ ‖WithLp.toLp 2 w‖ * ‖WithLp.toLp 2 c‖ := by
    simpa only [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] using
      real_inner_le_norm (WithLp.toLp 2 w) (WithLp.toLp 2 c)
  have hlow := hS w
  rw [hUw, henergy] at hlow
  have hcross' : ‖WithLp.toLp 2 c‖ ≤ γ * ‖WithLp.toLp 2 z‖ := hcross
  have hbound : ‖WithLp.toLp 2 w‖ ≤ (γ / α) * ‖WithLp.toLp 2 z‖ := by
    by_cases hw0 : ‖WithLp.toLp 2 w‖ = 0
    · rw [hw0]
      positivity
    have hwpos : 0 < ‖WithLp.toLp 2 w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
    have h := hCS.trans (mul_le_mul_of_nonneg_left hcross' (norm_nonneg _))
    have h' : α * ‖WithLp.toLp 2 w‖ ≤ γ * ‖WithLp.toLp 2 z‖ := by
      nlinarith
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀' hα).2 h'
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  rw [mul_pow, div_pow] at hsquare
  have hopt := isLeastSquaresSolution_moorePenroseInverse_mulVec A b
  have horth : Aᵀ *ᵥ z = 0 := by
    have h := (isLeastSquaresSolution_iff_transpose_mulVec_mulVec_eq A b xstar).1 hopt
    simp only [z, Matrix.mulVec_sub, h, sub_self]
  have hpyth := norm_sub_mulVec_sq_eq_add_of_transpose_mulVec_eq_zero horth x
  have hneg : A *ᵥ (xstar - x) = -(U *ᵥ w) := by
    rw [hw, ← Matrix.mulVec_neg, neg_sub]
  rw [hneg, WithLp.toLp_neg, norm_neg, hUw] at hpyth
  rw [hpyth]
  change ‖WithLp.toLp 2 z‖ ^ 2 + ‖WithLp.toLp 2 w‖ ^ 2 ≤ _
  nlinarith

/-- A cross-residual AMM bound with `γ² ≤ ε α²` gives the usual unsquared regression factor
`1 + ε`. The lower embedding and AMM hypotheses are explicit and deterministic, and the
conclusion applies to every sketched minimizer.
Source: Sarlós 2006, Theorem 12; Woodruff 2014, Theorem 2.16.
atlas: sketch-and-solve-ls (partial) -/
theorem IsSubspaceInjection.norm_sub_mulVec_le_one_add_of_cross_residual_le
    {k m n r : Type*} [Fintype k] [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
    {S : Matrix k m ℝ} {A : Matrix m n ℝ} {U : Matrix m r ℝ}
    {b : m → ℝ} {x : n → ℝ} {α γ ε : ℝ}
    (hS : IsSubspaceInjection S U α) (hα : 0 < α) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hbudget : γ ^ 2 ≤ ε * α ^ 2) (hU : HasOrthonormalCols U)
    (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ b) x)
    (hcross : ‖WithLp.toLp 2 (Uᵀ *ᵥ (Sᵀ *ᵥ (S *ᵥ
        (b - A *ᵥ (moorePenroseInverse A *ᵥ b)))))‖ ≤
      γ * ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖) :
    ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤ (1 + ε) *
      ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖ := by
  have hsq := hS.norm_sub_mulVec_sq_le_of_cross_residual_le hα hγ hU hA hx hcross
  have hratio : γ ^ 2 / α ^ 2 ≤ ε := (div_le_iff₀ (sq_pos_of_pos hα)).2 hbudget
  have hnorm : 0 ≤ ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖ := norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_right (add_le_add_left hratio 1) (sq_nonneg
    ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖)
  have hextra : 0 ≤ ε * (1 + ε) *
      ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖ ^ 2 := by positivity
  apply le_of_sq_le_sq _ (mul_nonneg (by linarith : 0 ≤ 1 + ε) hnorm)
  calc
    _ ≤ (1 + γ ^ 2 / α ^ 2) *
        ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖ ^ 2 := hsq
    _ ≤ (1 + ε) *
        ‖WithLp.toLp 2 (b - A *ᵥ (moorePenroseInverse A *ᵥ b))‖ ^ 2 := by
          simpa only [add_comm] using hmul
    _ ≤ _ := by nlinarith only [hextra]

end NLAlib
